/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Arrays.PrefixCount
import Mathlib.Data.Finset.Sort

/-! # Stable array selection and shared dense indices

One Boolean mask determines the count and increasing index correspondence.
Every related array is packed through this same correspondence.
-/

namespace Polytime2.ArrayPacking

variable {length : ℕ}

/-- The selected coordinates depend only on the mask, not on array contents. -/
def selected (flags : Fin length → Bool) : Finset (Fin length) :=
  Finset.univ.filter (fun index => flags index = true)

/-- Exact output length; no inactive coordinates are mathematical output data. -/
def count (flags : Fin length → Bool) : ℕ := (selected flags).card

/-- Increasing enumeration of exactly the active coordinates. -/
noncomputable def selection (flags : Fin length → Bool) :
    Fin (count flags) ≃o {index : Fin length // flags index = true} :=
  ((selected flags).orderIsoOfFin rfl).trans
    { toFun := fun index => ⟨index.val, (Finset.mem_filter.mp index.property).2⟩
      invFun := fun index => ⟨index.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, index.property⟩⟩
      left_inv := by intro index; rfl
      right_inv := by intro index; rfl
      map_rel_iff' := by intros; rfl }

/-- Original coordinates map back to their dense packed positions. -/
noncomputable def rank (flags : Fin length → Bool)
    (index : {index : Fin length // flags index = true}) : Fin (count flags) :=
  (selection flags).symm index

/-- The dense index viewed inside the original private capacity. -/
noncomputable def capacityRank (flags : Fin length → Bool)
    (index : {index : Fin length // flags index = true}) : Fin length :=
  ⟨(rank flags index).val, (rank flags index).isLt.trans_le (by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin length))⟩

theorem capacityRank_injective (flags : Fin length → Bool) : Function.Injective (capacityRank flags) := by
  intro first second equal
  apply (selection flags).symm.injective
  apply Fin.ext
  have coordinates : (capacityRank flags first).val = (capacityRank flags second).val := congrArg Fin.val equal
  exact coordinates

@[simp] theorem rank_selection (flags : Fin length → Bool) (position : Fin (count flags)) :
    rank flags (selection flags position) = position :=
  (selection flags).symm_apply_apply position

/-- Stable packing works for any mathematical element type and all lengths. -/
noncomputable def pack {Element : Type*} (flags : Fin length → Bool)
    (values : Fin length → Element) : Fin (count flags) → Element :=
  fun position => values (selection flags position).val

theorem count_le (flags : Fin length → Bool) : count flags ≤ length := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin length)

theorem count_eq_count_true (flags : Fin length → Bool) :
    count flags = (List.ofFn flags).count true := by
  rw [Computation.count_flags_card]
  exact ((Nat.card_congr (selection flags).toEquiv.symm).trans (Nat.card_fin _)).symm

theorem selection_active (flags : Fin length → Bool) (position : Fin (count flags)) :
    flags (selection flags position).val = true :=
  (selection flags position).property

theorem selection_strictMono (flags : Fin length → Bool) :
    StrictMono (fun position => (selection flags position).val) :=
  fun _ _ ordered => (selection flags).strictMono ordered

theorem selection_rank (flags : Fin length → Bool)
    (index : {index : Fin length // flags index = true}) :
    (selection flags (rank flags index)).val = index.val :=
  congrArg Subtype.val ((selection flags).apply_symm_apply index)

/-- The existing certified prefix counter computes the shared dense index. -/
theorem prefix_count_rank (flags : Fin length → Bool)
    (index : {index : Fin length // flags index = true}) :
    ((List.ofFn flags).take index.val.val).count true = (rank flags index).val :=
  Computation.prefix_count_orderIndex flags index (selection flags).symm

theorem pack_rank {Element : Type*} (flags : Fin length → Bool)
    (values : Fin length → Element) (index : {index : Fin length // flags index = true}) :
    pack flags values (rank flags index) = values index.val := by
  exact congrArg values (selection_rank flags index)

/-- Applying a pointwise operation before or after shared packing agrees. -/
theorem pack_map {Element Result : Type*} (flags : Fin length → Bool)
    (values : Fin length → Element) (operation : Element → Result) :
    pack flags (operation ∘ values) = operation ∘ pack flags values := rfl

/-- Related arrays retain their coordinate pairing under one shared mask. -/
theorem pack_pair {Left Right : Type*} (flags : Fin length → Bool)
    (left : Fin length → Left) (right : Fin length → Right) :
    pack flags (fun index => (left index, right index)) =
      fun position => (pack flags left position, pack flags right position) := rfl

/-- Number of selected entries among the first processed source coordinates. -/
def prefixCount (flags : Fin length → Bool) (processed : ℕ) : ℕ :=
  ((List.ofFn flags).take processed).count true

theorem prefix_le (flags : Fin length → Bool) (processed : ℕ) : prefixCount flags processed ≤ processed :=
  (List.count_le_length (a := true) (l := (List.ofFn flags).take processed)).trans (by simp)

theorem prefix_succ (flags : Fin length → Bool) (index : Fin length) :
    prefixCount flags (index.val + 1) = prefixCount flags index.val + if flags index then 1 else 0 := by
  unfold prefixCount
  rw [List.take_succ_eq_append_getElem (by simp)]
  cases selected : flags index <;> simp [selected]

/-- Private storage uses raw encoded blocks, so no default mathematical element
is required for unused capacity. -/
noncomputable def rawPack {Element : Type*} {width : ℕ}
    (encode : Element → BitVec width) (flags : Fin length → Bool)
    (values : Fin length → Element) : Fin length → BitVec width :=
  fun position => if within : position.val < count flags then
    encode (pack flags values ⟨position.val, within⟩) else 0

/-- Complete private storage consists of the packed blocks and zero blocks. -/
theorem rawPack_ofFn {Element : Type*} {width : ℕ} (encode : Element → BitVec width)
    (flags : Fin length → Bool) (values : Fin length → Element) :
    List.ofFn (rawPack encode flags values) =
      List.ofFn (fun position => encode (pack flags values position)) ++
        List.replicate (length - count flags) 0 := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    have fits := count_le flags
    omega
  · intro position leftWithin rightWithin
    by_cases inside : position < count flags <;>
      simp [rawPack, List.getElem_append, inside]

theorem count_all_true : count (fun _ : Fin length => true) = length := by
  simp [count, selected]

theorem count_all_false : count (fun _ : Fin length => false) = 0 := by
  simp [count, selected]

end Polytime2.ArrayPacking

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- The existing polynomial-time position table computes the shared packing
correspondence, including for runtime-dependent array lengths. -/
theorem prefixCounts_packing_rank (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (index : {index : Fin (MvPolynomial.eval sizes length) // flags index = true}) :
    (((prefixCounts length).compute sizes ⟨(fun _ => flags), trivial⟩) index.val).toNat =
      (ArrayPacking.rank flags index).val :=
  (prefixCounts_correct length sizes flags index.val).trans (ArrayPacking.prefix_count_rank flags index)

end Polytime2.Computation
