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

import Polytime2.Arrays.PackingPass

/-! # Correctness of the stable packing traversal

Processed active coordinates occupy their shared dense indices. Every block
at or beyond the active prefix count is still zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open ArrayPacking

variable {Parameter : Type} [Fintype Parameter]

/-- The invariant talks only about mathematical cursors and encoded blocks. -/
def packingInvariant (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (values : Fin (MvPolynomial.eval sizes length) → element.Carrier sizes)
    (processed : ℕ) (current : (packingState element capacity length).Carrier sizes) : Prop :=
  current.1.val = processed ∧ current.2.1.val = prefixCount flags processed ∧
    (∀ index : {index : Fin (MvPolynomial.eval sizes length) // flags index = true},
      index.val.val < processed → current.2.2 (capacityRank flags index) = element.encode sizes (values index.val)) ∧
    (∀ position : Fin (MvPolynomial.eval sizes length), prefixCount flags processed ≤ position.val →
      current.2.2 position = 0)

theorem packingInvariant_zero (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (values : Fin (MvPolynomial.eval sizes length) → element.Carrier sizes) :
    packingInvariant element capacity length sizes flags values 0
      (packingZero element capacity length sizes) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rfl
  · intro index before; omega
  · intro position beyond; rfl

/-- Each source value is copied at its prefix-count position if selected;
previous copies and unused zero padding remain unchanged. -/
theorem packingInvariant_advance (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool)
    (values : Fin (MvPolynomial.eval sizes length) → element.Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes length))
    (current : (packingState element capacity length).Carrier sizes)
    (fits : MvPolynomial.eval sizes length < 2 ^ sizes capacity)
    (invariant : packingInvariant element capacity length sizes flags values index.val current) :
    packingInvariant element capacity length sizes flags values (index.val + 1)
      (packingAdvance element capacity length sizes flags current (values index)) := by
  obtain ⟨source, destination, copied, padding⟩ := invariant
  have prefixBound := prefix_le flags index.val
  have permitted : current.1.val < MvPolynomial.eval sizes length ∧ current.2.1.val ≤ current.1.val := by
    constructor <;> omega
  have currentIndex : (⟨current.1.val, permitted.1⟩ : Fin (MvPolynomial.eval sizes length)) = index := Fin.ext source
  have cursor := packingAdvance_cursors element capacity length sizes flags current (values index)
    index.val source (by omega) index.isLt fits
  refine ⟨cursor.1, ?_, ?_, ?_⟩
  · simp only [packingAdvance, ArrayFold.extend, dite_eq_left permitted]
    dsimp only [packingStep]
    rw [currentIndex, prefix_succ]
    by_cases selected : flags index = true
    · simp only [ite_eq_left selected, StandardBinaryIncrement.next]
      rw [destination, Nat.mod_eq_of_lt (by omega)]
    · simpa only [ite_eq_right selected, Nat.add_zero] using destination
  · intro active before
    simp only [packingAdvance, ArrayFold.extend, dite_eq_left permitted]
    dsimp only [packingStep]
    rw [currentIndex]
    by_cases earlier : active.val.val < index.val
    · by_cases selected : flags index = true
      · simp only [ite_eq_left selected]
        have different : capacityRank flags active ≠
            (⟨current.2.1.val, lt_of_le_of_lt permitted.2 permitted.1⟩ : Fin (MvPolynomial.eval sizes length)) := by
          intro equal
          have rankCurrent : capacityRank flags ⟨index, selected⟩ =
              (⟨current.2.1.val, lt_of_le_of_lt permitted.2 permitted.1⟩ : Fin (MvPolynomial.eval sizes length)) := by
            apply Fin.ext
            exact (prefix_count_rank flags ⟨index, selected⟩).symm.trans destination.symm
          have same := capacityRank_injective flags (equal.trans rankCurrent.symm)
          have coordinates := congrArg (fun value => value.val.val) same
          change active.val.val = index.val at coordinates
          omega
        rw [Function.update_of_ne different]
        exact copied active earlier
      · simpa only [ite_eq_right selected] using copied active earlier
    · have same : active.val = index := Fin.ext (by omega)
      have selected : flags index = true := same ▸ active.property
      simp only [selected, ite_true]
      have location : capacityRank flags active =
          (⟨current.2.1.val, lt_of_le_of_lt permitted.2 permitted.1⟩ : Fin (MvPolynomial.eval sizes length)) := by
        apply Fin.ext
        change (rank flags active).val = current.2.1.val
        rw [← prefix_count_rank flags active, same]
        exact destination.symm
      rw [location, Function.update_self, same]
  · intro position beyond
    simp only [packingAdvance, ArrayFold.extend, dite_eq_left permitted]
    dsimp only [packingStep]
    rw [currentIndex]
    have nextCount := prefix_succ flags index
    by_cases selected : flags index = true
    · simp only [ite_eq_left selected]
      have different : position ≠ (⟨current.2.1.val, lt_of_le_of_lt permitted.2 permitted.1⟩ : Fin (MvPolynomial.eval sizes length)) := by
        intro equal
        have locations := congrArg Fin.val equal
        change position.val = current.2.1.val at locations
        simp only [ite_eq_left selected] at nextCount
        omega
      rw [Function.update_of_ne different]
      apply padding position
      simp only [ite_eq_left selected] at nextCount
      omega
    · simp only [ite_eq_right selected]
      apply padding position
      simp only [ite_eq_right selected, Nat.add_zero] at nextCount
      omega

/-- The initialized certified traversal produces exactly the stable packed
prefix, its active count, and zero bits throughout unused capacity. -/
theorem packingInitialized_correct (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (packingInitialized element capacity length).Arguments sizes)
    (valid : (packingInitialized element capacity length).precondition sizes arguments) :
    let result := (packingInitialized element capacity length).compute sizes ⟨arguments, valid⟩
    result.1.val = MvPolynomial.eval sizes length ∧
    result.2.1.val = count (arguments false) ∧
    result.2.2 = rawPack (element.encode sizes) (arguments false) (arguments true) := by
  let flags := arguments false
  let values := arguments true
  have invariant := ArrayFold.prefix_invariant
    (packingAdvance element capacity length sizes flags) values
    (packingZero element capacity length sizes)
    (packingInvariant element capacity length sizes flags values)
    (packingInvariant_zero element capacity length sizes flags values)
    (fun index current good => packingInvariant_advance element capacity length sizes flags values index current valid good)
  let result := (packingInitialized element capacity length).compute sizes ⟨arguments, valid⟩
  change packingInvariant element capacity length sizes flags values
    (MvPolynomial.eval sizes length) result at invariant
  obtain ⟨source, destination, copied, padding⟩ := invariant
  have total : prefixCount flags (MvPolynomial.eval sizes length) = count flags := by
    unfold prefixCount
    rw [List.take_of_length_le (by simp)]
    exact (count_eq_count_true flags).symm
  refine ⟨source, destination.trans total, ?_⟩
  funext position
  by_cases within : position.val < count flags
  · let active := selection flags ⟨position.val, within⟩
    have location : capacityRank flags active = position := by
      apply Fin.ext
      have coordinates := congrArg (fun value : Fin (count flags) => value.val)
        (rank_selection flags ⟨position.val, within⟩)
      exact coordinates
    have known := copied active active.val.isLt
    rw [location] at known
    change result.2.2 position = rawPack (element.encode sizes) flags values position
    rw [rawPack, dite_eq_left within]
    exact known
  · change result.2.2 position = rawPack (element.encode sizes) flags values position
    rw [rawPack, dite_eq_right within]
    exact padding position (by rw [total]; omega)

end Polytime2.Computation
