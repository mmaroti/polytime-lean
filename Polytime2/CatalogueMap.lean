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

import Polytime2.IndexedMapContract

/-! # Two active catalogue maps on binary-encoded arrays

Both maps are specialization-fixed. The active count, selected coordinates,
and source array are immutable arguments. A private intermediate array links
the calls; the final result is separate. Scalar and counter scratch is shared.
-/

namespace Polytime2.CatalogueMap

open MultiTape CallingConvention

-- parameterLevel: names of the caller's unary size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

abbrev Alphabet := CallingConvention.Alphabet (Sum Parameter (Fin 15))

/-- The ignored scalar parameter of a unary map occupies an empty region. -/
noncomputable def unitDomain : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 1))

abbrev State (elementWidth : ℕ) :=
  Sum (IndexedMap.State (unitDomain.width Empty.elim) elementWidth)
    (IndexedMap.State (unitDomain.width Empty.elim) elementWidth)

noncomputable instance stateFintype (elementWidth : ℕ) : Fintype (State elementWidth) := by
  letI : Fintype (IndexedMap.State (unitDomain.width Empty.elim) elementWidth) := inferInstance
  exact inferInstanceAs (Fintype (Sum _ _))

noncomputable def domains (elementDomain : EncodedDomain Empty) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Sum Parameter (Fin 15) → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 | .inr 1 | .inr 2 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 3 | .inr 4 | .inr 5 => elementDomain.constant.arrayOfLength length
  | .inr 6 => unitDomain.constant
  | .inr 7 | .inr 8 => elementDomain.constant
  | .inr 9 | .inr 10 | .inr 12 | .inr 13 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 11 | .inr 14 => EncodedDomain.booleans

def argumentReadOnly : Sum Parameter (Fin 15) → Bool
  | .inl _ => true
  | .inr name => decide (name.val < 4)

def sizeTapes : Parameter ↪ Sum Parameter (Fin 15) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def data (second : Bool) (name : Fin 12) : Fin 15 :=
  ⟨match name.val with
    | 0 => if second then 1 else 0
    | 1 => if second then 4 else 3
    | 2 => 6
    | 3 => if second then 5 else 4
    | 4 => 7
    | 5 => 8
    | 6 => 9
    | 7 => 10
    | 8 => 11
    | 9 => 12
    | 10 => 13
    | _ => 14, by cases second <;> fin_cases name <;> decide⟩

private theorem data_injective (second : Bool) : Function.Injective (data second) := by
  intro first other equal
  cases second <;> fin_cases first <;> fin_cases other <;> simp [data] at equal ⊢

def wiring (second : Bool) : Sum Parameter (Fin 12) ↪ Sum Parameter (Fin 15) :=
  (Function.Embedding.refl Parameter).sumMap ⟨data second, data_injective second⟩

noncomputable def algorithm (elementDomain : EncodedDomain Empty)
    (first second : ∀ assignment, elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    Machine (Alphabet (Parameter := Parameter)) (State (elementDomain.width Empty.elim)) :=
  MultiTape.sequence
    (MultiTape.wire (wiring false)
      (IndexedMap.algorithm unitDomain elementDomain (fun assignment _ => first assignment)))
    (MultiTape.wire (wiring true)
      (IndexedMap.algorithm unitDomain elementDomain (fun assignment _ => second assignment)))
    (IndexedMap.entry (unitDomain.width Empty.elim) (elementDomain.width Empty.elim))

noncomputable def entry (elementWidth : ℕ) : State elementWidth := .inl (IndexedMap.entry (unitDomain.width Empty.elim) elementWidth)
noncomputable def exit (elementWidth : ℕ) : State elementWidth := .inr (IndexedMap.exit (unitDomain.width Empty.elim) elementWidth)

omit [Fintype Parameter] in
@[simp] theorem halt (elementDomain : EncodedDomain Empty)
    (first second : ∀ assignment, elementDomain.Carrier assignment → elementDomain.Carrier assignment)
    (symbols : Symbols (Alphabet (Parameter := Parameter))) :
    algorithm elementDomain first second (exit (elementDomain.width Empty.elim)) symbols = none := by
  simp only [algorithm, exit, MultiTape.sequence, MultiTape.wire]
  rw [IndexedMap.halt unitDomain elementDomain (fun assignment _ => second assignment)]
  rfl

omit [Fintype Parameter] in
/-- The two calls reuse every scalar and counter scratch tape, with one
stationary handover and a distinct intermediate array. -/
theorem sequence_runs (elementDomain : EncodedDomain Empty)
    (first second : ∀ assignment, elementDomain.Carrier assignment → elementDomain.Carrier assignment)
    (width : Sum Parameter (Fin 15) → ℕ) (readOnly : Sum Parameter (Fin 15) → Bool)
    {firstTicks secondTicks : ℕ}
    {initialPosition middlePosition finalPosition : Sum Parameter (Fin 15) → ℤ}
    {initial middle final : Tapes (Alphabet (Parameter := Parameter))}
    (firstTrace : Runs width readOnly
      (MultiTape.wire (wiring false)
        (IndexedMap.algorithm unitDomain elementDomain (fun assignment _ => first assignment)))
      firstTicks (IndexedMap.entry (unitDomain.width Empty.elim) (elementDomain.width Empty.elim)) initialPosition initial
      (IndexedMap.exit (unitDomain.width Empty.elim) (elementDomain.width Empty.elim)) middlePosition middle)
    (secondTrace : Runs width readOnly
      (MultiTape.wire (wiring true)
        (IndexedMap.algorithm unitDomain elementDomain (fun assignment _ => second assignment)))
      secondTicks (IndexedMap.entry (unitDomain.width Empty.elim) (elementDomain.width Empty.elim)) middlePosition middle
      (IndexedMap.exit (unitDomain.width Empty.elim) (elementDomain.width Empty.elim)) finalPosition final) :
    Runs width readOnly (algorithm elementDomain first second) (firstTicks + secondTicks + 1)
      (entry (elementDomain.width Empty.elim)) initialPosition initial
      (exit (elementDomain.width Empty.elim)) finalPosition final :=
  firstTrace.sequence _ _ (by
    intro symbols
    simp only [MultiTape.wire]
    rw [IndexedMap.halt unitDomain elementDomain (fun assignment _ => first assignment)]
    rfl) secondTrace

-- Index: runtime array coordinates; Scalar: specialization-fixed entries.
variable {Index Scalar : Type} [DecidableEq Index]

/-- Equal selected coordinates apply the second map to the first map's result. -/
def compute (first second : Scalar → Scalar) (array : Index → Scalar)
    (firstIndex secondIndex : Index) : Index → Scalar :=
  let middle := Function.update array firstIndex (first (array firstIndex))
  Function.update middle secondIndex (second (middle secondIndex))

/-- Every entry outside the active prefix is preserved, regardless of its value. -/
theorem inactive_preserved (first second : Scalar → Scalar) {length : ℕ}
    (array : Fin length → Scalar) (firstIndex secondIndex index : Fin length)
    (active : ℕ) (firstActive : firstIndex.val < active) (secondActive : secondIndex.val < active)
    (inactive : active ≤ index.val) :
    compute first second array firstIndex secondIndex index = array index := by
  have firstDifferent : index ≠ firstIndex := by intro equal; subst index; omega
  have secondDifferent : index ≠ secondIndex := by intro equal; subst index; omega
  simp [compute, Function.update_of_ne, firstDifferent, secondDifferent]

end Polytime2.CatalogueMap
