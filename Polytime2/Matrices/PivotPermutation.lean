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

import Polytime2.Matrices.PivotPermutationMath
import Polytime2.Arrays.SwapValues
import Polytime2.Arrays.Indices
import Polytime2.Arrays.Operations
import Polytime2.Arrays.FoldContract
import Polytime2.Arrays.BoundedPositions

/-! # Runtime image-table updates for deterministic pivot permutations

The selected coordinates are an ordinary injective array. At each pivot
position, exchange the current image with the prescribed selected coordinate
throughout the table. The selected-array injection implies every lookup fits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Update a permutation image table at one selected pivot position. -/
noncomputable def pivotPermutationStep (dimension count : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) := by
  classical
  exact {
    inputDomains := fun name => match name with
      | 0 => (boundedIndex dimension).arrayOfLength count
      | 1 => (boundedIndex dimension).arrayOfLength dimension
      | 2 => arrayPosition count
    outputDomain := (boundedIndex dimension).arrayOfLength dimension
    precondition := fun _ arguments => Function.Injective (arguments 0)
    compute := fun sizes arguments =>
      let bound : MvPolynomial.eval sizes count ≤ MvPolynomial.eval sizes dimension := by
        simpa using Fintype.card_le_of_injective (α := Fin (MvPolynomial.eval sizes count))
          (β := Fin (MvPolynomial.eval sizes dimension)) (arguments.val 0) arguments.property
      let position : Fin (MvPolynomial.eval sizes dimension) :=
        ⟨(arguments.val 2).val, (arguments.val 2).isLt.trans_le bound⟩
      fun index => Equiv.swap ((arguments.val 1) position) ((arguments.val 0) (arguments.val 2)) ((arguments.val 1) index) }

/-- Two lookups and a pointwise scalar swap realize one permutation-prefix update. -/
theorem pivotPermutationStep_realizable (dimension count : MvPolynomial Parameter ℕ) :
    (pivotPermutationStep dimension count).Realizable := by
  classical
  let computation := pivotPermutationStep dimension count
  let coordinate := boundedIndex dimension
  let position := arrayPosition count
  let current sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      coordinate.Carrier sizes :=
    (arguments.val 1) ⟨(arguments.val 2).val, (arguments.val 2).isLt.trans_le (by
      simpa using Fintype.card_le_of_injective (α := Fin (MvPolynomial.eval sizes count))
          (β := Fin (MvPolynomial.eval sizes dimension)) (arguments.val 0) arguments.property)⟩
  have image := (arrayLookupWithIndex_realizable coordinate position (fun _ index => index.val)
    (arrayPosition_value count) dimension).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 2 | true => arguments.val 1) (by
      intro sizes arguments
      have bound : MvPolynomial.eval sizes count ≤ MvPolynomial.eval sizes dimension := by
        simpa using Fintype.card_le_of_injective (α := Fin (MvPolynomial.eval sizes count))
          (β := Fin (MvPolynomial.eval sizes dimension)) (arguments.val 0) arguments.property
      exact (arguments.val 2).isLt.trans_le bound) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  have desired := (arrayLookupWithIndex_realizable coordinate position (fun _ index => index.val)
    (arrayPosition_value count) count).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val 2 | true => arguments.val 0)
    (by intro sizes arguments; exact (arguments.val 2).isLt) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact Realizable.argument computation.inputDomains 0 computation.precondition)
  have updated := (arraySwapValues_realizable coordinate dimension).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
      | .inl false => current sizes arguments
      | .inl true => (arguments.val 0) (arguments.val 2)
      | .inr _ => arguments.val 1) (by intros; trivial) (by
        intro name
        rcases name with choice | singleton
        · cases choice
          · exact image
          · exact desired
        · exact Realizable.argument computation.inputDomains 1 computation.precondition)
  exact updated.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- A correct image table for the current prefix advances to the next mathematical prefix. -/
theorem pivotPermutationStep_correct (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (pivotPermutationStep dimension count).Arguments sizes //
      (pivotPermutationStep dimension count).precondition sizes arguments})
    (selected : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes dimension))
    (sameSelected : (arguments.val 0) = (fun index => selected index))
    (sameTable : (arguments.val 1) = (fun index => IntegerMatrix.pivotPermutationPrefix selected (arguments.val 2).val
      (Nat.le_of_lt (arguments.val 2).isLt) index)) :
    (pivotPermutationStep dimension count).compute sizes arguments =
      (fun index => IntegerMatrix.pivotPermutationPrefix selected ((arguments.val 2).val + 1) (arguments.val 2).isLt index) := by
  funext index
  dsimp only [pivotPermutationStep]
  rw [sameSelected, sameTable]
  simp only [IntegerMatrix.pivotPermutationPrefix, Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.eta]

private noncomputable def selectedDomain (dimension count : MvPolynomial Parameter ℕ) :=
  (boundedIndex dimension).arrayOfLength count

private noncomputable def tableDomain (dimension : MvPolynomial Parameter ℕ) :=
  (boundedIndex dimension).arrayOfLength dimension

private def stepArguments (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ _ : Unit, (selectedDomain dimension count).Carrier sizes)
    (table : (tableDomain dimension).Carrier sizes) (position : (arrayPosition count).Carrier sizes) :
    (pivotPermutationStep dimension count).Arguments sizes
  | 0 => selected () | 1 => table | 2 => position

private noncomputable def permutationUpdate (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ _ : Unit, (selectedDomain dimension count).Carrier sizes)
    (table : (tableDomain dimension).Carrier sizes) (position : (arrayPosition count).Carrier sizes) := by
  classical
  exact if valid : Function.Injective (selected ()) then
    (pivotPermutationStep dimension count).compute sizes ⟨stepArguments dimension count sizes selected table position, valid⟩ else table

private theorem permutationUpdate_realizable (dimension count : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (fun _ : Unit => selectedDomain dimension count) (arrayPosition count) (tableDomain dimension)
      (fun _ selected _ _ => Function.Injective (selected ())) (permutationUpdate dimension count)).Realizable := by
  classical
  let computation := arrayFoldStep (fun _ : Unit => selectedDomain dimension count) (arrayPosition count) (tableDomain dimension)
    (fun _ selected _ _ => Function.Injective (selected ())) (permutationUpdate dimension count)
  have executed := (pivotPermutationStep_realizable dimension count).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments => stepArguments dimension count sizes (fun _ => arguments.val (.inl ()))
      (arguments.val (.inr false)) (arguments.val (.inr true)) name)
    (by intro sizes arguments; exact arguments.property) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains (.inl ()) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inr false) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inr true) computation.precondition)
  apply executed.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  have good : Function.Injective (arguments (.inl ())) := valid
  simp only [computation, arrayFoldStep, permutationUpdate, dite_eq_left good, Computation.onResults]

private def permutationInvariant (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ _ : Unit, (selectedDomain dimension count).Carrier sizes)
    (processed : ℕ) (table : (tableDomain dimension).Carrier sizes) :=
  ∀ embedding : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes dimension),
    selected () = (fun index => embedding index) →
    ∃ within : processed ≤ MvPolynomial.eval sizes count,
      table = (fun index => IntegerMatrix.pivotPermutationPrefix embedding processed within index)

private theorem permutationPreserves (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ _ : Unit, (selectedDomain dimension count).Carrier sizes)
    (injective : Function.Injective (selected ())) (position : Fin (MvPolynomial.eval sizes count))
    (table : (tableDomain dimension).Carrier sizes)
    (before : permutationInvariant dimension count sizes selected position.val table) :
    permutationInvariant dimension count sizes selected (position.val + 1)
      (permutationUpdate dimension count sizes selected table position) := by
  classical
  intro embedding same
  obtain ⟨within, previous⟩ := before embedding same
  refine ⟨position.isLt, ?_⟩
  dsimp only [permutationUpdate]
  rw [dite_eq_left injective]
  exact pivotPermutationStep_correct dimension count sizes
    ⟨stepArguments dimension count sizes selected table position, injective⟩ embedding same previous

private noncomputable def permutationFold (dimension count : MvPolynomial Parameter ℕ) :=
  arrayFold (fun _ : Unit => selectedDomain dimension count) (arrayPosition count) (tableDomain dimension) count
    (fun _ selected array initial => Function.Injective (selected ()) ∧ array = id ∧ initial = id)
    (permutationUpdate dimension count)

private theorem permutationFold_realizable (dimension count : MvPolynomial Parameter ℕ) :
    (permutationFold dimension count).Realizable := by
  apply arrayFold_realizable (fun _ : Unit => selectedDomain dimension count) (arrayPosition count) (tableDomain dimension) count
    (fun _ selected array initial => Function.Injective (selected ()) ∧ array = id ∧ initial = id)
    (permutationUpdate dimension count) (fun _ selected _ _ => Function.Injective (selected ()))
    (permutationUpdate_realizable dimension count)
    (fun sizes selected _array _initial processed table => permutationInvariant dimension count sizes selected processed table)
  · intro sizes selected array initial valid embedding same
    exact ⟨Nat.zero_le _, valid.2.2⟩
  · intro sizes selected array initial valid index table before
    exact valid.1
  · intro sizes selected array initial valid index table before
    rw [valid.2.1]
    exact permutationPreserves dimension count sizes selected valid.1 index table before

/-- Construct the full deterministic permutation image table from injective selected coordinates. -/
noncomputable def pivotPermutationTable (dimension count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (permutationFold dimension count).onResults (fun _ => selectedDomain dimension count)
    (fun _ arguments => Function.Injective (arguments ()))
    (fun name _ arguments => match name with
      | .inl _ => arguments.val ()
      | .inr false => id
      | .inr true => id)
    (by intro sizes arguments; exact ⟨arguments.property, rfl, rfl⟩)

/-- Identity preparation, position enumeration, and all image-table updates are polynomial-time. -/
theorem pivotPermutationTable_realizable (dimension count : MvPolynomial Parameter ℕ) :
    (pivotPermutationTable dimension count).Realizable := by
  let computation := pivotPermutationTable dimension count
  apply (permutationFold_realizable dimension count).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | .inl _ => arguments.val ()
      | .inr false => id
      | .inr true => id)
    (by intro sizes arguments; exact ⟨arguments.property, rfl, rfl⟩)
  intro name
  rcases name with singleton | choice
  · exact Realizable.argument computation.inputDomains () computation.precondition
  · cases choice
    · exact (arrayBoundedPositions_realizable dimension).onResults computation.inputDomains computation.precondition
        (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
    · exact (arrayPositions_realizable count).onResults computation.inputDomains computation.precondition
        (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)

/-- The computed table is exactly the mathematical pivot-compaction permutation. -/
theorem pivotPermutationTable_correct (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (pivotPermutationTable dimension count).Arguments sizes //
      (pivotPermutationTable dimension count).precondition sizes arguments})
    (selected : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes dimension))
    (same : arguments.val () = (fun index => selected index)) :
    (pivotPermutationTable dimension count).compute sizes arguments =
      (fun index => IntegerMatrix.pivotPermutation selected index) := by
  have reached := ArrayFold.prefix_invariant (permutationUpdate dimension count sizes (fun _ => arguments.val ()))
    (id : Fin (MvPolynomial.eval sizes count) → Fin (MvPolynomial.eval sizes count))
    (id : Fin (MvPolynomial.eval sizes dimension) → Fin (MvPolynomial.eval sizes dimension))
    (permutationInvariant dimension count sizes (fun _ => arguments.val ()))
    (by intro embedding same; exact ⟨Nat.zero_le _, rfl⟩)
    (fun index table before => permutationPreserves dimension count sizes (fun _ => arguments.val ()) arguments.property index table before)
    (MvPolynomial.eval sizes count) (by rfl)
  obtain ⟨within, equal⟩ := reached selected same
  exact equal

/-- The returned image table is a genuine permutation of the full dimension. -/
theorem pivotPermutationTable_bijective (dimension count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (pivotPermutationTable dimension count).Arguments sizes //
      (pivotPermutationTable dimension count).precondition sizes arguments}) :
    Function.Bijective ((pivotPermutationTable dimension count).compute sizes arguments) := by
  let selected : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes dimension) :=
    ⟨arguments.val (), arguments.property⟩
  rw [pivotPermutationTable_correct dimension count sizes arguments selected rfl]
  exact (IntegerMatrix.pivotPermutation selected).bijective

end Polytime2.Computation
