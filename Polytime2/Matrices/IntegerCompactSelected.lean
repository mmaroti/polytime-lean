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

import Polytime2.Matrices.IntegerReindex
import Polytime2.Matrices.PivotPermutation

/-! # Compaction from selected pivot arrays

For injective selected row and column arrays of the same length, construct the
canonical pivot permutations and apply them to the matrix and both bases.
No entry bound grows. The length is a polynomial parameter here; the stored
rank adapter supplies it when compaction follows a Hermite sweep.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def compactInputs
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Fin 5 → EncodedDomain Parameter
  | 0 => (boundedIndex rows).arrayOfLength count
  | 1 => (boundedIndex columns).arrayOfLength count
  | 2 => integerMatrices rows columns matrixWidth
  | 3 => integerMatrices rows rows leftWidth
  | 4 => integerMatrices columns columns rightWidth

private def compactAllowed
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : ∀ name, (compactInputs rows columns count matrixWidth leftWidth rightWidth name).Carrier sizes) : Prop :=
  Function.Injective (arguments 0) ∧ Function.Injective (arguments 1)

private noncomputable def compactResults
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (name : Fin 5) (sizes : Parameter → ℕ)
    (arguments : {arguments // compactAllowed rows columns count matrixWidth leftWidth rightWidth sizes arguments}) :
    ((integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).inputDomains name).Carrier sizes :=
  match name with
  | 0 => (pivotPermutationTable rows count).compute sizes
      ⟨fun _ => arguments.val 0, arguments.property.1⟩
  | 1 => (pivotPermutationTable columns count).compute sizes
      ⟨fun _ => arguments.val 1, arguments.property.2⟩
  | 2 => arguments.val 2
  | 3 => arguments.val 3
  | 4 => arguments.val 4

/-- Compact selected pivots, carrying both actual transformation matrices. -/
noncomputable def integerCompactSelected
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  (integerReindexWithBases rows columns matrixWidth leftWidth rightWidth).onResults
    (compactInputs rows columns count matrixWidth leftWidth rightWidth)
    (compactAllowed rows columns count matrixWidth leftWidth rightWidth)
    (compactResults rows columns count matrixWidth leftWidth rightWidth)
    (by intros; trivial)

/-- Compaction composes two permutation tables and the coupled gather. -/
theorem integerCompactSelected_realizable
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerCompactSelected rows columns count matrixWidth leftWidth rightWidth).Realizable := by
  let context := compactInputs rows columns count matrixWidth leftWidth rightWidth
  let allowed := compactAllowed rows columns count matrixWidth leftWidth rightWidth
  apply (integerReindexWithBases_realizable rows columns matrixWidth leftWidth rightWidth).onResults
    context allowed (compactResults rows columns count matrixWidth leftWidth rightWidth) (by intros; trivial)
  intro name
  fin_cases name
  · exact (pivotPermutationTable_realizable rows count).onArguments context allowed
      (fun _ => 0) (by intro _; rfl) (by intro sizes arguments; exact arguments.property.1)
  · exact (pivotPermutationTable_realizable columns count).onArguments context allowed
      (fun _ => 1) (by intro _; rfl) (by intro sizes arguments; exact arguments.property.2)
  · exact Realizable.argument context 2 allowed
  · exact Realizable.argument context 3 allowed
  · exact Realizable.argument context 4 allowed

/-- The realized result is exactly compaction by the canonical pivot permutations. -/
theorem integerCompactSelected_correct
    (rows columns count matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments :
      (integerCompactSelected rows columns count matrixWidth leftWidth rightWidth).Arguments sizes //
      (integerCompactSelected rows columns count matrixWidth leftWidth rightWidth).precondition sizes arguments}) :
    let selectedRows : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes rows) :=
      ⟨arguments.val 0, arguments.property.1⟩
    let selectedColumns : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes columns) :=
      ⟨arguments.val 1, arguments.property.2⟩
    let result := (integerCompactSelected rows columns count matrixWidth leftWidth rightWidth).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.permuteWithBases (IntegerMatrix.pivotPermutation selectedRows)
        (IntegerMatrix.pivotPermutation selectedColumns)
        (arguments.val 2).val (arguments.val 3).val (arguments.val 4).val := by
  let selectedRows : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes rows) :=
    ⟨arguments.val 0, arguments.property.1⟩
  let selectedColumns : Fin (MvPolynomial.eval sizes count) ↪ Fin (MvPolynomial.eval sizes columns) :=
    ⟨arguments.val 1, arguments.property.2⟩
  have rowTable := pivotPermutationTable_correct rows count sizes
    ⟨fun _ => arguments.val 0, arguments.property.1⟩ selectedRows rfl
  have columnTable := pivotPermutationTable_correct columns count sizes
    ⟨fun _ => arguments.val 1, arguments.property.2⟩ selectedColumns rfl
  dsimp only [integerCompactSelected, Computation.onResults, integerReindexWithBases,
    compactResults, IntegerMatrix.permuteWithBases]
  rw [rowTable, columnTable]

end Polytime2.Computation
