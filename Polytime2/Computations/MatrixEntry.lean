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

import Polytime2.Computation.Layout
import Polytime2.StandardMatrixRowsPresentation
import Polytime2.StandardMatrixReplaceContract

/-! # Row-and-column access to ordinary mathematical matrices -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable StandardMatrixRows

noncomputable section MatrixCoordinates

/-- Arguments are binary row and column indices and the immutable matrix. -/
def matrixEntry (scalar : EncodedDomain Empty) : Computation (Fin 3) (Fin 3) where
  inputDomains
    | 0 | 1 => EncodedDomain.binaryNaturals 0
    | 2 => matrixDomain scalar
  outputDomain := scalar.constant
  precondition sizes arguments := sizes 2 < 2 ^ sizes 0 ∧
    (arguments 0).val < sizes 1 ∧ (arguments 1).val < sizes 2 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments := (arguments.val 2)
    ⟨(arguments.val 0).val, arguments.property.2.1⟩
    ⟨(arguments.val 1).val, arguments.property.2.2.1⟩

/-- Arguments are row, column, immutable matrix, and replacement scalar.
The result changes exactly that coordinate and has the same mathematical shape. -/
def matrixReplace (scalar : EncodedDomain Empty) : Computation (Fin 3) (Fin 4) where
  inputDomains
    | 0 | 1 => EncodedDomain.binaryNaturals 0
    | 2 => matrixDomain scalar
    | 3 => scalar.constant
  outputDomain := matrixDomain scalar
  precondition sizes arguments := sizes 2 < 2 ^ sizes 0 ∧
    (arguments 0).val < sizes 1 ∧ (arguments 1).val < sizes 2 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0
  compute _ arguments :=
    let row := ⟨(arguments.val 0).val, arguments.property.2.1⟩
    let column := ⟨(arguments.val 1).val, arguments.property.2.2.1⟩
    Function.update (arguments.val 2) row
      (Function.update (arguments.val 2 row) column (arguments.val 3))

namespace Realizable.Internal

private def matrixEntryLayout (name : StandardMatrixEntry.TapeName) :
    Fin 3 ⊕ (Fin 3 ⊕ (Unit ⊕ StandardMatrixEntry.TapeName)) :=
  match name with
  | .inl (.inl parameter) => .inl parameter
  | .inl (.inr 1) => .inr (.inl 0)
  | .inl (.inr 6) => .inr (.inl 1)
  | .inr false => .inr (.inl 2)
  | .inr true => .inr (.inr (.inl ()))
  | privateTape => .inr (.inr (.inr privateTape))

private def matrixEntrySource : Fin 3 ⊕ (Fin 3 ⊕ (Unit ⊕ StandardMatrixEntry.TapeName)) → StandardMatrixEntry.TapeName
  | .inl parameter => .inl (.inl parameter)
  | .inr (.inl 0) => .inl (.inr 1)
  | .inr (.inl 1) => .inl (.inr 6)
  | .inr (.inl 2) => .inr false
  | .inr (.inr (.inl _)) => .inr true
  | .inr (.inr (.inr name)) => name

private theorem matrixEntryLayout_leftInverse : Function.LeftInverse matrixEntrySource matrixEntryLayout := by
  intro name
  fin_cases name <;> rfl

private def matrixEntryEmbedding : StandardMatrixEntry.TapeName ↪ Fin 3 ⊕ (Fin 3 ⊕ (Unit ⊕ StandardMatrixEntry.TapeName)) :=
  ⟨matrixEntryLayout, matrixEntryLayout_leftInverse.injective⟩

private def matrixEntryDomains (scalar : EncodedDomain Empty) : StandardMatrixEntry.TapeName → EncodedDomain (Fin 3)
  | .inr false => matrixDomain scalar
  | name => StandardMatrixEntry.domains scalar.constant name

private def matrixEntryEquivalence (scalar : EncodedDomain Empty) (name : StandardMatrixEntry.TapeName) (sizes : Fin 3 → ℕ) :
    (matrixEntryDomains scalar name).Carrier sizes ≃ (StandardMatrixEntry.domains scalar.constant name).Carrier sizes :=
  match name with
  | .inr false => matrixEquiv sizes
  | .inr true => Equiv.refl _
  | .inl _ => Equiv.refl _

private theorem matrixEntryDomainEqual (scalar : EncodedDomain Empty) (name : StandardMatrixEntry.TapeName) :
    domains (matrixEntry scalar) (StandardMatrixEntry.domains scalar.constant) (matrixEntryEmbedding name) =
      matrixEntryDomains scalar name := by
  fin_cases name <;> rfl

private def matrixReplaceLayout (name : StandardMatrixReplace.TapeName) :
    Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ StandardMatrixReplace.TapeName)) :=
  match name with
  | .inl (.inl parameter) => .inl parameter
  | .inl (.inr 1) => .inr (.inl 0)
  | .inl (.inr 6) => .inr (.inl 1)
  | .inr 0 => .inr (.inl 2)
  | .inr 1 => .inr (.inl 3)
  | .inr 2 => .inr (.inr (.inl ()))
  | privateTape => .inr (.inr (.inr privateTape))

private def matrixReplaceSource : Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ StandardMatrixReplace.TapeName)) → StandardMatrixReplace.TapeName
  | .inl parameter => .inl (.inl parameter)
  | .inr (.inl 0) => .inl (.inr 1)
  | .inr (.inl 1) => .inl (.inr 6)
  | .inr (.inl 2) => .inr 0
  | .inr (.inl 3) => .inr 1
  | .inr (.inr (.inl _)) => .inr 2
  | .inr (.inr (.inr name)) => name

private theorem matrixReplaceLayout_leftInverse : Function.LeftInverse matrixReplaceSource matrixReplaceLayout := by
  intro name
  fin_cases name <;> rfl

private def matrixReplaceEmbedding : StandardMatrixReplace.TapeName ↪ Fin 3 ⊕ (Fin 4 ⊕ (Unit ⊕ StandardMatrixReplace.TapeName)) :=
  ⟨matrixReplaceLayout, matrixReplaceLayout_leftInverse.injective⟩

private def matrixReplaceDomains (scalar : EncodedDomain Empty) : StandardMatrixReplace.TapeName → EncodedDomain (Fin 3)
  | .inr 0 => matrixDomain scalar
  | .inr 2 => matrixDomain scalar
  | name => StandardMatrixReplace.domains scalar.constant name

private def matrixReplaceEquivalence (scalar : EncodedDomain Empty) (name : StandardMatrixReplace.TapeName) (sizes : Fin 3 → ℕ) :
    (matrixReplaceDomains scalar name).Carrier sizes ≃ (StandardMatrixReplace.domains scalar.constant name).Carrier sizes :=
  match name with
  | .inr 0 => matrixEquiv sizes
  | .inr 2 => matrixEquiv sizes
  | .inr 1 => Equiv.refl _
  | .inl _ => Equiv.refl _

private theorem matrixReplaceDomainEqual (scalar : EncodedDomain Empty) (name : StandardMatrixReplace.TapeName) :
    domains (matrixReplace scalar) (StandardMatrixReplace.domains scalar.constant) (matrixReplaceEmbedding name) =
      matrixReplaceDomains scalar name := by
  fin_cases name <;> rfl

private theorem matrixEquiv_replace {Carrier : Type} (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Carrier)
    (row : Fin (sizes 1)) (column : Fin (sizes 2)) (value : Carrier) :
    matrixEquiv sizes (Function.update matrix row (Function.update (matrix row) column value)) =
      Function.update (matrixEquiv sizes matrix) (matrixIndex sizes (row, column)) value := by
  apply (matrixEquiv (Carrier := Carrier) sizes).symm.injective
  refine ((matrixEquiv (Carrier := Carrier) sizes).symm_apply_apply _).trans ?_
  funext otherRow otherColumn
  change Function.update matrix row (Function.update (matrix row) column value) otherRow otherColumn =
    Function.update (matrixEquiv sizes matrix) (matrixIndex sizes (row, column)) value
      (matrixIndex sizes (otherRow, otherColumn))
  by_cases sameRow : otherRow = row <;> by_cases sameColumn : otherColumn = column <;>
    simp_all [Function.update, (matrixIndex sizes).injective.eq_iff, Prod.mk.injEq, matrixEquiv_apply]

end Realizable.Internal

open Realizable.Internal in
theorem matrixEntry_realizable (scalar : EncodedDomain Empty) : (matrixEntry scalar).Realizable := by
  let computation := matrixEntry scalar
  let scratchDomains := StandardMatrixEntry.domains scalar.constant
  let values name sizes := (Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (matrixEntryDomainEqual scalar name))).trans
      (matrixEntryEquivalence scalar name sizes)
  refine ofLayout computation scratchDomains (StandardMatrixEntry.domains scalar.constant)
    StandardMatrixEntry.readOnly StandardMatrixEntry.sizeTapes StandardMatrixEntry.outputTapes
    (StandardMatrixEntry.machine (scalar.width Empty.elim))
    (StandardMatrixEntry.entry (scalar.width Empty.elim)) (StandardMatrixEntry.exit (scalar.width Empty.elim)) _ _
    (StandardMatrixEntry.contract scalar.constant (scalar.width Empty.elim) (fun _ => rfl))
    matrixEntryEmbedding values
    (by intro name sizes; fin_cases name <;> rfl)
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨within, result⟩ := correct
  let arguments := arguments computation scratchDomains sizes input
  let row : Fin (sizes 1) := ⟨(arguments 0).val, valid.2.1⟩
  let column : Fin (sizes 2) := ⟨(arguments 1).val, valid.2.2.1⟩
  have coordinate : (⟨(arguments 0).val * sizes 2 + (arguments 1).val, within⟩ :
      Fin (MvPolynomial.eval sizes StandardMatrixEntry.length)) = matrixIndex sizes (row, column) :=
    Fin.ext (matrixIndex_val sizes row column).symm
  change output () = matrixEquiv sizes (arguments 2)
    ⟨(arguments 0).val * sizes 2 + (arguments 1).val, within⟩ at result
  rw [coordinate] at result
  have computed := matrixEquiv_apply (Carrier := scalar.Carrier Empty.elim) sizes (arguments 2) row column
  exact congrArg (encoded scalar.constant sizes) (result.trans computed)

open Realizable.Internal in
theorem matrixReplace_realizable (scalar : EncodedDomain Empty) : (matrixReplace scalar).Realizable := by
  let computation := matrixReplace scalar
  let scratchDomains := StandardMatrixReplace.domains scalar.constant
  let values name sizes := (Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (matrixReplaceDomainEqual scalar name))).trans
      (matrixReplaceEquivalence scalar name sizes)
  refine ofLayout computation scratchDomains (StandardMatrixReplace.domains scalar.constant)
    StandardMatrixReplace.readOnly StandardMatrixReplace.sizeTapes StandardMatrixReplace.outputTapes
    (StandardMatrixReplace.machine (scalar.width Empty.elim))
    (StandardMatrixReplace.entry (scalar.width Empty.elim)) (StandardMatrixReplace.exit (scalar.width Empty.elim)) _ _
    (StandardMatrixReplace.contract scalar.constant (scalar.width Empty.elim) (fun _ => rfl))
    matrixReplaceEmbedding values
    (by intro name sizes; fin_cases name <;> rfl)
    (by intro name sizes value; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨within, result⟩ := correct
  let arguments := arguments computation scratchDomains sizes input
  let row : Fin (sizes 1) := ⟨(arguments 0).val, valid.2.1⟩
  let column : Fin (sizes 2) := ⟨(arguments 1).val, valid.2.2.1⟩
  have coordinate : (⟨(arguments 0).val * sizes 2 + (arguments 1).val, within⟩ :
      Fin (MvPolynomial.eval sizes StandardMatrixEntry.length)) = matrixIndex sizes (row, column) :=
    Fin.ext (matrixIndex_val sizes row column).symm
  change output () = Function.update (matrixEquiv sizes (arguments 2))
    ⟨(arguments 0).val * sizes 2 + (arguments 1).val, within⟩ (arguments 3) at result
  rw [coordinate] at result
  have represented := result.trans (matrixEquiv_replace sizes (arguments 2) row column (arguments 3)).symm
  exact congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) represented

end MatrixCoordinates
end Polytime2.Computation
