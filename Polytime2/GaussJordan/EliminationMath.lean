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

import Polytime2.GaussJordan.EliminationLoop

/-! # Connecting the outer machine to mathematical elimination -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {cardinality : ℕ}

private theorem eliminateColumns_append {rows columns : ℕ}
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) (pivot : ℕ)
    (first second : List (Fin columns)) :
    GaussJordan.eliminateColumns matrix pivot (first ++ second) =
      GaussJordan.eliminateColumns
        (GaussJordan.eliminateColumns matrix pivot first).1
        (GaussJordan.eliminateColumns matrix pivot first).2 second := by
  induction first generalizing matrix pivot with
  | nil => rfl
  | cons column first inductionHypothesis =>
    exact inductionHypothesis (GaussJordan.columnStep matrix pivot column).1
      (GaussJordan.columnStep matrix pivot column).2

/-- Starting at column zero, the standard loop computes the existing
mathematical elimination function and returns its final pivot row. -/
theorem mathematical_loop_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_pivotWithin : pivot.val ≤ sizes 1) (_rowsFit : sizes 1 < 2 ^ sizes 0)
      (columnsFit : sizes 2 < 2 ^ sizes 0),
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ∃ finalPivot : Fin (2 ^ sizes 0), ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (loop enumeration) ticks
          (loopEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (loopExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.eliminateColumns matrix pivot.val (List.finRange (sizes 2))).1 ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes finalPivot ∧
        finalPivot.val = (GaussJordan.eliminateColumns matrix pivot.val (List.finRange (sizes 2))).2 ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨bound, execute⟩ := loop_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial pivot matrix pivotWithin rowsFit columnsFit capacity pivotEq
    columnEq matrixEq limitEq headers regions
  let states (count : ℕ) :=
    GaussJordan.eliminateColumns matrix pivot.val ((List.finRange (sizes 2)).take count)
  have stateBound (count : ℕ) : (states count).2 ≤ sizes 1 :=
    (GaussJordan.eliminateColumns_row_bound matrix pivot.val
      ((List.finRange (sizes 2)).take count) pivotWithin).2
  let matrices (count : ℕ) := (states count).1
  let pivots (count : ℕ) : Fin (2 ^ sizes 0) :=
    ⟨(states count).2, lt_of_le_of_lt (stateBound count) rowsFit⟩
  have stateStep (count : ℕ) (before : count < sizes 2) :
      GaussJordan.columnStep (matrices count) (pivots count).val ⟨count, before⟩ =
        (matrices (count + 1), (pivots (count + 1)).val) := by
    have prefixEq : (List.finRange (sizes 2)).take (count + 1) =
        (List.finRange (sizes 2)).take count ++ [⟨count, before⟩] := by
      have expanded := List.take_succ_eq_append_getElem
        (l := List.finRange (sizes 2)) (i := count) (by simpa using before)
      rw [List.getElem_finRange] at expanded
      exact expanded
    dsimp only [matrices, pivots, states]
    rw [prefixEq, eliminateColumns_append]
    rfl
  let start : Fin (2 ^ sizes 0) := ⟨0, by positivity⟩
  have firstPivot : pivots start.val = pivot := Fin.ext rfl
  have firstMatrix : matrices start.val = matrix := rfl
  obtain ⟨ticks, final, cost, trace, resultEq, finalRowEq, finalColumnEq⟩ :=
    execute sizes initial start (by simp [start]) rowsFit columnsFit matrices pivots stateBound stateStep
      capacity
      (pivotEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) firstPivot.symm))
      columnEq (matrixEq.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes)
        firstMatrix.symm)) limitEq headers regions
  have fullPrefix : (List.finRange (sizes 2)).take (sizes 2) = List.finRange (sizes 2) := by simp
  refine ⟨ticks, final, pivots (sizes 2), cost, trace, ?_, finalRowEq, ?_,
    finalColumnEq⟩
  · simpa only [matrices, states, fullPrefix] using resultEq
  · simp only [pivots, states, fullPrefix]

end Polytime2.StandardGaussJordanElimination
