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

import Polytime.Examples.MatrixTraversal

/-! # Complete elimination in a prepared matrix frame

A restoring guard traverses all columns. Each body performs the certified
column step and increments the runtime column counter. The loop invariant
identifies the remaining mathematical elimination, including empty dimensions.
-/

namespace Polytime.Examples.MatrixEliminate

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section Elimination

open MatrixTraversal (Value)

variable (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] [DecidableEq field.Carrier]

private def remaining (sizes : SizeAssignment Matrices.context) (value : Value field sizes) :=
  GaussJordan.eliminateColumns value.2.1 value.2.2 ((List.finRange (sizes .L)).drop value.1)

private theorem remaining_advance (sizes : SizeAssignment Matrices.context) (value : Value field sizes) :
    remaining field sizes (MatrixTraversal.advance field sizes value) = remaining field sizes value := by
  by_cases active : value.1 < sizes .L
  · have columns : (List.finRange (sizes .L)).drop value.1 =
        ⟨value.1, active⟩ :: (List.finRange (sizes .L)).drop (value.1 + 1) := by
      rw [List.drop_eq_getElem_cons (l := List.finRange (sizes .L)) (i := value.1) (by simpa using active)]
      congr 1
      apply Fin.ext
      simp
    simp only [remaining, MatrixTraversal.advance, dite_eq_left active, columns, GaussJordan.eliminateColumns]
  · simp only [MatrixTraversal.advance, dite_eq_right active]

/-- The elimination proof uses mathematical states and a fold only;
frame layout, scratch values, finite controllers, and runtime bounds are hidden. -/
theorem contract : Realization.Realizes (MatrixTraversal.representation field) (MatrixTraversal.representation field)
    (fun sizes value => MatrixTraversal.valid field sizes value ∧ value.1 = 0 ∧ value.2.2 = 0)
    (fun sizes initial final => final.1 = sizes .L ∧ final.2.1 = GaussJordan.eliminate initial.2.1 ∧ final.2.2 ≤ sizes .K) := by
  apply (MatrixTraversal.traverse_contract field).consequence (by intro sizes value valid; exact valid.1)
  intro sizes initial final started finished
  obtain ⟨folded, valid, stopped⟩ := finished
  have preservesRemaining : ∀ count (value : Value field sizes),
      remaining field sizes ((MatrixTraversal.advance field sizes)^[count] value) = remaining field sizes value := by
    intro count
    induction count with
    | zero => intro value; rfl
    | succ count hypothesis =>
      intro value
      rw [Function.iterate_succ_apply', remaining_advance]
      exact hypothesis value
  have preserved : remaining field sizes final = remaining field sizes initial := by
    rw [folded]
    exact preservesRemaining _ _
  have finalColumn : final.1 = sizes .L := by
    have exited : ¬ final.1 < sizes .L := by simpa only [MatrixTraversal.condition, decide_eq_false_iff_not] using stopped
    have upper := valid.1
    omega
  refine ⟨finalColumn, ?_, valid.2⟩
  have matrices := congrArg Prod.fst preserved
  have empty : (List.finRange (sizes .L)).drop (sizes .L) = [] := List.drop_eq_nil_of_le (by simp)
  simpa only [remaining, finalColumn, empty, started.2.1, started.2.2, List.drop_zero,
    GaussJordan.eliminateColumns, GaussJordan.eliminate] using matrices

/-- One finite controller realizes complete Gauss–Jordan elimination in a
prepared frame, with a polynomial bound in both matrix dimensions. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (GaussJordan.eliminate matrix)).getLsbD index.val)
          ∃ (finalRow : ℕ) (finalScalar : field.Carrier) (ticks : ℕ),
            ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
              (Tape.configuration entry []
                (UnaryMachine.fields [0, rows, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [finalRow, rows, columns, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            finalRow ≤ rows ∧ (GaussJordan.eliminate matrix).IsReducedRowEchelon ∧
            ∃ transformation : Matrix.GeneralLinearGroup (Fin rows) field.Carrier,
              (transformation : Matrix (Fin rows) (Fin rows) field.Carrier) * matrix = GaussJordan.eliminate matrix := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := contract field
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix initialScalar right
  let sizes := assignment rows columns
  let initial : Value field sizes := (0, matrix, 0)
  obtain ⟨final, finalTape, ticks, cost, trace, correct, represented⟩ :=
    runs sizes right initial _ ⟨⟨by simp [initial], by simp [initial]⟩, rfl, rfl⟩
      ⟨initialScalar, rfl⟩
  obtain ⟨finalScalar, equal⟩ := represented
  rw [equal] at trace
  refine ⟨final.2.2, finalScalar, ticks, cost, ?_, correct.2.2, GaussJordan.correct matrix⟩
  have finalColumn : final.1 = columns := correct.1
  have finalMatrix : final.2.1 = GaussJordan.eliminate matrix := correct.2.1
  simp only [MatrixTraversal.frame, MatrixTraversal.layout_values] at trace
  dsimp only [MatrixTraversal.suffix, initial, sizes, assignment, Tape.configuration] at trace
  rw [finalColumn, finalMatrix] at trace
  simpa only [Tape.configuration, List.append_assoc] using trace

end Elimination

end Polytime.Examples.MatrixEliminate
