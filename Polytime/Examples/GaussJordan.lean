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

import Polytime.GaussJordan
import Polytime.Examples.MatrixEliminate
import Polytime.Examples.Matrices
import Polytime.Examples.MatrixPrepareFrame
import Polytime.FrameExtractMachine

/-! # Rectangular elimination over fixed prime fields

The mathematical algorithm and its RREF and invertible-transformation contracts
are proved here. `realizes` composes frame preparation, complete elimination,
and output extraction into a polynomial-time external tape realization.
-/

namespace Polytime.Examples.GaussJordan

open Polytime.GaussJordan (eliminate)

section PrimeFields

variable {prime rows columns : ℕ} [Fact (Nat.Prime prime)]

/-- Every fixed prime field is an instance, with independent matrix dimensions. -/
example (matrix : Matrix (Fin rows) (Fin columns) (ZMod prime)) :
    (eliminate matrix).IsReducedRowEchelon ∧
      ∃ transformation : Matrix.GeneralLinearGroup (Fin rows) (ZMod prime),
        (transformation : Matrix (Fin rows) (Fin rows) (ZMod prime)) * matrix = eliminate matrix :=
  Polytime.GaussJordan.correct matrix

end PrimeFields

section FieldFiveChecks

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A swap is needed, and the first pivot must be divided by three.
#guard eliminate (!![0, 1, 2; 3, 4, 0] : Matrix (Fin 2) (Fin 3) (ZMod 5)) =
  !![1, 0, 4; 0, 1, 2]
-- Entirely missing leading columns and a dependent row are retained.
#guard eliminate (!![0, 2, 4; 0, 1, 2; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 5)) =
  !![0, 1, 2; 0, 0, 0; 0, 0, 0]
-- Tall rectangular input: all rows below the rank become zero.
#guard eliminate (!![0, 1; 1, 2; 2, 4; 0, 0] : Matrix (Fin 4) (Fin 2) (ZMod 5)) =
  !![1, 0; 0, 1; 0, 0; 0, 0]
#guard eliminate (0 : Matrix (Fin 2) (Fin 3) (ZMod 5)) = 0
#guard eliminate (0 : Matrix (Fin 0) (Fin 3) (ZMod 5)) = 0
#guard eliminate (0 : Matrix (Fin 3) (Fin 0) (ZMod 5)) = 0

end FieldFiveChecks

-- scalarLevel: the mathematical carrier of the specialized fixed finite field.
universe scalarLevel

noncomputable section TapeRealization

open Matrices TupleMachine

/-- Complete external realization: prepare the frame from the dimension header,
compute elimination, and extract its canonical output, all in polynomial time.
The finite controller is chosen before the runtime dimensions and matrix. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    [DecidableEq field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let input := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (eliminate matrix)).getLsbD index.val)
          ∃ ticks, ticks ≤ bound.eval (assignment rows columns) ∧ Tape.Steps machine ticks
            (Tape.configuration entry [] (UnaryMachine.fields [rows, columns] ++ word input ++ right))
            (Tape.configuration exit [] (word output ++ right)) ∧
            (eliminate matrix).IsReducedRowEchelon ∧
            ∃ transformation : Matrix.GeneralLinearGroup (Fin rows) field.Carrier,
              (transformation : Matrix (Fin rows) (Fin rows) field.Carrier) * matrix = eliminate matrix := by
  classical
  obtain ⟨PrepareState, prepareFinite, prepareInhabited, prepareEntry, prepareExit, preparer,
    prepareBound, prepareHalt, prepareRuns⟩ := MatrixPrepareFrame.realizes field 0
  let prepareControllerFinite : Fintype PrepareState := prepareFinite
  let prepareControllerInhabited : Inhabited PrepareState := prepareInhabited
  obtain ⟨EliminateState, eliminateFinite, eliminateInhabited, eliminateEntry, eliminateExit, eliminator,
    eliminateBound, eliminateHalt, eliminateRuns⟩ := MatrixEliminate.realizes field
  let eliminateControllerFinite : Fintype EliminateState := eliminateFinite
  let eliminateControllerInhabited : Inhabited EliminateState := eliminateInhabited
  let first := Tape.sequence preparer eliminator eliminateEntry
  let extractBound : SizePolynomial Matrices.context :=
    SizePolynomial.constant (2 * field.bitWidth) * SizePolynomial.parameter (ctx := Matrices.context) .K *
      SizePolynomial.parameter (ctx := Matrices.context) .L +
        SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K +
        SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .L +
        SizePolynomial.constant (2 * field.bitWidth + 12)
  refine ⟨Sum (Sum PrepareState EliminateState) (Fin 4), inferInstance, inferInstance,
    .inl (.inl prepareEntry), .inr 3, Tape.sequence first FrameExtractMachine.machine 0,
    prepareBound + eliminateBound + extractBound + SizePolynomial.constant 2, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, FrameExtractMachine.halt]
  · intro rows columns matrix right
    dsimp only
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let input := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns matrix).getLsbD index.val)
    let output := List.ofFn (fun index : Fin matrixWidth => (encode field rows columns (eliminate matrix)).getLsbD index.val)
    obtain ⟨prepareTicks, prepareCost, prepared⟩ := prepareRuns rows columns (word input ++ right)
    obtain ⟨finalRow, finalScalar, eliminateTicks, eliminateCost, eliminated, rowBound, correct⟩ :=
      eliminateRuns rows columns matrix 0 right
    simp only [List.append_assoc] at prepared eliminated
    have firstTrace := Tape.sequence_steps eliminateEntry prepared prepareHalt eliminated
    let working := UnaryMachine.fields [finalRow, rows, columns, columns] ++
      word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
        3 :: List.replicate matrixWidth (data true)
    have valid : ∀ symbol ∈ working, symbol ≠ 4 := by
      intro symbol member
      rcases List.mem_append.mp member with before | counter
      · rcases List.mem_append.mp before with header | scalar
        · rcases UnaryMachine.fields_symbols [finalRow, rows, columns, columns] symbol header with rfl | rfl <;> decide
        · obtain ⟨bit, _, equality⟩ := List.mem_map.mp scalar
          subst symbol
          cases bit <;> decide
      · rcases List.mem_cons.mp counter with rfl | units
        · decide
        · have equal : symbol = data true := List.eq_of_mem_replicate units
          subst symbol
          decide
    have extracted := FrameExtractMachine.realizes working (word output ++ right) valid
    have extracted' : Tape.Steps FrameExtractMachine.machine (2 * working.length + 2)
        (Tape.configuration 0 []
          (UnaryMachine.fields [finalRow, rows, columns, columns] ++
            word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
              3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))))
        (Tape.configuration 3 [] (word output ++ right)) := by
      simpa only [working, List.append_assoc, List.cons_append] using extracted
    simp only [List.append_assoc] at extracted'
    have firstHalt (symbol : Symbol) : first (.inr eliminateExit) symbol = none := by
      simp [first, Tape.sequence, eliminateHalt]
    have computation := Tape.sequence_steps 0 firstTrace firstHalt extracted'
    have extractionCost : 2 * working.length + 2 ≤ extractBound.eval (assignment rows columns) := by
      simp [working, word, extractBound, assignment, matrixWidth]
      nlinarith
    refine ⟨prepareTicks + (eliminateTicks + 1) + (2 * working.length + 2 + 1), ?_, ?_, correct⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [first, input, output, matrixWidth, Tape.configuration, List.append_assoc] using computation

end TapeRealization

end Polytime.Examples.GaussJordan
