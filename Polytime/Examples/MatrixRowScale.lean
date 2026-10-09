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

import Polytime.Examples.MatrixRowMap
import Polytime.FiniteDispatchMachine
import Polytime.Matrix
import Polytime.HeaderResetMachine

/-! # Row scaling with a coefficient read from the tape

All bit-pattern branches are compiled into a single finite controller before
the coefficient, matrix dimensions, or row index are supplied. Summing their
polynomial bounds gives one bound independent of the runtime coefficient.
-/

namespace Polytime.Examples.MatrixRowScale

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeCoefficient

/-- Scale a runtime-selected row by a runtime coefficient. Its leading scalar
slot is consumed; the original matrix frame remains and its column counter is reset.
Zero coefficients and zero-column matrices are included. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (row : Fin rows) (coefficient initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (MatrixOperations.scaleRow matrix row coefficient)).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (word (List.ofFn (BoolTuple.fromBits (field.codec.encode coefficient))) ++
                  UnaryMachine.fields [row.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields [row.val, 0, columns] ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  classical
  let Bits := Fin field.bitWidth → Bool
  let coefficientOf (bits : Bits) := (field.codec.decode (BoolTuple.toBits bits)).getD 0
  have realizations := fun bits : Bits =>
    MatrixRowMap.realizes field (fun value => coefficientOf bits * value)
  choose Branch branchFinite branchInhabited entries exits branches bounds halts runs using realizations
  let familyFinite : ∀ bits, Fintype (Branch bits) := branchFinite
  let familyInhabited : ∀ bits, Inhabited (Branch bits) := branchInhabited
  let uniformBound : SizePolynomial Matrices.context := ∑ bits : Bits, bounds bits
  let resetBound : SizePolynomial Matrices.context :=
    SizePolynomial.parameter (ctx := Matrices.context) .L *
      (SizePolynomial.constant 6 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 4) +
      SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 2
  refine ⟨Sum (FiniteDispatchMachine.State Branch) (HeaderResetMachine.State 1), inferInstance, inferInstance,
    .inl (.inl (0, (fun _ => false), 0)), .inr (.inr (0, 8)),
    Tape.sequence (FiniteDispatchMachine.machine branches entries) (HeaderResetMachine.machine 1) (.inl (Fin.last 1)),
    uniformBound + resetBound + SizePolynomial.constant (4 * field.bitWidth + 5), ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, HeaderResetMachine.halt]
  · intro rows columns matrix row coefficient initialScalar right
    dsimp only
    let selector := BoolTuple.fromBits (field.codec.encode coefficient)
    have decoded : coefficientOf selector = coefficient := by
      simp [coefficientOf, selector, field.codec.decode_encode]
    have updateEquality : Function.update matrix row (fun column => coefficient * matrix row column) =
        MatrixOperations.scaleRow matrix row coefficient := by
      funext i j
      by_cases sameRow : i = row <;> simp [Function.update, MatrixOperations.scaleRow, sameRow]
    obtain ⟨finalScalar, ticks, cost, trace⟩ := runs selector rows columns matrix row initialScalar right
    rw [decoded, updateEquality] at trace
    have realized := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      ticks _ _ (halts selector) trace
    let matrixWidth := (domain field).bitWidth (assignment rows columns)
    let output := List.ofFn (fun index : Fin matrixWidth =>
      (encode field rows columns (MatrixOperations.scaleRow matrix row coefficient)).getLsbD index.val)
    let suffix := word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
      3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right))
    have reset := HeaderResetMachine.realizes [row.val] columns (UnaryMachine.fields [columns] ++ suffix)
    have reset' : Tape.Steps (HeaderResetMachine.machine 1)
        (columns * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2)
        (Tape.configuration (.inl (Fin.last 1)) [] (UnaryMachine.fields [row.val, columns, columns] ++ suffix))
        (Tape.configuration (.inr (0, 8)) [] (UnaryMachine.fields [row.val, 0, columns] ++ suffix)) := by
      simpa [UnaryMachine.fields, List.append_assoc] using reset
    simp only [List.append_assoc] at realized
    have composed := Tape.sequence_steps (Sum.inl (Fin.last 1) : HeaderResetMachine.State 1)
      realized (FiniteDispatchMachine.halt branches entries) reset'
    have uniformValue : uniformBound.eval (assignment rows columns) =
        ∑ bits : Bits, (bounds bits).eval (assignment rows columns) := by
      simp [uniformBound, SizePolynomial.eval, map_sum]
    have dominated : (bounds selector).eval (assignment rows columns) ≤
        uniformBound.eval (assignment rows columns) := by
      rw [uniformValue]
      exact Finset.single_le_sum (f := fun bits : Bits => (bounds bits).eval (assignment rows columns))
        (s := Finset.univ) (by intro bits _; exact Nat.zero_le _) (Finset.mem_univ selector)
    have resetCost : columns * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2 ≤
        resetBound.eval (assignment rows columns) := by
      have prefixBound : row.val + 1 ≤ rows := row.isLt
      have first := Nat.mul_le_mul_left columns
        (Nat.add_le_add_right (Nat.mul_le_mul_left 6 prefixBound) 4)
      have second := Nat.mul_le_mul_left 2 prefixBound
      simp [resetBound, assignment]
      omega
    refine ⟨finalScalar, 4 * field.bitWidth + ticks + 4 +
      (columns * (6 * (row.val + 1) + 4) + 2 * (row.val + 1) + 2 + 1), ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [selector, matrixWidth, suffix, output, Tape.configuration, List.append_assoc] using composed

end RuntimeCoefficient

end Polytime.Examples.MatrixRowScale
