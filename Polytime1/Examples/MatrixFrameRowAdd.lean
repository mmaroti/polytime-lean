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

import Polytime1.Examples.MatrixFrameRowCombine
import Polytime1.Matrix
import Polytime1.FiniteDispatchMachine

/-! # Runtime row addition retaining caller header counters

All bit-pattern branches are compiled into a single finite controller before
the coefficient, matrix dimensions, or row index are supplied. Summing their
polynomial bounds gives one bound independent of the runtime coefficient.
-/

namespace Polytime1.Examples.MatrixFrameRowAdd

open Matrices TupleMachine

-- scalarLevel: the mathematical carrier of the fixed finite field.
universe scalarLevel

noncomputable section RuntimeCoefficient

/-- Dispatch a runtime scalar coefficient to a fixed binary row operation,
retaining caller counters and resetting the traversal column. -/
theorem realizes_operation (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (operation : field.Carrier → field.Carrier → field.Carrier → field.Carrier)
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (coefficient initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (Function.update matrix target (fun column => operation coefficient (matrix source column) (matrix target column)))).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (word (List.ofFn (BoolTuple.fromBits (field.codec.encode coefficient))) ++
                  UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) := by
  classical
  let Bits := Fin field.bitWidth → Bool
  let coefficientOf (bits : Bits) := (field.codec.decode (BoolTuple.toBits bits)).getD 0
  have realizations := fun bits : Bits =>
    MatrixFrameRowCombine.realizes_reset field (operation (coefficientOf bits)) extraCount extraBound
  choose Branch branchFinite branchInhabited entries exits branches bounds halts runs using realizations
  let familyFinite : ∀ bits, Fintype (Branch bits) := branchFinite
  let familyInhabited : ∀ bits, Inhabited (Branch bits) := branchInhabited
  let uniformBound : SizePolynomial Matrices.context := ∑ bits : Bits, bounds bits
  refine ⟨FiniteDispatchMachine.State Branch, inferInstance, inferInstance,
    .inl (0, (fun _ => false), 0), .inr (.inr ()),
    FiniteDispatchMachine.machine branches entries,
    uniformBound + SizePolynomial.constant (4 * field.bitWidth + 4), ?_, ?_⟩
  · exact FiniteDispatchMachine.halt branches entries
  · intro rows columns matrix source target extra extraLength extraBounded coefficient initialScalar right
    dsimp only
    let selector := BoolTuple.fromBits (field.codec.encode coefficient)
    have decoded : coefficientOf selector = coefficient := by
      simp [coefficientOf, selector, field.codec.decode_encode]
    obtain ⟨finalScalar, ticks, cost, trace⟩ := runs selector rows columns matrix source target extra extraLength extraBounded initialScalar right
    rw [decoded] at trace
    have realized := FiniteDispatchMachine.realizes branches entries selector (exits selector)
      ticks _ _ (halts selector) trace
    have uniformValue : uniformBound.eval (assignment rows columns) =
        ∑ bits : Bits, (bounds bits).eval (assignment rows columns) := by
      simp [uniformBound, SizePolynomial.eval, map_sum]
    have dominated : (bounds selector).eval (assignment rows columns) ≤
        uniformBound.eval (assignment rows columns) := by
      rw [uniformValue]
      exact Finset.single_le_sum (f := fun bits : Bits => (bounds bits).eval (assignment rows columns))
        (s := Finset.univ) (by intro bits _; exact Nat.zero_le _) (Finset.mem_univ selector)
    refine ⟨finalScalar, 4 * field.bitWidth + ticks + 4, ?_, ?_⟩
    · simp only [SizePolynomial.eval_add, SizePolynomial.eval_constant]
      omega
    · simpa only [selector, Tape.configuration, List.append_assoc] using realized

/-- Add a runtime multiple of the source row to the target, retaining caller counters. -/
theorem realizes (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (coefficient initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (Function.update matrix target (fun column => matrix target column + coefficient * matrix source column))).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (word (List.ofFn (BoolTuple.fromBits (field.codec.encode coefficient))) ++
                  UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (source ≠ target → Matrix.RowEquivalent matrix (Function.update matrix target
              (fun column => matrix target column + coefficient * matrix source column))) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_operation field (fun coefficient source target => target + coefficient * source) extraCount extraBound
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target extra extraLength extraBounded coefficient initialScalar right
  obtain ⟨finalScalar, ticks, cost, trace⟩ :=
    runs rows columns matrix source target extra extraLength extraBounded coefficient initialScalar right
  exact ⟨finalScalar, ticks, cost, trace, MatrixOperations.addRow_rowEquivalent matrix source target coefficient⟩

/-- Scale the target row by a runtime coefficient, retaining the source index and caller counters. -/
theorem realizes_scale (field : FixedPresentation.{scalarLevel}) [Field field.Carrier]
    (extraCount : ℕ) (extraBound : SizePolynomial Matrices.context) :
    ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial Matrices.context),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (rows columns : ℕ) (matrix : Matrix (Fin rows) (Fin columns) field.Carrier)
          (source target : Fin rows)
          (extra : List ℕ) (_extraLength : extra.length = extraCount)
          (_extraBounded : (UnaryMachine.fields extra).length ≤ extraBound.eval (assignment rows columns))
          (coefficient initialScalar : field.Carrier) (right : List Symbol),
          let matrixWidth := (domain field).bitWidth (assignment rows columns)
          let payload := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns matrix).getLsbD index.val)
          let output := List.ofFn (fun index : Fin matrixWidth =>
            (encode field rows columns (MatrixOperations.scaleRow matrix target coefficient)).getLsbD index.val)
          ∃ (finalScalar : field.Carrier) (ticks : ℕ), ticks ≤ bound.eval (assignment rows columns) ∧
            Tape.Steps machine ticks
              (Tape.configuration entry []
                (word (List.ofFn (BoolTuple.fromBits (field.codec.encode coefficient))) ++
                  UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode initialScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word payload ++ right))))
              (Tape.configuration exit []
                (UnaryMachine.fields ([source.val, target.val, 0, columns] ++ extra) ++
                  word (List.ofFn (BoolTuple.fromBits (field.codec.encode finalScalar))) ++
                  3 :: (List.replicate matrixWidth (data true) ++ 4 :: (word output ++ right)))) ∧
            (coefficient ≠ 0 → Matrix.RowEquivalent matrix (MatrixOperations.scaleRow matrix target coefficient)) := by
  classical
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_operation field (fun coefficient _source target => coefficient * target) extraCount extraBound
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro rows columns matrix source target extra extraLength extraBounded coefficient initialScalar right
  obtain ⟨finalScalar, ticks, cost, trace⟩ :=
    runs rows columns matrix source target extra extraLength extraBounded coefficient initialScalar right
  have updateEquality : Function.update matrix target (fun column => coefficient * matrix target column) =
      MatrixOperations.scaleRow matrix target coefficient := by
    funext row column
    by_cases same : row = target <;> simp [Function.update, MatrixOperations.scaleRow, same]
  rw [updateEquality] at trace
  exact ⟨finalScalar, ticks, cost, trace, MatrixOperations.scaleRow_rowEquivalent matrix target coefficient⟩

end RuntimeCoefficient

end Polytime1.Examples.MatrixFrameRowAdd
