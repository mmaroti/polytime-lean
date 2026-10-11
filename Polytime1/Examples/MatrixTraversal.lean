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

import Polytime1.Examples.MatrixColumnStep
import Polytime1.RealizationLoop

/-! # Mathematical states and contracts for matrix column traversal

The logical state contains the column, matrix, and pivot row. The temporary
scalar and physical navigation window belong only to its representation.
-/

namespace Polytime1.Examples.MatrixTraversal

open Matrices TupleMachine

-- scalarLevel: the carrier of the specialized finite field.
universe scalarLevel

abbrev Value (field : FixedPresentation.{scalarLevel}) (sizes : SizeAssignment Matrices.context) :=
  ℕ × (Matrix (Fin (sizes .K)) (Fin (sizes .L)) field.Carrier × ℕ)

/-- The restored traversal frame names its four counters. -/
abbrev layout : List MatrixColumnStep.HeaderField := [.savedRow, .rowCount, .column, .columnCount]

abbrev columnPosition : ℕ := layout.idxOf .column

noncomputable section ColumnContracts

variable (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] [DecidableEq field.Carrier]

def valid (sizes : SizeAssignment Matrices.context) (value : Value field sizes) : Prop :=
  value.1 ≤ sizes .L ∧ value.2.2 ≤ sizes .K

def condition (sizes : SizeAssignment Matrices.context) (value : Value field sizes) : Bool :=
  decide (value.1 < sizes .L)

def advance (sizes : SizeAssignment Matrices.context) (value : Value field sizes) : Value field sizes :=
  if active : value.1 < sizes .L then
    (value.1 + 1, GaussJordan.columnStep value.2.1 value.2.2 ⟨value.1, active⟩)
  else value

/-- The matrix payload and navigation window follow the temporary scalar. -/
def suffix (sizes : SizeAssignment Matrices.context) (value : Value field sizes)
    (scalar : field.Carrier) (right : List Symbol) : List Symbol :=
  let width := (domain field).bitWidth (assignment (sizes .K) (sizes .L))
  word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++
    3 :: (List.replicate width (data true) ++ 4 ::
      (word (List.ofFn (fun index : Fin width =>
        (encode field (sizes .K) (sizes .L) value.2.1).getLsbD index.val)) ++ right))

def headerValues (sizes : SizeAssignment Matrices.context) (value : Value field sizes) :
    MatrixColumnStep.HeaderField → ℕ
  | .candidate | .savedRow => value.2.2
  | .rowCount => sizes .K
  | .column => value.1
  | .columnCount => sizes .L

omit [Field field.Carrier] [DecidableEq field.Carrier] in
@[simp] theorem layout_values (sizes : SizeAssignment Matrices.context) (value : Value field sizes) :
    layout.map (headerValues field sizes value) = [value.2.2, sizes .K, value.1, sizes .L] := rfl

def frame (sizes : SizeAssignment Matrices.context) (value : Value field sizes)
    (scalar : field.Carrier) (right : List Symbol) : List Symbol :=
  UnaryMachine.fields (layout.map (headerValues field sizes value)) ++ suffix field sizes value scalar right

/-- Scratch is existential, and the caller suffix is preserved as environment. -/
def representation (sizes : SizeAssignment Matrices.context) (right : List Symbol)
    (value : Value field sizes) (tape : Turing.Tape Symbol) : Prop :=
  ∃ scalar, tape = (Tape.configuration () [] (frame field sizes value scalar right)).Tape

def guardedRepresentation (sizes : SizeAssignment Matrices.context) (right : List Symbol)
    (value : Value field sizes) (tape : Turing.Tape Symbol) : Prop :=
  ∃ scalar, tape = (Tape.configuration () []
    (data (condition field sizes value) :: frame field sizes value scalar right)).Tape

omit [Field field.Carrier] [DecidableEq field.Carrier] in
theorem guard_contract : Realization.Realizes (representation field) (guardedRepresentation field)
    (valid field) (fun _ initial final => final = initial) := by
  let bound : SizePolynomial Matrices.context :=
    SizePolynomial.constant 2 * SizePolynomial.parameter (ctx := Matrices.context) .L ^ 2 +
      SizePolynomial.constant 10 * SizePolynomial.parameter (ctx := Matrices.context) .L +
      SizePolynomial.constant 4 * SizePolynomial.parameter (ctx := Matrices.context) .K + SizePolynomial.constant 12
  refine ⟨HeaderGuardMachine.State columnPosition, inferInstance, inferInstance, (Fin.last columnPosition, false, 0),
    (0, false, 14), HeaderGuardMachine.machine columnPosition, bound, HeaderGuardMachine.halt, ?_⟩
  intro sizes right value initial bounded represented
  obtain ⟨scalar, rfl⟩ := represented
  have trace := HeaderGuardMachine.realizes_at columnPosition [value.2.2, sizes .K] (by rfl) value.1 (sizes .L)
    (suffix field sizes value scalar right) bounded.1
  refine ⟨value, (Tape.configuration () [] (data (condition field sizes value) :: frame field sizes value scalar right)).Tape,
    2 * value.1 ^ 2 + 10 * value.1 + 2 * (UnaryMachine.fields [value.2.2, sizes .K]).length + 8,
    ?_, ?_, rfl, ⟨scalar, rfl⟩⟩
  · have square := Nat.pow_le_pow_left bounded.1 2
    have rowBound := bounded.2
    simp [bound, valid, UnaryMachine.fields] at *
    nlinarith
  · simpa [frame, layout_values, headerValues, condition, UnaryMachine.fields, Tape.configuration, List.append_assoc] using trace

/-- One column step and counter increment, with existential scalar scratch. -/
theorem body_contract : Realization.Realizes (guardedRepresentation field) (representation field)
    (fun sizes value => valid field sizes value ∧ condition field sizes value = true)
    (fun sizes initial final => final = advance field sizes initial) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, stepMachine, stepBound, stepHalt, stepRuns⟩ :=
    MatrixColumnStep.realizes field
  let stepControllerFinite : Fintype Controller := finite
  let stepControllerInhabited : Inhabited Controller := inhabited
  let first := Tape.sequence HeaderGuardMachine.consume stepMachine entry
  let incrementer := HeaderIncrementMachine.machine columnPosition
  let incrementEntry : HeaderIncrementMachine.State columnPosition := .inl (Fin.last columnPosition)
  let bound := stepBound + SizePolynomial.constant 6 * SizePolynomial.parameter (ctx := Matrices.context) .K +
    SizePolynomial.constant 12
  refine ⟨Sum (Sum (Fin 3) Controller) (HeaderIncrementMachine.State columnPosition), inferInstance, inferInstance,
    .inl (.inl 0), .inr (.inr (0, 2)), Tape.sequence first incrementer incrementEntry, bound, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, incrementer, HeaderIncrementMachine.halt]
  · intro sizes right value initial validInput represented
    obtain ⟨scalar, rfl⟩ := represented
    have active : value.1 < sizes .L := by simpa only [condition, decide_eq_true_eq] using validInput.2
    have bounded := validInput.1.2
    have sizesEqual : assignment (sizes .K) (sizes .L) = sizes := by
      funext name; cases name <;> rfl
    obtain ⟨nextScalar, ticks, cost, trace, _, _, nextBound⟩ :=
      stepRuns (sizes .K) (sizes .L) value.2.1 value.2.2 bounded ⟨value.1, active⟩ scalar right
    let next : Value field sizes := (value.1, GaussJordan.columnStep value.2.1 value.2.2 ⟨value.1, active⟩)
    have trace' : Tape.Steps stepMachine ticks
        ⟨entry, (Tape.configuration () [] (frame field sizes value scalar right)).Tape⟩
        ⟨exit, (Tape.configuration () [] (frame field sizes next nextScalar right)).Tape⟩ := by
      simpa only [frame, layout_values, headerValues, suffix, next, Tape.configuration, List.append_assoc] using trace
    have consumed := HeaderGuardMachine.consumes true (frame field sizes value scalar right)
    have prepared := Tape.sequence_steps entry consumed HeaderGuardMachine.consume_halt trace'
    have incremented := HeaderIncrementMachine.realizes_at columnPosition [next.2.2, sizes .K] (by rfl) value.1
      (UnaryMachine.fields [sizes .L] ++ suffix field sizes next nextScalar right)
    have incremented' : Tape.Steps incrementer (3 * (next.2.2 + sizes .K + 2) + 2)
        ⟨incrementEntry, (Tape.configuration () [] (frame field sizes next nextScalar right)).Tape⟩
        ⟨.inr (0, 2), (Tape.configuration () [] (frame field sizes (advance field sizes value) nextScalar right)).Tape⟩ := by
      simpa [incrementer, incrementEntry, frame, layout_values, headerValues, next, advance, active, suffix, UnaryMachine.fields,
        Tape.configuration, List.append_assoc, Nat.add_assoc] using incremented
    have firstHalt (symbol : Symbol) : first (.inr exit) symbol = none := by
      simp [first, Tape.sequence, stepHalt]
    have complete := Tape.sequence_steps incrementEntry prepared firstHalt incremented'
    refine ⟨advance field sizes value,
      (Tape.configuration () [] (frame field sizes (advance field sizes value) nextScalar right)).Tape,
      2 + (ticks + 1) + (3 * (next.2.2 + sizes .K + 2) + 2 + 1), ?_, ?_, rfl, ⟨nextScalar, rfl⟩⟩
    · rw [sizesEqual] at cost
      change next.2.2 ≤ sizes .K at nextBound
      simp only [bound, SizePolynomial.eval_add, SizePolynomial.eval_mul,
        SizePolynomial.eval_constant, SizePolynomial.eval_parameter]
      omega
    · simpa only [first, condition, decide_eq_true active, Tape.configuration] using complete

omit [Field field.Carrier] [DecidableEq field.Carrier] in
/-- Consume a guard result without changing the mathematical state. -/
theorem consume_contract : Realization.Realizes (guardedRepresentation field) (representation field)
    (fun _ _ => True) (fun _ initial final => final = initial) := by
  refine ⟨Fin 3, inferInstance, inferInstance, 0, 2, HeaderGuardMachine.consume,
    SizePolynomial.constant 2, HeaderGuardMachine.consume_halt, ?_⟩
  intro sizes right value initial _ represented
  obtain ⟨scalar, rfl⟩ := represented
  refine ⟨value, _, 2, by simp, ?_, rfl, ⟨scalar, rfl⟩⟩
  exact HeaderGuardMachine.consumes _ _

omit [Field field.Carrier] [DecidableEq field.Carrier] in
private theorem guarded_head (sizes : SizeAssignment Matrices.context) (right : List Symbol)
    (value : Value field sizes) (tape : Turing.Tape Symbol)
    (represented : guardedRepresentation field sizes right value tape) :
    tape.head = data (condition field sizes value) := by
  obtain ⟨scalar, rfl⟩ := represented
  simp [condition, Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk]

/-- Column traversal exposes its mathematical fold and exit
condition. Its representation hides the temporary scalar at every iteration. -/
theorem traverse_contract : Realization.Realizes (representation field) (representation field)
    (valid field) (fun sizes initial final =>
      final = (advance field sizes)^[sizes .L - initial.1] initial ∧
        valid field sizes final ∧ condition field sizes final = false) := by
  have loop := Realization.Realizes.fold (representation field) (guardedRepresentation field)
    (SizeExpression.parameter .L) (fun _ value => value.1)
    (valid field) (advance field)
    (guard_contract field) (body_contract field)
    (guarded_head field)
    (by intro sizes value bounded; exact bounded.1)
    (by
      intro sizes value bounded active
      change value.1 < sizes .L at active
      have rowBound := (GaussJordan.columnStep_row_bound value.2.1 value.2.2 ⟨value.1, active⟩ bounded.2).2
      simp only [valid, advance, dite_eq_left active]
      exact ⟨by omega, rowBound⟩)
    (by
      intro sizes value _ active
      change value.1 < sizes .L at active
      simp only [advance, dite_eq_left active])
  exact (loop.sequence (consume_contract field) (by intros; trivial)).consequence
    (by intros; assumption) (by
      intro sizes initial final _ composed
      obtain ⟨middle, correct, equal⟩ := composed
      subst final
      have finalIndex : middle.1 = sizes .L := correct.2.2
      exact ⟨correct.1, correct.2.1, by simp [condition, finalIndex]⟩)

end ColumnContracts
end Polytime1.Examples.MatrixTraversal
