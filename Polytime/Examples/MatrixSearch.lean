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

import Polytime.RealizationLoop
import Polytime.GaussJordan
import Polytime.HeaderIncrementMachine
import Polytime.Examples.MatrixPivotGuard

/-! # Pivot search through mathematical contracts

The candidate, selected column, and immutable matrix are mathematical state.
The scalar refreshed by the guard is existential scratch, never loop state.
-/

namespace Polytime.Examples.MatrixSearch

open Matrices TupleMachine

-- scalarLevel: the specialized finite field carrier.
universe scalarLevel

abbrev Value (field : FixedPresentation.{scalarLevel}) (sizes : SizeAssignment context) :=
  ℕ × (Fin (sizes .L) × Matrix (Fin (sizes .K)) (Fin (sizes .L)) field.Carrier)

noncomputable section SearchContracts

variable (field : FixedPresentation.{scalarLevel}) [Field field.Carrier] [DecidableEq field.Carrier]

abbrev Environment (extraCount : ℕ) (extraBound : SizePolynomial context) (sizes : SizeAssignment context) :=
  {extra : List ℕ // extra.length = extraCount ∧ (UnaryMachine.fields extra).length ≤ extraBound.eval sizes} × List Symbol

def condition (sizes : SizeAssignment context) (value : Value field sizes) : Bool :=
  if active : value.1 < sizes .K then decide (value.2.2 ⟨value.1, active⟩ value.2.1 = 0) else false

def advance (sizes : SizeAssignment context) (value : Value field sizes) : Value field sizes :=
  (value.1 + 1, value.2)

def frame (sizes : SizeAssignment context) (extra : List ℕ) (right : List Symbol)
    (value : Value field sizes) (scalar : field.Carrier) : List Symbol :=
  let width := (domain field).bitWidth (assignment (sizes .K) (sizes .L))
  UnaryMachine.fields ([value.1, sizes .K, value.2.1.val, sizes .L] ++ extra) ++
    word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
      (List.replicate width (data true) ++ 4 ::
        (word (List.ofFn (fun index : Fin width =>
          (encode field (sizes .K) (sizes .L) value.2.2).getLsbD index.val)) ++ right))

def representation (extraCount : ℕ) (extraBound : SizePolynomial context)
    (sizes : SizeAssignment context) (caller : Environment extraCount extraBound sizes)
    (value : Value field sizes) (tape : Turing.Tape Symbol) : Prop :=
  ∃ scalar, tape = (Tape.configuration () [] (frame field sizes caller.1.val caller.2 value scalar)).Tape

def guardedRepresentation (extraCount : ℕ) (extraBound : SizePolynomial context)
    (sizes : SizeAssignment context) (caller : Environment extraCount extraBound sizes)
    (value : Value field sizes) (tape : Turing.Tape Symbol) : Prop :=
  ∃ scalar, tape = (Tape.configuration () []
    (data (condition field sizes value) :: frame field sizes caller.1.val caller.2 value scalar)).Tape

/-- Refreshing the scalar changes no mathematical state. -/
theorem guard_contract (extraCount : ℕ) (extraBound : SizePolynomial context) :
    Realization.Realizes (representation field extraCount extraBound) (guardedRepresentation field extraCount extraBound)
      (fun sizes value => value.1 ≤ sizes .K) (fun _ initial final => final = initial) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    MatrixPivotGuard.realizes_with_counters field extraCount extraBound
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro sizes caller value initial bounded represented
  obtain ⟨scalar, rfl⟩ := represented
  have sizesEqual : assignment (sizes .K) (sizes .L) = sizes := by
    funext name; cases name <;> rfl
  obtain ⟨ticks, cost, trace⟩ := runs (sizes .K) (sizes .L) value.2.2 value.1 bounded value.2.1
    caller.1.val caller.1.property.1 (by simpa only [sizesEqual] using caller.1.property.2) scalar caller.2
  rw [sizesEqual] at cost
  let finalScalar := if active : value.1 < sizes .K then value.2.2 ⟨value.1, active⟩ value.2.1 else scalar
  refine ⟨value, (Tape.configuration () []
    (data (condition field sizes value) :: frame field sizes caller.1.val caller.2 value finalScalar)).Tape,
    ticks, cost, ?_, rfl, ⟨finalScalar, rfl⟩⟩
  simpa only [condition, frame, finalScalar, Tape.configuration] using trace

/-- Increment only a candidate known to be eligible and zero. -/
theorem body_contract (extraCount : ℕ) (extraBound : SizePolynomial context) :
    Realization.Realizes (guardedRepresentation field extraCount extraBound) (representation field extraCount extraBound)
      (fun sizes value => value.1 ≤ sizes .K ∧ condition field sizes value = true)
      (fun sizes initial final => final = advance field sizes initial ∧ condition field sizes initial = true) := by
  let incrementer := HeaderIncrementMachine.machine 0
  let entry : HeaderIncrementMachine.State 0 := .inl (Fin.last 0)
  let machine := Tape.sequence HeaderGuardMachine.consume incrementer entry
  refine ⟨Sum (Fin 3) (HeaderIncrementMachine.State 0), inferInstance, inferInstance,
    .inl 0, .inr (.inr (0, 2)), machine, SizePolynomial.constant 5, ?_, ?_⟩
  · intro symbol; simp [machine, incrementer, Tape.sequence, HeaderIncrementMachine.halt]
  · intro sizes caller value initial valid represented
    obtain ⟨scalar, rfl⟩ := represented
    have consumed := HeaderGuardMachine.consumes true (frame field sizes caller.1.val caller.2 value scalar)
    have incremented := HeaderIncrementMachine.realizes [] value.1
      (UnaryMachine.fields ([sizes .K, value.2.1.val, sizes .L] ++ caller.1.val) ++
        word (List.ofFn (BoolTuple.fromBits (field.codec.encode scalar))) ++ 3 ::
          (List.replicate ((domain field).bitWidth (assignment (sizes .K) (sizes .L))) (data true) ++ 4 ::
            (word (List.ofFn (fun index : Fin ((domain field).bitWidth (assignment (sizes .K) (sizes .L))) =>
              (encode field (sizes .K) (sizes .L) value.2.2).getLsbD index.val)) ++ caller.2)))
    have incremented' : Tape.Steps incrementer 2
        ⟨entry, (Tape.configuration () [] (frame field sizes caller.1.val caller.2 value scalar)).Tape⟩
        ⟨.inr (0, 2), (Tape.configuration () []
          (frame field sizes caller.1.val caller.2 (advance field sizes value) scalar)).Tape⟩ := by
      simpa [incrementer, entry, frame, advance, UnaryMachine.fields, Tape.configuration, List.append_assoc] using incremented
    have trace := Tape.sequence_steps entry consumed HeaderGuardMachine.consume_halt incremented'
    refine ⟨advance field sizes value, (Tape.configuration () []
      (frame field sizes caller.1.val caller.2 (advance field sizes value) scalar)).Tape,
      5, by simp, ?_, ⟨rfl, valid.2⟩, ⟨scalar, rfl⟩⟩
    simpa only [machine, valid.2, Tape.configuration] using trace

theorem consume_contract (extraCount : ℕ) (extraBound : SizePolynomial context) :
    Realization.Realizes (guardedRepresentation field extraCount extraBound) (representation field extraCount extraBound)
      (fun _ _ => True) (fun _ initial final => final = initial) := by
  refine ⟨Fin 3, inferInstance, inferInstance, 0, 2, HeaderGuardMachine.consume,
    SizePolynomial.constant 2, HeaderGuardMachine.consume_halt, ?_⟩
  intro sizes caller value initial _ represented
  obtain ⟨scalar, rfl⟩ := represented
  refine ⟨value, (Tape.configuration () [] (frame field sizes caller.1.val caller.2 value scalar)).Tape,
    2, by simp, ?_, rfl, ⟨scalar, rfl⟩⟩
  exact HeaderGuardMachine.consumes _ _

/-- The shared search rule supplies termination and all tape cost bookkeeping. -/
theorem search_contract (extraCount : ℕ) (extraBound : SizePolynomial context) :
    Realization.Realizes (representation field extraCount extraBound) (representation field extraCount extraBound)
      (fun sizes value => value.1 ≤ sizes .K)
      (fun sizes initial final =>
        Relation.ReflTransGen (fun before after =>
          after = advance field sizes before ∧ condition field sizes before = true) initial final ∧
        final.1 ≤ sizes .K ∧ condition field sizes final = false) := by
  have loop := Realization.Realizes.search (representation field extraCount extraBound)
    (guardedRepresentation field extraCount extraBound) (SizeExpression.parameter .K)
    (fun _ value => value.1) (condition field) (fun sizes value => value.1 ≤ sizes .K)
    (fun sizes before after => after = advance field sizes before ∧ condition field sizes before = true)
    (guard_contract field extraCount extraBound) (body_contract field extraCount extraBound)
    (by
      intro sizes caller value tape represented
      obtain ⟨scalar, rfl⟩ := represented
      simp [Tape.configuration, Turing.Tape.mk', Turing.ListBlank.head_mk])
    (by
      intro sizes value _ active
      change value.1 < sizes .K
      by_contra inactive
      simp [condition, inactive] at active)
    (by
      intro sizes before after _ active step
      rw [step.1]
      have eligible : before.1 < sizes .K := by
        by_contra inactive
        simp [condition, inactive] at active
      change before.1 + 1 ≤ sizes .K
      omega)
    (by intro sizes before after _ _ step; rw [step.1]; rfl)
  exact (loop.sequence (consume_contract field extraCount extraBound) (by intros; trivial)).consequence
    (by intros; assumption) (by
      intro sizes initial final _ composed
      obtain ⟨middle, correct, equal⟩ := composed
      subst final
      exact correct)

/-- First eligible nonzero row, or the row-count sentinel. The proof is purely
mathematical: reachability preserves the skipped-zero invariant. -/
theorem contract (extraCount : ℕ) (extraBound : SizePolynomial context) :
    Realization.Realizes (representation field extraCount extraBound) (representation field extraCount extraBound)
      (fun sizes value => value.1 ≤ sizes .K)
      (fun sizes initial final => final.2 = initial.2 ∧ initial.1 ≤ final.1 ∧ final.1 ≤ sizes .K ∧
        (∀ row : Fin (sizes .K), initial.1 ≤ row.val → row.val < final.1 → initial.2.2 row initial.2.1 = 0) ∧
        (∀ active : final.1 < sizes .K, initial.2.2 ⟨final.1, active⟩ initial.2.1 ≠ 0) ∧
        GaussJordan.findPivot initial.2.2 initial.1 initial.2.1 =
          (if active : final.1 < sizes .K then some ⟨final.1, active⟩ else none)) := by
  apply (search_contract field extraCount extraBound).consequence (by intros; assumption)
  intro sizes initial final _ finished
  obtain ⟨reached, upper, stopped⟩ := finished
  have evidence : ∀ before after : Value field sizes,
      Relation.ReflTransGen (fun previous next =>
        next = advance field sizes previous ∧ condition field sizes previous = true) before after →
      after.2 = before.2 ∧ before.1 ≤ after.1 ∧
        ∀ row : Fin (sizes .K), before.1 ≤ row.val → row.val < after.1 → before.2.2 row before.2.1 = 0 := by
    intro before after reached
    induction reached with
    | refl => exact ⟨rfl, le_rfl, by intros; omega⟩
    | @tail middle after _ step hypothesis =>
      rcases step with ⟨rfl, active⟩
      have eligible : middle.1 < sizes .K := by
        by_contra inactive
        simp [condition, inactive] at active
      have zero : middle.2.2 ⟨middle.1, eligible⟩ middle.2.1 = 0 := by
        simpa only [condition, dite_eq_left eligible, decide_eq_true_eq] using active
      refine ⟨hypothesis.1, by change before.1 ≤ middle.1 + 1; omega, ?_⟩
      intro row lower earlier
      by_cases previous : row.val < middle.1
      · exact hypothesis.2.2 row lower previous
      · have rowEqual : row = (⟨middle.1, eligible⟩ : Fin (sizes .K)) := by
          apply Fin.ext
          change row.val = middle.1
          change row.val < middle.1 + 1 at earlier
          omega
        rw [hypothesis.1] at zero
        simpa only [rowEqual] using zero
  obtain ⟨unchanged, lower, skipped⟩ := evidence initial final reached
  have nonzero : ∀ active : final.1 < sizes .K,
      initial.2.2 ⟨final.1, active⟩ initial.2.1 ≠ 0 := by
    intro active
    rw [condition, dite_eq_left active] at stopped
    rw [unchanged] at stopped
    exact of_decide_eq_false stopped
  exact ⟨unchanged, lower, upper, skipped, nonzero,
    GaussJordan.findPivot_eq_of_minimal initial.2.2 initial.1 final.1 initial.2.1 lower upper skipped nonzero⟩

end SearchContracts
end Polytime.Examples.MatrixSearch
