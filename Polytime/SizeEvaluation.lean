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

import Polytime.SizeMachine

/-! # Uniform polynomial-time tape evaluation of size expressions -/

namespace Polytime.SizeEvaluation

open UnaryMachine (Symbol units fields)
variable {ctx : SizeContext}

/-- A finite controller and a polynomial witness are chosen before any runtime
assignment. Unary fields are followed by an arbitrary preserved tape suffix. -/
def Realizes (input output : List (SizeExpression ctx)) : Prop :=
  ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
    let _controllerInhabited : Inhabited Controller := inhabited
    ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller) (bound : SizePolynomial ctx),
      (∀ symbol, machine exit symbol = none) ∧
      ∀ (assignment : SizeAssignment ctx) (tail : List Symbol),
        ∃ ticks, ticks ≤ bound.eval assignment ∧ Tape.Steps machine ticks
          (Tape.configuration entry [] (fields (input.map (·.eval assignment)) ++ tail))
          (Tape.configuration exit [] (fields (output.map (·.eval assignment)) ++ tail))

namespace Realizes

noncomputable section Certificates

variable {input middle output : List (SizeExpression ctx)}

theorem trans (first : Realizes input middle) (second : Realizes middle output) :
    Realizes input output := by
  obtain ⟨First, finiteFirst, inhabitedFirst, firstEntry, firstExit,
    firstMachine, firstBound, firstHalt, firstRun⟩ := first
  obtain ⟨Second, finiteSecond, inhabitedSecond, secondEntry, secondExit,
    secondMachine, secondBound, secondHalt, secondRun⟩ := second
  let firstFinite : Fintype First := finiteFirst
  let secondFinite : Fintype Second := finiteSecond
  let firstInhabited : Inhabited First := inhabitedFirst
  let secondInhabited : Inhabited Second := inhabitedSecond
  refine ⟨Sum First Second, inferInstance, inferInstance, .inl firstEntry, .inr secondExit,
    Tape.sequence firstMachine secondMachine secondEntry, firstBound + secondBound + 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, secondHalt]
  · intro assignment tail
    obtain ⟨firstTicks, firstCost, firstTrace⟩ := firstRun assignment tail
    obtain ⟨secondTicks, secondCost, secondTrace⟩ := secondRun assignment tail
    refine ⟨firstTicks + (secondTicks + 1), ?_, ?_⟩
    · simp; omega
    · exact Tape.sequence_steps secondEntry firstTrace firstHalt secondTrace

theorem output_congr (trace : Realizes input output) (other : List (SizeExpression ctx))
    (equality : ∀ assignment, output.map (·.eval assignment) = other.map (·.eval assignment)) :
    Realizes input other := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := trace
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment tail
  simpa only [← equality assignment] using runs assignment tail

theorem constant (value : ℕ) (input : List (SizeExpression ctx)) :
    Realizes input (.constant value :: input) := by
  refine ⟨SizeMachine.Constant.State value, inferInstance, 
    SizeMachine.Constant.instInhabitedState value, (Fin.last value, 0), (0, 4),
    SizeMachine.Constant.machine value, SizePolynomial.constant (2 * value + 3), ?_, ?_⟩
  · intro symbol; rfl
  · intro assignment tail
    exact ⟨2 * value + 3, by simp, by
      simpa [fields] using SizeMachine.Constant.realizes value
        (fields (input.map (·.eval assignment)) ++ tail)⟩

theorem copy (before after : List (SizeExpression ctx)) (expression : SizeExpression ctx) :
    Realizes (before ++ expression :: after) (expression :: before ++ expression :: after) := by
  refine ⟨SizeMachine.Copy.State before.length, inferInstance, 
    SizeMachine.Copy.instInhabitedState before.length, (Fin.last before.length, 0), (0, 19),
    SizeMachine.Copy.machine before.length,
    SizePolynomial.constant 64 *
      (((before ++ expression :: after).map SizeExpression.polynomial).sum +
        SizePolynomial.constant (before.length + after.length + 2)) ^ 2, ?_, ?_⟩
  · intro symbol; simp [SizeMachine.Copy.machine, UnaryMachine.machine]
  · intro assignment tail
    obtain ⟨ticks, cost, trace⟩ := SizeMachine.Copy.realizes
      (before.map (·.eval assignment)) (after.map (·.eval assignment)) (expression.eval assignment) tail
    rw [List.length_map] at trace
    refine ⟨ticks, ?_, ?_⟩
    · convert cost using 1
      simp [UnaryMachine.fields_length, SizeExpression.eval_eq, List.map_map, Function.comp_def]
      ring
    · simpa only [List.map_append, List.map_cons, List.length_map] using trace

theorem add (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left + right) :: rest) := by
  refine ⟨SizeMachine.Addition.State, inferInstance, SizeMachine.Addition.instInhabitedState, 0, 8,
    SizeMachine.Addition.machine, SizePolynomial.constant 2 * left.polynomial +
      SizePolynomial.constant 9, ?_, ?_⟩
  · intro symbol; rfl
  · intro assignment tail
    refine ⟨2 * left.eval assignment + 9, by simp [← SizeExpression.eval_eq], ?_⟩
    simpa only [List.map_cons, UnaryMachine.fields_cons, List.append_assoc, List.cons_append,
      SizeExpression.eval_add] using
      SizeMachine.Addition.realizes (left.eval assignment) (right.eval assignment)
        (fields (rest.map (·.eval assignment)) ++ tail)

theorem mul (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left * right) :: left :: right :: rest) := by
  refine ⟨UnaryMachine.State, inferInstance, UnaryMachine.instInhabitedState, 0, 19, UnaryMachine.machine false,
    SizePolynomial.constant 256 * (left.polynomial + right.polynomial + 1) ^ 5, ?_, ?_⟩
  · intro symbol; rfl
  · intro assignment tail
    obtain ⟨ticks, cost, trace⟩ := UnaryMachine.realizes false
      (left.eval assignment) (right.eval assignment) (fields (rest.map (·.eval assignment)) ++ tail)
    refine ⟨ticks, by simpa [← SizeExpression.eval_eq] using cost, ?_⟩
    simpa only [List.map_cons, UnaryMachine.fields_cons, List.append_assoc, List.cons_append,
      SizeExpression.eval_mul, Bool.toNat_false, Nat.add_zero, UnaryMachine.Steps,
      UnaryMachine.configuration] using trace

end Certificates
end Realizes

/-- Evaluation may retain intermediate counters before the original header.
Their number and expressions are fixed by the syntax, not by the assignment. -/
def Evaluates (expression : SizeExpression ctx) : Prop :=
  ∀ stack : List (SizeExpression ctx),
    (∀ name, SizeExpression.parameter name ∈ stack) →
    ∃ scratch : List (SizeExpression ctx), Realizes stack (expression :: scratch ++ stack)

noncomputable section ExpressionRealization

private theorem binary (left right result : SizeExpression ctx)
    (saved : List (SizeExpression ctx)) (leftEval : Evaluates left) (rightEval : Evaluates right)
    (operation : ∀ rest, Realizes (left :: right :: rest) (result :: saved ++ rest)) :
    Evaluates result := by
  intro stack contains
  obtain ⟨leftScratch, first⟩ := leftEval stack contains
  obtain ⟨rightScratch, second⟩ := rightEval (left :: leftScratch ++ stack)
    (by intro name; simp [contains name])
  have copy := Realizes.copy (right :: rightScratch) (leftScratch ++ stack) left
  have arithmetic := operation (rightScratch ++ left :: leftScratch ++ stack)
  refine ⟨saved ++ rightScratch ++ left :: leftScratch, ?_⟩
  simp only [List.cons_append, List.append_assoc] at first second copy arithmetic
  have trace := first.trans (second.trans (copy.trans arithmetic))
  simpa only [List.cons_append, List.append_assoc] using trace

/-- Every executable size expression has a fixed finite tape controller with
polynomially many actual transitions, uniformly over all size assignments. -/
theorem evaluates (expression : SizeExpression ctx) : Evaluates expression := by
  induction expression with
  | constant value =>
    intro stack _
    exact ⟨[], Realizes.constant value stack⟩
  | parameter name =>
    intro stack contains
    obtain ⟨before, after, equality⟩ := List.mem_iff_append.mp (contains name)
    refine ⟨[], ?_⟩
    simpa [equality] using Realizes.copy before after (.parameter name)
  | add left right leftEval rightEval =>
    exact binary left right (left + right) [] leftEval rightEval (Realizes.add left right)
  | mul left right leftEval rightEval =>
    exact binary left right (left * right) [left, right] leftEval rightEval (Realizes.mul left right)
  | pow base exponent baseEval =>
    induction exponent with
    | zero =>
      intro stack _
      refine ⟨[], (Realizes.constant 1 stack).output_congr (.pow base 0 :: stack) ?_⟩
      intro assignment
      simp [SizeExpression.eval]
    | succ exponent powerEval =>
      have combined := binary base (SizeExpression.pow base exponent) (SizeExpression.mul base (SizeExpression.pow base exponent))
        [base, SizeExpression.pow base exponent] baseEval powerEval (Realizes.mul (ctx := ctx) base (SizeExpression.pow base exponent))
      intro stack contains
      obtain ⟨scratch, trace⟩ := combined stack contains
      refine ⟨scratch, trace.output_congr (.pow base (exponent + 1) :: scratch ++ stack) ?_⟩
      intro assignment
      simp [SizeExpression.eval, pow_succ, Nat.mul_comm]

/-- The runtime header lists parameters in an explicitly chosen finite order.
The original header and arbitrary canonical input remain after the scratch. -/
theorem realizes_header (expression : SizeExpression ctx) (names : List ctx.Parameter)
    (complete : ∀ name, name ∈ names) :
    ∃ scratch, Realizes (names.map SizeExpression.parameter)
      (expression :: scratch ++ names.map SizeExpression.parameter) := by
  apply evaluates expression
  intro name
  exact List.mem_map.mpr ⟨name, complete name, rfl⟩

/-- These unary fields are exactly the existing serialized size header. -/
theorem fields_header (values : List ℕ) :
    fields values = TupleMachine.word (Frame.header values) := by
  induction values with
  | nil => rfl
  | cons value values hypothesis =>
    simpa [fields, Frame.header, TupleMachine.word, units, List.map_replicate,
      TupleMachine.data, List.map_append, List.append_assoc] using
      congrArg (fun suffix => units value ++ 1 :: suffix) hypothesis

/-- Tape realization on the framework's actual header format. Intermediate
fields precede the unchanged header and payload; all are polynomially bounded. -/
theorem realizes (expression : SizeExpression ctx) {count : ℕ}
    (ordering : ctx.Parameter ≃ Fin count) :
    ∃ (scratch : List (SizeExpression ctx)) (Controller : Type) (_finite : Fintype Controller)
      (inhabited : Inhabited Controller),
      let _controllerInhabited : Inhabited Controller := inhabited
      ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller)
        (bound : SizePolynomial ctx),
        (∀ symbol, machine exit symbol = none) ∧
        ∀ (assignment : SizeAssignment ctx) (tail : List Symbol),
          ∃ ticks, ticks ≤ bound.eval assignment ∧ Tape.Steps machine ticks
            (Tape.configuration entry [] (TupleMachine.word
              (Frame.header (Frame.values ordering assignment)) ++ tail))
            (Tape.configuration exit [] (units (expression.eval assignment) ++ 1 ::
              (fields (scratch.map (·.eval assignment)) ++ TupleMachine.word
                (Frame.header (Frame.values ordering assignment)) ++ tail))) := by
  let names := List.ofFn ordering.symm
  obtain ⟨scratch, Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    realizes_header expression names (by
      intro name
      exact List.mem_ofFn.mpr ⟨ordering name, ordering.symm_apply_apply name⟩)
  refine ⟨scratch, Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment tail
  have headerEquality : fields ((names.map SizeExpression.parameter).map (·.eval assignment)) =
      TupleMachine.word (Frame.header (Frame.values ordering assignment)) := by
    simp only [names, List.map_ofFn, Function.comp_def, SizeExpression.eval_parameter,
      Frame.values]
    exact fields_header _
  simpa only [List.map_cons, List.map_append, UnaryMachine.fields_cons,
    UnaryMachine.fields_append, List.append_assoc, List.cons_append, headerEquality] using runs assignment tail


end ExpressionRealization
end Polytime.SizeEvaluation
