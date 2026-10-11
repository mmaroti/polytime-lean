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

import Polytime1.SizeMachine
import Polytime1.Realization
import Polytime1.SizeFrame

/-! # Uniform polynomial-time tape evaluation of size expressions -/

namespace Polytime1.SizeEvaluation

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

/-- A finite reserved frame also runs with the original blank-left convention. -/
theorem of_frame (certificate : SizeFrame.Realizes input output) : Realizes input output := by
  obtain ⟨reserve, _fits, Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := certificate
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment tail
  let caller : SizeFrame.Caller reserve assignment := (⟨reserve.eval assignment, le_rfl⟩, [], tail)
  obtain ⟨result, final, ticks, cost, trace, _, represented⟩ :=
    runs assignment caller () _ trivial rfl
  change final = (Tape.configuration ()
    (List.replicate (caller.1.val - (SizeFrame.headerWidth output).eval assignment) 0 ++ caller.2.1)
    (fields (output.map (·.eval assignment)) ++ caller.2.2)).Tape at represented
  rw [represented] at trace
  dsimp only [caller] at trace
  simp only [List.append_nil] at trace
  change Tape.Steps machine ticks
    (Tape.configuration entry
      (List.replicate (reserve.eval assignment - (SizeFrame.headerWidth input).eval assignment) default)
      (fields (input.map (·.eval assignment)) ++ tail))
    (Tape.configuration exit
      (List.replicate (reserve.eval assignment - (SizeFrame.headerWidth output).eval assignment) default)
      (fields (output.map (·.eval assignment)) ++ tail)) at trace
  exact ⟨ticks, cost, by simpa only [Tape.configuration_replicate_blank] using trace⟩

/-- Size-expression routines retain their caller suffix as shared context. -/
def representation (expressions : List (SizeExpression ctx)) (assignment : SizeAssignment ctx)
    (tail : List Symbol) (_value : Unit) (tape : Turing.Tape Symbol) : Prop :=
  tape = (Tape.configuration () [] (fields (expressions.map (·.eval assignment)) ++ tail)).Tape

/-- The original certificate is exactly a mathematical contract with no
logical result beyond the statically declared expression list. -/
theorem contract_iff (input output : List (SizeExpression ctx)) :
    Realizes input output ↔ Realization.Realizes (representation input) (representation output)
      (fun _ _ => True) (fun _ _ _ => True) := by
  constructor
  · intro certificate
    obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := certificate
    refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
    intro assignment tail value initial _ represented
    obtain ⟨ticks, cost, trace⟩ := runs assignment tail
    refine ⟨(), _, ticks, cost, ?_, trivial, rfl⟩
    change initial = _ at represented
    subst initial
    exact trace
  · intro certificate
    obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := certificate
    refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
    intro assignment tail
    obtain ⟨outputValue, final, ticks, cost, trace, _, represented⟩ :=
      runs assignment tail () _ trivial rfl
    refine ⟨ticks, cost, ?_⟩
    change final = _ at represented
    rw [represented] at trace
    exact trace

theorem trans (first : Realizes input middle) (second : Realizes middle output) :
    Realizes input output := by
  apply (contract_iff input output).mpr
  exact ((contract_iff input middle).mp first |>.sequence ((contract_iff middle output).mp second)
    (by intros; trivial)).consequence (by intros; trivial) (by intros; trivial)

theorem output_congr (trace : Realizes input output) (other : List (SizeExpression ctx))
    (equality : ∀ assignment, output.map (·.eval assignment) = other.map (·.eval assignment)) :
    Realizes input other := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := trace
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment tail
  simpa only [← equality assignment] using runs assignment tail

theorem constant (value : ℕ) (input : List (SizeExpression ctx)) :
    Realizes input (.constant value :: input) :=
  of_frame (SizeFrame.Realizes.constant value input)

theorem copy (before after : List (SizeExpression ctx)) (expression : SizeExpression ctx) :
    Realizes (before ++ expression :: after) (expression :: before ++ expression :: after) :=
  of_frame (SizeFrame.Realizes.copy before after expression)

theorem add (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left + right) :: rest) :=
  of_frame (SizeFrame.Realizes.add left right rest)

theorem mul (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left * right) :: left :: right :: rest) :=
  of_frame (SizeFrame.Realizes.mul left right rest)

end Certificates
end Realizes

/-- Evaluation may retain intermediate counters before the original header.
Their number and expressions are fixed by the syntax, not by the assignment. -/
def Evaluates (expression : SizeExpression ctx) : Prop :=
  ∀ stack : List (SizeExpression ctx),
    (∀ name, SizeExpression.parameter name ∈ stack) →
    ∃ scratch : List (SizeExpression ctx), Realizes stack (expression :: scratch ++ stack)

noncomputable section ExpressionRealization

/-- The reserved-frame evaluator also realizes the original blank-left interface. -/
theorem evaluates (expression : SizeExpression ctx) : Evaluates expression := by
  intro stack contains
  obtain ⟨scratch, certificate⟩ := SizeFrame.evaluates expression stack contains
  exact ⟨scratch, Realizes.of_frame certificate⟩

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
end Polytime1.SizeEvaluation
