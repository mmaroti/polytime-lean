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
import Polytime.Realization

/-! # Size-expression routines inside a fixed reserved frame

A capacity bounds the whole header and its blank margin. Both caller regions
are preserved. Capacity and polynomial witnesses stay inside the certificate.
-/

namespace Polytime.SizeFrame

open UnaryMachine (Symbol fields units)
variable {ctx : SizeContext}

/-- Storage occupied by a list of runtime unary fields. -/
noncomputable def headerWidth (expressions : List (SizeExpression ctx)) : SizePolynomial ctx :=
  (expressions.map SizeExpression.polynomial).sum + SizePolynomial.constant expressions.length

@[simp] theorem headerWidth_eval (expressions : List (SizeExpression ctx)) (assignment : SizeAssignment ctx) :
    (headerWidth expressions).eval assignment = (fields (expressions.map (·.eval assignment))).length := by
  simp [headerWidth, UnaryMachine.fields_length, SizePolynomial.eval_sum, List.map_map,
    Function.comp_def, ← SizeExpression.eval_eq]

/-- The capacity and protected left/right regions belong to the caller. -/
abbrev Caller (reserve : SizePolynomial ctx) (assignment : SizeAssignment ctx) :=
  {capacity : ℕ // reserve.eval assignment ≤ capacity} × (List Symbol × List Symbol)

/-- The same capacity is used before and after a call; only the header and
its complementary blank margin change. -/
def representation (expressions : List (SizeExpression ctx)) (reserve : SizePolynomial ctx)
    (assignment : SizeAssignment ctx) (caller : Caller reserve assignment) (_value : Unit)
    (actual : Turing.Tape Symbol) : Prop :=
  actual = (Tape.configuration ()
    (List.replicate (caller.1.val - (headerWidth expressions).eval assignment) 0 ++ caller.2.1)
    (fields (expressions.map (·.eval assignment)) ++ caller.2.2)).Tape

/-- One capacity polynomial suffices for all calls, with polynomial work
independent of excess reserved space. -/
def Realizes (input output : List (SizeExpression ctx)) : Prop :=
  ∃ reserve : SizePolynomial ctx,
    (∀ assignment, (headerWidth input).eval assignment ≤ reserve.eval assignment ∧
      (headerWidth output).eval assignment ≤ reserve.eval assignment) ∧
    Realization.Realizes (representation input reserve) (representation output reserve)
      (fun _ _ => True) (fun _ _ _ => True)

namespace Realizes

noncomputable section Composition

private theorem enlarge {input output : List (SizeExpression ctx)}
    {small large : SizePolynomial ctx} (bounded : ∀ assignment, small.eval assignment ≤ large.eval assignment)
    (realization : Realization.Realizes (representation input small) (representation output small)
      (fun _ _ => True) (fun _ _ _ => True)) :
    Realization.Realizes (representation input large) (representation output large)
      (fun _ _ => True) (fun _ _ _ => True) := by
  exact realization.adapt (fun _ value => value)
    (fun assignment caller _ => (⟨caller.1.val, (bounded assignment).trans caller.1.property⟩, caller.2))
    (fun _ _ value => value) (representation input large) (representation output large)
    (fun _ _ => True) (fun _ _ _ => True)
    (by intros; trivial) (by intros; assumption) (by intros; trivial) (by intros; assumption)

/-- Compose inside one capacity, hiding workspace growth and controller handoff. -/
theorem trans {input middle output : List (SizeExpression ctx)}
    (first : Realizes input middle) (second : Realizes middle output) : Realizes input output := by
  obtain ⟨firstReserve, firstFits, firstContract⟩ := first
  obtain ⟨secondReserve, secondFits, secondContract⟩ := second
  have firstBound : ∀ assignment, firstReserve.eval assignment ≤ (firstReserve + secondReserve).eval assignment := by
    intro assignment; simp only [SizePolynomial.eval_add]; omega
  have secondBound : ∀ assignment, secondReserve.eval assignment ≤ (firstReserve + secondReserve).eval assignment := by
    intro assignment; simp only [SizePolynomial.eval_add]; omega
  refine ⟨firstReserve + secondReserve, ?_, ?_⟩
  · intro assignment
    exact ⟨(firstFits assignment).1.trans (firstBound assignment),
      (secondFits assignment).2.trans (secondBound assignment)⟩
  · exact ((enlarge firstBound firstContract).sequence (enlarge secondBound secondContract)
      (by intros; trivial)).consequence (by intros; trivial) (by intros; trivial)

/-- Equal mathematical field values allow a different expression description. -/
theorem output_congr {input output : List (SizeExpression ctx)} (certificate : Realizes input output)
    (other : List (SizeExpression ctx))
    (equality : ∀ assignment, output.map (·.eval assignment) = other.map (·.eval assignment)) :
    Realizes input other := by
  obtain ⟨reserve, fits, realization⟩ := certificate
  have widths (assignment : SizeAssignment ctx) :
      (headerWidth output).eval assignment = (headerWidth other).eval assignment := by
    simp only [headerWidth_eval, equality assignment]
  have descriptions : representation output reserve = representation other reserve := by
    funext assignment caller value actual
    dsimp only [representation]
    rw [widths, equality]
  refine ⟨reserve, ?_, ?_⟩
  · intro assignment
    exact ⟨(fits assignment).1, (widths assignment) ▸ (fits assignment).2⟩
  · rw [descriptions] at realization
    exact realization

end Composition

noncomputable section Primitives

/-- Shared allocation rule for a constant, copied field, or computed product. -/
private theorem prepend (input : List (SizeExpression ctx)) (expression : SizeExpression ctx) (spare : ℕ)
    {Controller : Type} [Fintype Controller] [Inhabited Controller]
    (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller) (bound : SizePolynomial ctx)
    (halt : ∀ symbol, machine exit symbol = none)
    (runs : ∀ assignment caller tail,
      ∃ ticks, ticks ≤ bound.eval assignment ∧ Tape.Steps machine ticks
        (Tape.configuration entry
          (List.replicate (expression.eval assignment + 1 + spare) 0 ++ caller)
          (fields (input.map (·.eval assignment)) ++ tail))
        (Tape.configuration exit (List.replicate spare 0 ++ caller)
          (fields ((expression :: input).map (·.eval assignment)) ++ tail))) :
    Realizes input (expression :: input) := by
  let output := expression :: input
  let reserve := headerWidth input + expression.polynomial + SizePolynomial.constant (1 + spare)
  have outputWidth (assignment : SizeAssignment ctx) :
      (headerWidth output).eval assignment = expression.eval assignment + 1 + (headerWidth input).eval assignment := by
    simp [output, UnaryMachine.fields_cons]
    omega
  have reserveWidth (assignment : SizeAssignment ctx) :
      reserve.eval assignment = (headerWidth input).eval assignment + expression.eval assignment + (1 + spare) := by
    simp only [reserve, SizePolynomial.eval_add, SizePolynomial.eval_constant, ← SizeExpression.eval_eq]
  refine ⟨reserve, ?_, Controller, inferInstance, inferInstance, entry, exit, machine, bound, halt, ?_⟩
  · intro assignment
    rw [reserveWidth, outputWidth]
    omega
  · intro assignment caller initialValue initial _ represented
    change initial = _ at represented
    subst initial
    let margin := caller.1.val - (headerWidth output).eval assignment - spare
    have enough : (headerWidth input).eval assignment + expression.eval assignment + (1 + spare) ≤ caller.1.val := by
      simpa only [reserveWidth] using caller.1.property
    have initialMargin : caller.1.val - (headerWidth input).eval assignment =
        expression.eval assignment + 1 + spare + margin := by
      dsimp only [margin]; rw [outputWidth]; omega
    have finalMargin : caller.1.val - (headerWidth output).eval assignment = spare + margin := by
      dsimp only [margin]; rw [outputWidth]; omega
    have physicalInput : List.replicate (expression.eval assignment + 1 + spare) (0 : Symbol) ++
        (List.replicate margin 0 ++ caller.2.1) =
        List.replicate (caller.1.val - (headerWidth input).eval assignment) 0 ++ caller.2.1 := by
      rw [← List.append_assoc, ← List.replicate_add, ← initialMargin]
    have physicalOutput : List.replicate spare (0 : Symbol) ++ (List.replicate margin 0 ++ caller.2.1) =
        List.replicate (caller.1.val - (headerWidth output).eval assignment) 0 ++ caller.2.1 := by
      rw [← List.append_assoc, ← List.replicate_add, ← finalMargin]
    obtain ⟨ticks, cost, trace⟩ := runs assignment (List.replicate margin 0 ++ caller.2.1) caller.2.2
    rw [physicalInput, physicalOutput] at trace
    refine ⟨(), (Tape.configuration ()
      (List.replicate (caller.1.val - (headerWidth output).eval assignment) 0 ++ caller.2.1)
      (fields (output.map (·.eval assignment)) ++ caller.2.2)).Tape,
      ticks, cost, ?_, trivial, rfl⟩
    exact trace

/-- Allocate a fixed constant in the shared capacity without exposing its margin. -/
theorem constant (value : ℕ) (input : List (SizeExpression ctx)) :
    Realizes input (.constant value :: input) := by
  apply prepend input (.constant value) 0 (Fin.last value, 0) (0, 4)
    (SizeMachine.Constant.machine value) (SizePolynomial.constant (2 * value + 3)) (by intros; rfl)
  intro assignment caller tail
  refine ⟨2 * value + 3, by simp, ?_⟩
  simpa [UnaryMachine.fields_cons, SizeExpression.eval, List.append_assoc] using
    SizeMachine.Constant.realizes_reserved value caller (fields (input.map (·.eval assignment)) ++ tail)

/-- Copy a selected field while capacity accounting remains inside the library. -/
theorem copy (before after : List (SizeExpression ctx)) (expression : SizeExpression ctx) :
    Realizes (before ++ expression :: after) (expression :: before ++ expression :: after) := by
  apply prepend (before ++ expression :: after) expression 1 (Fin.last before.length, 0) (0, 19)
    (SizeMachine.Copy.machine before.length)
    (SizePolynomial.constant 64 * (headerWidth (before ++ expression :: after) + 1) ^ 2)
    (by intro symbol; simp [SizeMachine.Copy.machine, UnaryMachine.machine])
  intro assignment caller tail
  obtain ⟨ticks, cost, trace⟩ := SizeMachine.Copy.realizes_reserved
    (before.map (·.eval assignment)) (after.map (·.eval assignment)) (expression.eval assignment) caller tail
  rw [List.length_map] at trace
  refine ⟨ticks, ?_, ?_⟩
  · simpa only [SizePolynomial.eval_mul, SizePolynomial.eval_constant, SizePolynomial.eval_pow,
      SizePolynomial.eval_add, SizePolynomial.eval_one, headerWidth_eval, List.map_append, List.map_cons] using cost
  · simpa only [List.map_append, List.map_cons, List.replicate_one, List.singleton_append,
      List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using trace

/-- Compute a product in the same capacity while retaining both operands. -/
theorem mul (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left * right) :: left :: right :: rest) := by
  apply prepend (left :: right :: rest) (left * right) 1 0 19 (UnaryMachine.machine false)
    (SizePolynomial.constant 256 * (left.polynomial + right.polynomial + 1) ^ 5) (by intros; rfl)
  intro assignment caller tail
  obtain ⟨ticks, cost, trace⟩ := UnaryMachine.realizes_reserved false
    (left.eval assignment) (right.eval assignment) caller (fields (rest.map (·.eval assignment)) ++ tail)
  refine ⟨ticks, by simpa [← SizeExpression.eval_eq] using cost, ?_⟩
  simpa only [List.map_cons, UnaryMachine.fields_cons, List.append_assoc, List.cons_append,
    SizeExpression.eval_mul, Bool.toNat_false, Nat.add_zero, List.replicate_one, List.singleton_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd, UnaryMachine.Steps, UnaryMachine.configuration] using trace

/-- Addition returns its freed separator cell to the shared blank margin. -/
theorem add (left right : SizeExpression ctx) (rest : List (SizeExpression ctx)) :
    Realizes (left :: right :: rest) ((left + right) :: rest) := by
  let input := left :: right :: rest
  let output := (left + right) :: rest
  let reserve := headerWidth input + 1
  have widthEq (assignment : SizeAssignment ctx) :
      (headerWidth input).eval assignment = (headerWidth output).eval assignment + 1 := by
    simp [input, output, UnaryMachine.fields_cons, SizeExpression.eval_add]
    omega
  refine ⟨reserve, ?_, ?_⟩
  · intro assignment
    change (headerWidth input).eval assignment ≤ reserve.eval assignment ∧
      (headerWidth output).eval assignment ≤ reserve.eval assignment
    simp only [reserve, SizePolynomial.eval_add, SizePolynomial.eval_one]
    have widths := widthEq assignment
    omega
  · refine ⟨SizeMachine.Addition.State, inferInstance, inferInstance, 0, 8,
      SizeMachine.Addition.machine, SizePolynomial.constant 2 * left.polynomial + SizePolynomial.constant 9,
      by intros; rfl, ?_⟩
    intro assignment caller initialValue initial _ represented
    change initial = _ at represented
    subst initial
    let remainder := caller.1.val - (headerWidth input).eval assignment - 1
    have enough : (headerWidth input).eval assignment + 1 ≤ caller.1.val := by
      simpa only [reserve, SizePolynomial.eval_add, SizePolynomial.eval_one] using caller.1.property
    have initialMargin : caller.1.val - (headerWidth input).eval assignment = remainder + 1 := by
      dsimp only [remainder]; omega
    have finalMargin : caller.1.val - (headerWidth output).eval assignment = remainder + 2 := by
      have widths := widthEq assignment
      dsimp only [remainder]; omega
    have physicalInput : 0 :: (List.replicate remainder (0 : Symbol) ++ caller.2.1) =
        List.replicate (caller.1.val - (headerWidth input).eval assignment) 0 ++ caller.2.1 := by
      rw [initialMargin, List.replicate_succ]; rfl
    have physicalOutput : 0 :: 0 :: (List.replicate remainder (0 : Symbol) ++ caller.2.1) =
        List.replicate (caller.1.val - (headerWidth output).eval assignment) 0 ++ caller.2.1 := by
      rw [finalMargin, List.replicate_succ, List.replicate_succ]; rfl
    have trace := SizeMachine.Addition.realizes_reserved (left.eval assignment) (right.eval assignment)
      (List.replicate remainder 0 ++ caller.2.1) (fields (rest.map (·.eval assignment)) ++ caller.2.2)
    rw [physicalOutput, physicalInput] at trace
    refine ⟨(), (Tape.configuration ()
      (List.replicate (caller.1.val - (headerWidth output).eval assignment) 0 ++ caller.2.1)
      (fields (output.map (·.eval assignment)) ++ caller.2.2)).Tape,
      2 * left.eval assignment + 9, by simp [← SizeExpression.eval_eq], ?_, trivial, rfl⟩
    simpa [input, output, UnaryMachine.fields_cons, SizeExpression.eval_add,
      Tape.configuration, List.append_assoc] using trace

/-- Allocate two operands and add them in one capacity, preserving both callers. -/
example (rest : List (SizeExpression ctx)) :
    Realizes rest ((SizeExpression.constant 2 + SizeExpression.constant 1) :: rest) :=
  ((constant 1 rest).trans (constant 2 (.constant 1 :: rest))).trans
    (add (.constant 2) (.constant 1) rest)

end Primitives
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

end ExpressionRealization
end Polytime.SizeFrame
