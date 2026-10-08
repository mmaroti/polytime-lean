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

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! # Size parameters

A context names finitely many parameters. Every name has the same role, and
an assignment gives each name an arbitrary natural value.
-/

namespace Polytime

structure SizeContext where
  Parameter : Type
  finiteParameters : Fintype Parameter

attribute [instance] SizeContext.finiteParameters

abbrev SizeAssignment (ctx : SizeContext) := ctx.Parameter → ℕ
/-- Mathematical polynomial witnesses, separate from executable capacities. -/
abbrev SizePolynomial (ctx : SizeContext) := MvPolynomial ctx.Parameter ℕ

namespace SizePolynomial

variable {ctx : SizeContext}

noncomputable section SizePolynomialDefinitions

def parameter (k : ctx.Parameter) : SizePolynomial ctx := MvPolynomial.X k
def constant (n : ℕ) : SizePolynomial ctx := MvPolynomial.C n

def eval (e : SizePolynomial ctx) (a : SizeAssignment ctx) : ℕ :=
  MvPolynomial.eval a e

@[simp] theorem eval_parameter (k : ctx.Parameter) (a : SizeAssignment ctx) :
    eval (parameter k) a = a k := by
  simp [eval, parameter]

@[simp] theorem eval_constant (n : ℕ) (a : SizeAssignment ctx) : eval (constant n) a = n := by
  simp [eval, constant]

@[simp] theorem eval_zero (a : SizeAssignment ctx) : eval (0 : SizePolynomial ctx) a = 0 := by
  simp [eval]

@[simp] theorem eval_one (a : SizeAssignment ctx) : eval (1 : SizePolynomial ctx) a = 1 := by
  simp [eval]

@[simp] theorem eval_add (e f : SizePolynomial ctx) (a : SizeAssignment ctx) :
    eval (e + f) a = eval e a + eval f a := by simp [eval]

@[simp] theorem eval_mul (e f : SizePolynomial ctx) (a : SizeAssignment ctx) :
    eval (e * f) a = eval e a * eval f a := by simp [eval]

@[simp] theorem eval_pow (e : SizePolynomial ctx) (n : ℕ) (a : SizeAssignment ctx) :
    eval (e ^ n) a = eval e a ^ n := by simp [eval]

@[simp] theorem eval_sum (expressions : List (SizePolynomial ctx)) (assignment : SizeAssignment ctx) :
    expressions.sum.eval assignment = (expressions.map fun expression => expression.eval assignment).sum := by
  induction expressions with
  | nil => simp
  | cons expression expressions hypothesis => simp [hypothesis]

/-- Natural-coefficient size expressions are monotone in every parameter. -/
theorem eval_mono (e : SizePolynomial ctx) (a b : SizeAssignment ctx) (h : ∀ k, a k ≤ b k) :
    e.eval a ≤ e.eval b := by
  induction e using MvPolynomial.induction_on with
  | C n => simp [eval]
  | add e f he hf => simpa using Nat.add_le_add he hf
  | mul_X e k he => simpa [eval] using Nat.mul_le_mul he (h k)

end SizePolynomialDefinitions
end SizePolynomial

/-- Executable natural-coefficient expressions used to declare capacities. -/
inductive SizeExpression (ctx : SizeContext)
  | constant (value : ℕ)
  | parameter (name : ctx.Parameter)
  | add (left right : SizeExpression ctx)
  | mul (left right : SizeExpression ctx)
  | pow (base : SizeExpression ctx) (exponent : ℕ)

namespace SizeExpression

variable {ctx : SizeContext}

instance : Add (SizeExpression ctx) := ⟨add⟩
instance : Mul (SizeExpression ctx) := ⟨mul⟩
instance : Pow (SizeExpression ctx) ℕ := ⟨pow⟩
instance (value : ℕ) : OfNat (SizeExpression ctx) value := ⟨constant value⟩

def eval : SizeExpression ctx → SizeAssignment ctx → ℕ
  | .constant value, _ => value
  | .parameter name, assignment => assignment name
  | .add left right, assignment => left.eval assignment + right.eval assignment
  | .mul left right, assignment => left.eval assignment * right.eval assignment
  | .pow base exponent, assignment => base.eval assignment ^ exponent

@[simp] theorem eval_constant (value : ℕ) (assignment : SizeAssignment ctx) :
    (constant value).eval assignment = value := rfl
@[simp] theorem eval_parameter (name : ctx.Parameter) (assignment : SizeAssignment ctx) :
    (parameter name).eval assignment = assignment name := rfl
@[simp] theorem eval_add (left right : SizeExpression ctx) (assignment : SizeAssignment ctx) :
    (left + right).eval assignment = left.eval assignment + right.eval assignment := rfl
@[simp] theorem eval_mul (left right : SizeExpression ctx) (assignment : SizeAssignment ctx) :
    (left * right).eval assignment = left.eval assignment * right.eval assignment := rfl
@[simp] theorem eval_pow (base : SizeExpression ctx) (exponent : ℕ) (assignment : SizeAssignment ctx) :
    (base ^ exponent).eval assignment = base.eval assignment ^ exponent := rfl

noncomputable section PolynomialMeaning

def polynomial : SizeExpression ctx → SizePolynomial ctx
  | .constant value => SizePolynomial.constant value
  | .parameter name => SizePolynomial.parameter name
  | .add left right => left.polynomial + right.polynomial
  | .mul left right => left.polynomial * right.polynomial
  | .pow base exponent => base.polynomial ^ exponent

/-- Executable evaluation agrees with the derived mathematical polynomial. -/
theorem eval_eq (expression : SizeExpression ctx) (assignment : SizeAssignment ctx) :
    expression.eval assignment = expression.polynomial.eval assignment := by
  induction expression <;> simp [eval, polynomial, *]

end PolynomialMeaning
end SizeExpression
end Polytime
