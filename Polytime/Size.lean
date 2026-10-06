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
an assignment gives each name an arbitrary natural value. No parameter bounds
or distinguished complexity parameter belong to this data layer.
-/

namespace Polytime

structure SizeContext where
  Parameter : Type
  finiteParameters : Fintype Parameter

attribute [instance] SizeContext.finiteParameters

abbrev SizeAssignment (ctx : SizeContext) := ctx.Parameter → ℕ
abbrev SizeExpr (ctx : SizeContext) := MvPolynomial ctx.Parameter ℕ

namespace SizeExpr

variable {ctx : SizeContext}

noncomputable section

def parameter (k : ctx.Parameter) : SizeExpr ctx := MvPolynomial.X k
def constant (n : ℕ) : SizeExpr ctx := MvPolynomial.C n

def eval (e : SizeExpr ctx) (a : SizeAssignment ctx) : ℕ :=
  MvPolynomial.eval a e

@[simp] theorem eval_parameter (k : ctx.Parameter) (a : SizeAssignment ctx) :
    eval (parameter k) a = a k := by
  simp [eval, parameter]

@[simp] theorem eval_constant (n : ℕ) (a : SizeAssignment ctx) : eval (constant n) a = n := by
  simp [eval, constant]

@[simp] theorem eval_zero (a : SizeAssignment ctx) : eval (0 : SizeExpr ctx) a = 0 := by
  simp [eval]

@[simp] theorem eval_one (a : SizeAssignment ctx) : eval (1 : SizeExpr ctx) a = 1 := by
  simp [eval]

@[simp] theorem eval_add (e f : SizeExpr ctx) (a : SizeAssignment ctx) :
    eval (e + f) a = eval e a + eval f a := by simp [eval]

@[simp] theorem eval_mul (e f : SizeExpr ctx) (a : SizeAssignment ctx) :
    eval (e * f) a = eval e a * eval f a := by simp [eval]

@[simp] theorem eval_pow (e : SizeExpr ctx) (n : ℕ) (a : SizeAssignment ctx) :
    eval (e ^ n) a = eval e a ^ n := by simp [eval]

/-- Natural-coefficient size expressions are monotone in every parameter. -/
theorem eval_mono (e : SizeExpr ctx) (a b : SizeAssignment ctx) (h : ∀ k, a k ≤ b k) :
    e.eval a ≤ e.eval b := by
  induction e using MvPolynomial.induction_on with
  | C n => simp [eval]
  | add e f he hf => simpa using Nat.add_le_add he hf
  | mul_X e k he => simpa [eval] using Nat.mul_le_mul he (h k)

end
end SizeExpr
end Polytime
