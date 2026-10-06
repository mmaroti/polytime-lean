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

import Polytime.Domain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Exact rectangular matrices over a fixed finite field

K and L are external indices bounded by N. A matrix contains only its entries,
in row-major order: rows first, then entries within each row.
-/

namespace Polytime.Examples.Matrices

inductive Parameter | K | L
  deriving DecidableEq

instance : Fintype Parameter := ⟨{.K, .L}, by intro k; cases k <;> simp⟩

noncomputable section

def context : SizeContext Parameter where
  bound _ := Polynomial.X

def assignment (N K L : ℕ) : SizeAssignment Parameter where
  N := N
  auxiliary | .K => K | .L => L

@[simp] theorem admissible_iff (N K L : ℕ) :
    context.Admissible (assignment N K L) ↔ K ≤ N ∧ L ≤ N := by
  simp only [SizeContext.Admissible, context, Polynomial.eval_X, assignment]
  constructor
  · intro h; exact ⟨h .K, h .L⟩
  · rintro ⟨hK, hL⟩ k; cases k <;> assumption

def domain (field : FinitePresentation.{u}) : DomainExpr Parameter :=
  .power (.power (.fixed field) (SizeExpr.parameter .L)) (SizeExpr.parameter .K)

/-- In particular this works for a finite field equipped with an enumeration. -/
def valueEquiv (field : FinitePresentation.{u}) (N K L : ℕ) :
    (domain field).Value context (assignment N K L) ≃
      Matrix (Fin K) (Fin L) field.Carrier := by
  simp only [domain, DomainExpr.value_power, DomainExpr.value_fixed,
    SizeExpr.eval_parameter, assignment]
  exact Equiv.refl (Matrix (Fin K) (Fin L) field.Carrier)

@[simp] theorem exact_width (field : FinitePresentation.{u}) (N K L : ℕ) :
    (domain field).bitWidth context (assignment N K L) = K * L * field.bitWidth := by
  simp [domain, assignment, Nat.mul_assoc]

theorem width_le_square (field : FinitePresentation.{u}) (N K L : ℕ)
    (hK : K ≤ N) (hL : L ≤ N) :
    (domain field).bitWidth context (assignment N K L) ≤ N ^ 2 * field.bitWidth := by
  rw [exact_width, pow_two]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hL)

/-- Users can instead request the qualitative certificate without naming a bound. -/
theorem polynomial_size (field : FinitePresentation.{u}) :
    ∃ p : Polynomial ℕ, ∀ a, context.Admissible a →
      (domain field).bitWidth context a ≤ p.eval a.N :=
  (domain field).polynomially_bounded context

def encode (field : FinitePresentation.{u}) (N K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) :
    BitVec ((domain field).bitWidth context (assignment N K L)) :=
  (domain field).encode context (assignment N K L) ((valueEquiv field N K L).symm matrix)

theorem decode_matrix (field : FinitePresentation.{u}) (N K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) :
    (domain field).decode context (assignment N K L) (encode field N K L matrix) =
      some ((valueEquiv field N K L).symm matrix) :=
  (domain field).decode_encode context (assignment N K L) _

def field5 : FinitePresentation where
  Carrier := ZMod 5
  cardinality := 5
  enumeration := (ZMod.finEquiv 5).toEquiv.symm

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
example : Field field5.Carrier := inferInstanceAs (Field (ZMod 5))

@[simp] theorem field5_width : field5.bitWidth = 3 := by decide

def sample : Matrix (Fin 2) (Fin 3) (ZMod 5) := !![0, 1, 2; 3, 4, 0]

example : context.Admissible (assignment 3 2 3) := by simp

example : (domain field5).bitWidth context (assignment 3 2 3) = 18 := by simp

example : (domain field5).decode context (assignment 3 2 3) (encode field5 3 2 3 sample) =
    some ((valueEquiv field5 3 2 3).symm sample) := decode_matrix _ _ _ _ _

example (N L : ℕ) : (domain field5).bitWidth context (assignment N 0 L) = 0 := by simp
example (N K : ℕ) : (domain field5).bitWidth context (assignment N K 0) = 0 := by simp

def constantTuple (field : FinitePresentation.{u}) : DomainExpr Parameter :=
  .power (.fixed field) (SizeExpr.constant 3)

example (field : FinitePresentation.{u}) (a : SizeAssignment Parameter) :
    (constantTuple field).bitWidth context a = 3 * field.bitWidth := by simp [constantTuple]

def compositeTuple (field : FinitePresentation.{u}) : DomainExpr Parameter :=
  .power (.fixed field)
    (SizeExpr.main ^ 2 + SizeExpr.parameter .K * SizeExpr.parameter .L)

example (field : FinitePresentation.{u}) :
    ∃ p : Polynomial ℕ, ∀ a, context.Admissible a →
      (compositeTuple field).bitWidth context a ≤ p.eval a.N :=
  (compositeTuple field).polynomially_bounded context

example (field : FinitePresentation.{u}) (N K L : ℕ) :
    (compositeTuple field).bitWidth context (assignment N K L) =
      (N ^ 2 + K * L) * field.bitWidth := by simp [compositeTuple, assignment]

end
end Polytime.Examples.Matrices
