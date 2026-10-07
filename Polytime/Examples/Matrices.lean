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

K and L are independent external indices. A matrix contains only its entries,
in row-major order: rows first, then entries within each row.
-/

namespace Polytime.Examples.Matrices

inductive Parameter | K | L
  deriving DecidableEq

instance : Fintype Parameter := ⟨{.K, .L}, by intro k; cases k <;> simp⟩

abbrev context : SizeContext := ⟨Parameter, inferInstance⟩

def assignment (K L : ℕ) : SizeAssignment context
  | .K => K
  | .L => L

noncomputable section MatrixExamples

def domain (field : FixedPresentation.{u}) : DomainExpression context :=
  .power (.power (.fixed field) (SizeExpression.parameter (ctx := context) .L))
    (SizeExpression.parameter (ctx := context) .K)

/-- In particular this works for a finite field equipped with an enumeration. -/
def valueEquiv (field : FixedPresentation.{u}) (K L : ℕ) :
    (domain field).Value (assignment K L) ≃
      Matrix (Fin K) (Fin L) field.Carrier := by
  simp only [domain, DomainExpression.value_power, DomainExpression.value_fixed,
    SizeExpression.eval_parameter (ctx := context), assignment]
  exact Equiv.refl (Matrix (Fin K) (Fin L) field.Carrier)

@[simp] theorem exact_width (field : FixedPresentation.{u}) (K L : ℕ) :
    (domain field).bitWidth (assignment K L) = K * L * field.bitWidth := by
  simp [domain, SizeExpression.eval_parameter (ctx := context), assignment, Nat.mul_assoc]

/-- The size certificate is uniform over all independent dimension assignments. -/
theorem polynomial_size (field : FixedPresentation.{u}) :
    ∃ p : SizeExpression context, ∀ a, (domain field).bitWidth a ≤ p.eval a :=
  (domain field).polynomially_bounded

def encode (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) :
    BitVec ((domain field).bitWidth (assignment K L)) :=
  (domain field).encode (assignment K L) ((valueEquiv field K L).symm matrix)

theorem decode_matrix (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) :
    (domain field).decode (assignment K L) (encode field K L matrix) =
      some ((valueEquiv field K L).symm matrix) :=
  (domain field).decode_encode (assignment K L) _

def field5 : FixedPresentation where
  Carrier := ZMod 5
  cardinality := 5
  enumeration := (ZMod.finEquiv 5).toEquiv.symm

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
example : Field field5.Carrier := inferInstanceAs (Field (ZMod 5))

@[simp] theorem field5_width : field5.bitWidth = 3 := by decide

def sample : Matrix (Fin 2) (Fin 3) (ZMod 5) := !![0, 1, 2; 3, 4, 0]

example : (domain field5).bitWidth (assignment 2 3) = 18 := by simp

example : (domain field5).decode (assignment 2 3) (encode field5 2 3 sample) =
    some ((valueEquiv field5 2 3).symm sample) := decode_matrix _ _ _ _

example (L : ℕ) : (domain field5).bitWidth (assignment 0 L) = 0 := by simp
example (K : ℕ) : (domain field5).bitWidth (assignment K 0) = 0 := by simp

/-- Neither dimension bounds the other. -/
example : (domain field5).bitWidth (assignment 7 2) = 42 := by simp
example : (domain field5).bitWidth (assignment 2 7) = 42 := by simp

def constantTuple (field : FixedPresentation.{u}) : DomainExpression context :=
  .power (.fixed field) (SizeExpression.constant 3)

example (field : FixedPresentation.{u}) (a : SizeAssignment context) :
    (constantTuple field).bitWidth a = 3 * field.bitWidth := by simp [constantTuple]

def compositeTuple (field : FixedPresentation.{u}) : DomainExpression context :=
  .power (.fixed field)
    (SizeExpression.parameter (ctx := context) .K ^ 2 +
      SizeExpression.parameter (ctx := context) .K * SizeExpression.parameter (ctx := context) .L)

example (field : FixedPresentation.{u}) :
    ∃ p : SizeExpression context, ∀ a, (compositeTuple field).bitWidth a ≤ p.eval a :=
  (compositeTuple field).polynomially_bounded

example (field : FixedPresentation.{u}) (K L : ℕ) :
    (compositeTuple field).bitWidth (assignment K L) =
      (K ^ 2 + K * L) * field.bitWidth := by
  simp [compositeTuple, SizeExpression.eval_parameter (ctx := context), assignment]

end MatrixExamples
end Polytime.Examples.Matrices
