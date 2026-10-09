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

-- u: the fixed scalar carrier used for matrix entries.
universe u

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
      Matrix (Fin K) (Fin L) field.Carrier :=
  Equiv.cast (by simp only [domain, DomainExpression.value_power, DomainExpression.value_fixed,
    SizeExpression.eval_parameter (ctx := context), assignment]; rfl)

@[simp] theorem exact_width (field : FixedPresentation.{u}) (K L : ℕ) :
    (domain field).bitWidth (assignment K L) = K * L * field.bitWidth := by
  simp [domain, SizeExpression.eval_parameter (ctx := context), assignment, Nat.mul_assoc]

/-- The size certificate is uniform over all independent dimension assignments. -/
theorem polynomial_size (field : FixedPresentation.{u}) :
    ∃ p : SizePolynomial context, ∀ a, (domain field).bitWidth a ≤ p.eval a :=
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

/-- The bit address of a matrix entry is its row-major position times the
fixed scalar width, followed by the offset inside that scalar. -/
theorem encode_entry_bit (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier)
    (row : Fin K) (column : Fin L) (offset : Fin field.bitWidth) :
    (encode field K L matrix).getLsbD
        ((row.val * L + column.val) * field.bitWidth + offset.val) =
      (field.codec.encode (matrix row column)).getLsbD offset.val := by
  let inner : DomainExpression context :=
    .power (.fixed field) (SizeExpression.parameter (ctx := context) .L)
  let rows : Fin K → inner.Value (assignment K L) := fun index =>
    DomainExpression.powerFixedValue field
      (SizeExpression.parameter (ctx := context) .L) (assignment K L) (matrix index)
  have representation : (valueEquiv field K L).symm matrix =
      DomainExpression.powerValue inner (.parameter .K) (assignment K L) rows := by
    apply eq_of_heq
    have source : HEq ((valueEquiv field K L).symm matrix) matrix := cast_heq _ _
    apply source.trans
    symm
    unfold DomainExpression.powerValue
    apply (cast_heq _ _).trans
    apply Function.hfunext rfl
    intro index other same
    cases same
    dsimp only [rows]
    unfold DomainExpression.powerFixedValue DomainExpression.powerValue
    apply (cast_heq _ _).trans
    apply Function.hfunext rfl
    intro position other same
    cases same
    exact cast_heq _ _
  rw [encode, representation]
  change ((inner.power (SizeExpression.parameter (ctx := context) .K)).encode (assignment K L)
    (DomainExpression.powerValue inner _ _ rows)).getLsbD _ = _
  erw [DomainExpression.encode_power_bit]
  have innerWidth : inner.bitWidth (assignment K L) = L * field.bitWidth := by
    simp [inner, assignment]
  have validOffset : column.val * field.bitWidth + offset.val <
      inner.bitWidth (assignment K L) := by
    rw [innerWidth]
    have columnBound := Nat.mul_le_mul_right field.bitWidth column.isLt
    simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at columnBound
    omega
  have address : (row.val * L + column.val) * field.bitWidth + offset.val =
      row.val * inner.bitWidth (assignment K L) + (column.val * field.bitWidth + offset.val) := by
    rw [innerWidth]
    ring
  rw [address]
  erw [BitCodec.power_encode_entry_bit _ _ rows row ⟨_, validOffset⟩]
  change (inner.encode (assignment K L) (rows row)).getLsbD _ = _
  dsimp only [rows, inner]
  erw [DomainExpression.encode_power_fixed_bit]
  exact BitCodec.power_encode_entry_bit _ L (matrix row) column offset

/-- A scalar's complete canonical encoding is the corresponding matrix slice. -/
theorem encode_entry_slice (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) (row : Fin K) (column : Fin L) :
    ((List.ofFn (fun index : Fin ((domain field).bitWidth (assignment K L)) =>
        (encode field K L matrix).getLsbD index.val)).drop
      ((row.val * L + column.val) * field.bitWidth)).take field.bitWidth =
      List.ofFn (fun offset : Fin field.bitWidth =>
        (field.codec.encode (matrix row column)).getLsbD offset.val) := by
  have entryBound : row.val * L + column.val + 1 ≤ K * L := by
    calc
      _ ≤ row.val * L + L := by omega
      _ = (row.val + 1) * L := by ring
      _ ≤ K * L := Nat.mul_le_mul_right L row.isLt
  have blockFits : (row.val * L + column.val) * field.bitWidth + field.bitWidth ≤
      (domain field).bitWidth (assignment K L) := by
    rw [exact_width]
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right field.bitWidth entryBound
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro index firstValid secondValid
    simp only [List.length_ofFn] at secondValid
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    exact encode_entry_bit field K L matrix row column ⟨index, secondValid⟩

/-- Replacing one matrix entry replaces exactly its canonical scalar block. -/
theorem encode_update_entry (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) (row : Fin K) (column : Fin L)
    (replacement : field.Carrier) :
    let width := (domain field).bitWidth (assignment K L)
    let payload := List.ofFn (fun index : Fin width => (encode field K L matrix).getLsbD index.val)
    let start := (row.val * L + column.val) * field.bitWidth
    List.ofFn (fun index : Fin width =>
      (encode field K L (Function.update matrix row (Function.update (matrix row) column replacement))).getLsbD index.val) =
      payload.take start ++ (List.ofFn (fun offset : Fin field.bitWidth =>
        (field.codec.encode replacement).getLsbD offset.val) ++ payload.drop (start + field.bitWidth)) := by
  dsimp only
  let width := (domain field).bitWidth (assignment K L)
  let payload := List.ofFn (fun index : Fin width => (encode field K L matrix).getLsbD index.val)
  let start := (row.val * L + column.val) * field.bitWidth
  let updated := Function.update matrix row (Function.update (matrix row) column replacement)
  let target : Fin (K * L) := finProdFinEquiv (row, column)
  have startEq : start = target.val * field.bitWidth := by
    dsimp [start, target, finProdFinEquiv]
    ring
  have entryBound : row.val * L + column.val + 1 ≤ K * L := by
    calc
      _ ≤ row.val * L + L := by omega
      _ = (row.val + 1) * L := by ring
      _ ≤ K * L := Nat.mul_le_mul_right L row.isLt
  have blockFits : start + field.bitWidth ≤ width := by
    dsimp only [start, width]
    rw [exact_width]
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right field.bitWidth entryBound
  have payloadLength : payload.length = width := List.length_ofFn
  have prefixLength : (payload.take start).length = start := by simp [payloadLength]; omega
  change List.ofFn (fun index : Fin width => (encode field K L updated).getLsbD index.val) =
    payload.take start ++ (List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode replacement).getLsbD offset.val) ++ payload.drop (start + field.bitWidth))
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, prefixLength, List.length_drop, payloadLength]
    omega
  · intro index firstValid secondValid
    simp only [List.length_ofFn] at firstValid
    let position : Fin (K * L * field.bitWidth) := ⟨index, by simpa [width] using firstValid⟩
    let coordinate : Fin (K * L) × Fin field.bitWidth := finProdFinEquiv.symm position
    let rowColumn : Fin K × Fin L := finProdFinEquiv.symm coordinate.1
    have positionEq : index = coordinate.1.val * field.bitWidth + coordinate.2.val := by
      have result := congrArg Fin.val (finProdFinEquiv.apply_symm_apply position)
      simpa [position, coordinate, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using result.symm
    have entryEq : coordinate.1.val = rowColumn.1.val * L + rowColumn.2.val := by
      have result := congrArg Fin.val (finProdFinEquiv.apply_symm_apply coordinate.1)
      simpa [rowColumn, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using result.symm
    have addressEq : index = (rowColumn.1.val * L + rowColumn.2.val) * field.bitWidth + coordinate.2.val := by
      rw [positionEq, entryEq]
    have newBit := encode_entry_bit field K L updated rowColumn.1 rowColumn.2 coordinate.2
    have oldBit := encode_entry_bit field K L matrix rowColumn.1 rowColumn.2 coordinate.2
    rw [← addressEq] at newBit oldBit
    simp only [List.getElem_ofFn]
    rw [newBit]
    by_cases same : coordinate.1 = target
    · have selected : rowColumn = (row, column) := by
        change finProdFinEquiv.symm coordinate.1 = (row, column)
        rw [same]
        exact finProdFinEquiv.symm_apply_apply (row, column)
      have exactPosition : index = start + coordinate.2.val := by
        rw [same] at positionEq
        omega
      have inside : index - start = coordinate.2.val := by omega
      have afterPrefix : ¬ index < start := by omega
      simp [List.getElem_append, prefixLength, afterPrefix, inside,
        selected, updated, Function.update]
    · have different : coordinate.1.val ≠ target.val := Fin.ext_iff.not.mp same
      have unchanged : updated rowColumn.1 rowColumn.2 = matrix rowColumn.1 rowColumn.2 := by
        by_cases sameRow : rowColumn.1 = row
        · have differentColumn : rowColumn.2 ≠ column := by
            intro sameColumn
            apply same
            have result := finProdFinEquiv.apply_symm_apply coordinate.1
            change finProdFinEquiv rowColumn = coordinate.1 at result
            rw [show rowColumn = (row, column) from Prod.ext sameRow sameColumn] at result
            exact result.symm
          simp [updated, Function.update, sameRow, differentColumn]
        · simp [updated, Function.update, sameRow]
      rw [unchanged, ← oldBit]
      by_cases earlier : coordinate.1.val < target.val
      · have productBound := Nat.mul_le_mul_right field.bitWidth earlier
        simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at productBound
        have beforePrefix : index < start := by have bound := coordinate.2.isLt; omega
        simp [prefixLength, beforePrefix, List.getElem_take, payload]
      · have productBound := Nat.mul_le_mul_right field.bitWidth (by omega : target.val + 1 ≤ coordinate.1.val)
        simp only [Nat.add_mul, Nat.one_mul] at productBound
        have pastBlock : start + field.bitWidth ≤ index := by omega
        have afterPrefix : ¬ index < start := by omega
        have afterScalar : ¬ index - start < field.bitWidth := by omega
        have originalIndex : start + field.bitWidth + (index - start - field.bitWidth) = index := by omega
        simp [List.getElem_append, prefixLength, afterPrefix, afterScalar,
          List.getElem_drop, payload, originalIndex]

def field5 : FixedPresentation where
  Carrier := ZMod 5
  cardinality := 5
  enumeration := (ZMod.finEquiv 5).toEquiv.symm

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance field5Field : Field field5.Carrier := inferInstanceAs (Field (ZMod 5))
instance field5DecidableEq : DecidableEq field5.Carrier := inferInstanceAs (DecidableEq (ZMod 5))

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
    ∃ p : SizePolynomial context, ∀ a, (compositeTuple field).bitWidth a ≤ p.eval a :=
  (compositeTuple field).polynomially_bounded

example (field : FixedPresentation.{u}) (K L : ℕ) :
    (compositeTuple field).bitWidth (assignment K L) =
      (K ^ 2 + K * L) * field.bitWidth := by
  simp [compositeTuple, SizeExpression.eval_parameter (ctx := context), assignment]

end MatrixExamples
end Polytime.Examples.Matrices
