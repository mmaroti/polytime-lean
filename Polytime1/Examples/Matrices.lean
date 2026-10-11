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

import Polytime1.Domain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Exact rectangular matrices over a fixed finite field

K and L are independent external indices. A matrix contains only its entries,
in row-major order: rows first, then entries within each row.
-/

namespace Polytime1.Examples.Matrices

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
  let sizes := assignment K L
  let inner : DomainExpression context := .power (.fixed field) (.parameter .L)
  (DomainExpression.powerEquiv inner (.parameter .K) sizes).trans
    (Equiv.piCongrRight fun _ =>
      (DomainExpression.powerEquiv (.fixed field) (SizeExpression.parameter (ctx := context) .L) sizes).trans
        (Equiv.piCongrRight fun _ => DomainExpression.fixedEquiv field sizes))

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
  let sizes := assignment K L
  let inner : DomainExpression context := .power (.fixed field) (.parameter .L)
  have innerWidth : inner.bitWidth sizes = L * field.bitWidth := by simp [inner, sizes, assignment]
  have validOffset : column.val * field.bitWidth + offset.val < inner.bitWidth sizes := by
    rw [innerWidth]
    have columnBound := Nat.mul_le_mul_right field.bitWidth column.isLt
    simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at columnBound
    omega
  have address : (row.val * L + column.val) * field.bitWidth + offset.val =
      row.val * inner.bitWidth sizes + (column.val * field.bitWidth + offset.val) := by
    rw [innerWidth]
    ring
  rw [address]
  unfold encode
  change ((inner.power (.parameter .K)).encode sizes ((valueEquiv field K L).symm matrix)).getLsbD _ = _
  erw [DomainExpression.encode_power_lookup_bit inner (.parameter .K) sizes _ row ⟨_, validOffset⟩]
  change ((DomainExpression.power (.fixed field) (SizeExpression.parameter (ctx := context) .L)).encode sizes _).getLsbD _ = _
  erw [DomainExpression.encode_power_fixed_lookup_bit field (SizeExpression.parameter (ctx := context) .L) sizes _ column offset]
  have viewed := congrFun (congrFun ((valueEquiv field K L).apply_symm_apply matrix) row) column
  exact congrArg (fun scalar => (field.codec.encode scalar).getLsbD offset.val) viewed

/-- Every indexed entry's complete block fits, including zero-width scalars. -/
theorem entry_block_fits (field : FixedPresentation.{u}) (K L : ℕ)
    (row : Fin K) (column : Fin L) :
    (row.val * L + column.val) * field.bitWidth + field.bitWidth ≤
      (domain field).bitWidth (assignment K L) := by
  have entryBound : row.val * L + column.val + 1 ≤ K * L := by
    calc
      _ ≤ row.val * L + L := by omega
      _ = (row.val + 1) * L := by ring
      _ ≤ K * L := Nat.mul_le_mul_right L row.isLt
  rw [exact_width]
  simpa only [Nat.add_mul, Nat.one_mul] using Nat.mul_le_mul_right field.bitWidth entryBound

/-- A scalar's complete canonical encoding is the corresponding matrix slice. -/
theorem encode_entry_slice (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) (row : Fin K) (column : Fin L) :
    ((List.ofFn (fun index : Fin ((domain field).bitWidth (assignment K L)) =>
        (encode field K L matrix).getLsbD index.val)).drop
      ((row.val * L + column.val) * field.bitWidth)).take field.bitWidth =
      List.ofFn (fun offset : Fin field.bitWidth =>
        (field.codec.encode (matrix row column)).getLsbD offset.val) := by
  exact BitCodec.slice_of_bits (encode field K L matrix) (field.codec.encode (matrix row column))
    ((row.val * L + column.val) * field.bitWidth) (entry_block_fits field K L row column)
    (encode_entry_bit field K L matrix row column)

/-- Shared decomposition for readers and writers, with or without saved
counters. The prefix locates the entry; the lengths account for the whole payload. -/
theorem encode_entry_partition (field : FixedPresentation.{u}) (K L : ℕ)
    (matrix : Matrix (Fin K) (Fin L) field.Carrier) (row : Fin K) (column : Fin L) :
    let width := (domain field).bitWidth (assignment K L)
    let payload := List.ofFn (fun index : Fin width => (encode field K L matrix).getLsbD index.val)
    let scalar := List.ofFn (fun offset : Fin field.bitWidth =>
      (field.codec.encode (matrix row column)).getLsbD offset.val)
    let start := (row.val * L + column.val) * field.bitWidth
    payload.take start ++ scalar ++ payload.drop (start + field.bitWidth) = payload ∧
      (payload.take start).length = start ∧
      (payload.take start).length + field.bitWidth + (payload.drop (start + field.bitWidth)).length = width := by
  dsimp only
  have fits := entry_block_fits field K L row column
  have split := List.take_append_drop
    ((row.val * L + column.val) * field.bitWidth + field.bitWidth)
    (List.ofFn (fun index : Fin ((domain field).bitWidth (assignment K L)) =>
      (encode field K L matrix).getLsbD index.val))
  rw [List.take_add, encode_entry_slice] at split
  refine ⟨split, ?_, ?_⟩
  · simp only [List.length_take, List.length_ofFn]
    exact Nat.min_eq_left (by omega)
  · have lengths := congrArg List.length split
    simpa only [List.length_append, List.length_ofFn] using lengths

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
  let start := (row.val * L + column.val) * field.bitWidth
  let updated : Matrix (Fin K) (Fin L) field.Carrier :=
    Function.update matrix row (Function.update (matrix row) column replacement)
  apply BitCodec.replace_of_bits (encode field K L matrix) (encode field K L updated)
    (field.codec.encode replacement) start (entry_block_fits field K L row column)
  · intro offset
    simpa [start, updated, Function.update] using
      encode_entry_bit field K L updated row column offset
  · intro index outside
    let position : Fin (K * L * field.bitWidth) := ⟨index.val, by simpa [width] using index.isLt⟩
    let coordinate : Fin (K * L) × Fin field.bitWidth := finProdFinEquiv.symm position
    let rowColumn : Fin K × Fin L := finProdFinEquiv.symm coordinate.1
    have positionEq : index.val = coordinate.1.val * field.bitWidth + coordinate.2.val := by
      have result := congrArg Fin.val (finProdFinEquiv.apply_symm_apply position)
      simpa [position, coordinate, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using result.symm
    have entryEq : coordinate.1.val = rowColumn.1.val * L + rowColumn.2.val := by
      have result := congrArg Fin.val (finProdFinEquiv.apply_symm_apply coordinate.1)
      simpa [rowColumn, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using result.symm
    have addressEq : index.val = (rowColumn.1.val * L + rowColumn.2.val) * field.bitWidth + coordinate.2.val := by
      rw [positionEq, entryEq]
    have different : ¬ (rowColumn.1 = row ∧ rowColumn.2 = column) := by
      intro selected
      have sameAddress : index.val = start + coordinate.2.val := by
        simpa only [selected.1, selected.2, start] using addressEq
      have bound := coordinate.2.isLt
      rcases outside with before | after <;> omega
    have unchanged : updated rowColumn.1 rowColumn.2 = matrix rowColumn.1 rowColumn.2 := by
      by_cases sameRow : rowColumn.1 = row
      · have differentColumn : rowColumn.2 ≠ column := fun equal => different ⟨sameRow, equal⟩
        simp [updated, Function.update, sameRow, differentColumn]
      · simp [updated, Function.update, sameRow]
    rw [addressEq]
    calc
      _ = (field.codec.encode (updated rowColumn.1 rowColumn.2)).getLsbD coordinate.2.val :=
        encode_entry_bit field K L updated rowColumn.1 rowColumn.2 coordinate.2
      _ = (field.codec.encode (matrix rowColumn.1 rowColumn.2)).getLsbD coordinate.2.val := by rw [unchanged]
      _ = _ := (encode_entry_bit field K L matrix rowColumn.1 rowColumn.2 coordinate.2).symm

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
end Polytime1.Examples.Matrices
