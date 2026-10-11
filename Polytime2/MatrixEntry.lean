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

import Polytime2.MatrixAddress
import Polytime2.MatrixAccess
import Polytime2.Alphabet

/-! # Complete runtime matrix-entry access

Compute the address from row/column counters, read or write the scalar, and
clear the address counter. The dimension and index counters, all heads, and
the caller's array are preserved according to the selected access mode.
-/

namespace Polytime2.MatrixEntry

open MultiTape

variable {Scalar : Type} {rows columns : ℕ}

abbrev TapeName := Sum MatrixAddress.TapeName Bool

abbrev Alphabet (Scalar : Type) : TapeName → Type
  | .inl _ => Binary.Symbol
  | .inr _ => TableTraversal.Symbol Scalar

instance (name : TapeName) : Inhabited (Alphabet Scalar name) :=
  match name with
  | .inl _ => (⟨0⟩ : Inhabited Binary.Symbol)
  | .inr _ => (⟨none⟩ : Inhabited (TableTraversal.Symbol Scalar))

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) := by
  cases name <;> dsimp [Alphabet] <;> infer_instance

def scalarWiring : ScalarAccess.TapeName ↪ TapeName where
  toFun
    | .index => .inl .output
    | .array => .inr false
    | .element => .inr true
  inj' := by intro first second equal; cases first <;> cases second <;> simp_all

def scalarEquivalences (Scalar : Type) (name : ScalarAccess.TapeName) :
    ScalarAccess.Alphabet Scalar name ≃ Alphabet Scalar (scalarWiring name) := by
  cases name <;> exact Equiv.refl _

theorem scalarBlanks (name : ScalarAccess.TapeName) : scalarEquivalences Scalar name default = default := by
  cases name <;> rfl

noncomputable def address : Machine (Alphabet Scalar) MatrixAddress.State :=
  wire Function.Embedding.inl MatrixAddress.machine

noncomputable def access (write : Bool) : Machine (Alphabet Scalar) (Fin 3) :=
  wire scalarWiring (relabel (scalarEquivalences Scalar) (ScalarAccess.machine write))

noncomputable def clearAddress : Machine (Alphabet Scalar) (Fin 3) :=
  wire (oneTape (Sum.inl MatrixAddress.TapeName.output)) (Unary.machine true)

abbrev State := Sum (Sum MatrixAddress.State (Fin 3)) (Fin 3)

noncomputable def machine (write : Bool) : Machine (Alphabet Scalar) State :=
  sequence (sequence address (access write) 0) clearAddress 0

def entry : State := .inl (.inl MatrixAddress.entry)
def exit : State := .inr 2

def frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (address : ℕ) (element : Scalar) : Tapes (Alphabet Scalar)
  | .inl name => MatrixAddress.ready row.val columns column.val address name
  | .inr false => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]))
  | .inr true => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk [some (some element)])

private theorem address_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    Steps address (3 * row.val * columns + 9 * row.val + 3 * column.val + 12)
      (MatrixAddress.entry, frame matrix row column 0 element)
      (MatrixAddress.exit, frame matrix row column (row.val * columns + column.val) element) := by
  have trace := wire_steps Function.Embedding.inl MatrixAddress.machine
    (MatrixAddress.steps row.val columns column.val) (frame matrix row column 0 element)
    (by intro name; rfl)
  have restored : install Function.Embedding.inl
      (MatrixAddress.ready row.val columns column.val (row.val * columns + column.val))
      (frame matrix row column 0 element) =
      frame matrix row column (row.val * columns + column.val) element := by
    funext name
    cases name with
    | inl name => exact install_at Function.Embedding.inl _ _ name
    | inr name =>
      cases name <;>
        exact install_outside Function.Embedding.inl _ _ _ (by rintro ⟨source, equal⟩; cases equal)
  simpa only [address, restored] using trace

private theorem localFrame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    mapTapes (scalarEquivalences Scalar) scalarBlanks (MatrixAccess.frame matrix row column element) =
      fun name => frame matrix row column (row.val * columns + column.val) element (scalarWiring name) := by
  funext name
  cases name with
  | index =>
    change (Binary.tape [3] (List.replicate (MatrixAccess.address row column).val 2 ++ [0]) ()).map
      (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) =
      Binary.tape [3] (List.replicate (row.val * columns + column.val) 2 ++ [0]) ()
    rw [MatrixAccess.address_value]
    exact mapTape_identity _
  | array =>
    change (Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]))).map
        (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) = _
    exact mapTape_identity _
  | element =>
    change (Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk [some (some element)])).map
        (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) = _
    exact mapTape_identity _

private theorem access_steps (write : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    Steps (access write) (2 * (row.val * columns + column.val) + 3)
      (0, frame matrix row column (row.val * columns + column.val) element)
      (2, frame (if write then MatrixAccess.update matrix row column element else matrix)
        row column (row.val * columns + column.val) (if write then element else matrix row column)) := by
  have localTrace : Steps (ScalarAccess.machine write) (2 * (row.val * columns + column.val) + 3)
      (0, MatrixAccess.frame matrix row column element)
      (2, MatrixAccess.frame (if write then MatrixAccess.update matrix row column element else matrix)
        row column (if write then element else matrix row column)) := by
    cases write with
    | false => exact MatrixAccess.lookup_steps matrix row column element
    | true => exact MatrixAccess.update_steps matrix row column element
  have mapped := localTrace.relabel (scalarEquivalences Scalar) scalarBlanks
  simp only [localFrame] at mapped
  have trace := wire_steps scalarWiring (relabel (scalarEquivalences Scalar) (ScalarAccess.machine write))
    mapped (frame matrix row column (row.val * columns + column.val) element) (by intro name; rfl)
  have restored : install scalarWiring
      (fun name => frame (if write then MatrixAccess.update matrix row column element else matrix)
        row column (row.val * columns + column.val) (if write then element else matrix row column) (scalarWiring name))
      (frame matrix row column (row.val * columns + column.val) element) =
      frame (if write then MatrixAccess.update matrix row column element else matrix)
        row column (row.val * columns + column.val) (if write then element else matrix row column) := by
    funext name
    cases name with
    | inl name =>
      cases name with
      | output => exact install_at scalarWiring _ _ .index
      | row =>
        exact install_outside scalarWiring _ _ (.inl .row)
          (by rintro ⟨source, equal⟩; cases source <;> cases equal)
      | width =>
        exact install_outside scalarWiring _ _ (.inl .width)
          (by rintro ⟨source, equal⟩; cases source <;> cases equal)
      | column =>
        exact install_outside scalarWiring _ _ (.inl .column)
          (by rintro ⟨source, equal⟩; cases source <;> cases equal)
    | inr name =>
      cases name with
      | false => exact install_at scalarWiring _ _ .array
      | true => exact install_at scalarWiring _ _ .element
  simpa only [access, restored] using trace

private theorem clear_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (address : ℕ) (element : Scalar) :
    Steps clearAddress (2 * address + 3)
      (0, frame matrix row column address element)
      (2, frame matrix row column 0 element) := by
  have localTrace : Steps (Unary.machine true) (2 * address + 3)
      (0, Binary.tape [3] (List.replicate address 2 ++ [0]))
      (2, Binary.tape [3] [0]) := by
    have trace := Unary.reset_steps address [] []
    have zeros : Turing.ListBlank.mk (List.replicate address (0 : Binary.Symbol) ++ [0]) =
        Turing.ListBlank.mk [0] := by
      rw [← List.replicate_succ', UnaryAppend.mk_replicate_zero, UnaryAppend.mk_zero]
    have erased : Binary.tape [3] (List.replicate address 0 ++ [0]) = Binary.tape [3] [0] := by
      funext name
      exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk [3])) zeros
    rw [erased] at trace
    exact trace
  have trace := wire_steps (oneTape (Sum.inl MatrixAddress.TapeName.output)) (Unary.machine true)
    localTrace (frame matrix row column address element) (by intro name; cases name; rfl)
  have restored : install (oneTape (Sum.inl MatrixAddress.TapeName.output)) (Binary.tape [3] [0])
      (frame matrix row column address element) = frame matrix row column 0 element := by
    funext name
    cases name with
    | inl name =>
      cases name with
      | output => exact install_at (oneTape (Sum.inl MatrixAddress.TapeName.output)) _ _ ()
      | row =>
        exact install_outside (oneTape (Sum.inl MatrixAddress.TapeName.output : TapeName)) _ _
          (.inl .row) (by rintro ⟨source, equal⟩; cases equal)
      | width =>
        exact install_outside (oneTape (Sum.inl MatrixAddress.TapeName.output : TapeName)) _ _
          (.inl .width) (by rintro ⟨source, equal⟩; cases equal)
      | column =>
        exact install_outside (oneTape (Sum.inl MatrixAddress.TapeName.output : TapeName)) _ _
          (.inl .column) (by rintro ⟨source, equal⟩; cases equal)
    | inr name =>
      cases name <;> exact install_outside (oneTape (Sum.inl MatrixAddress.TapeName.output : TapeName)) _ _
        _ (by rintro ⟨source, equal⟩; cases equal)
  simpa only [clearAddress, restored] using trace

/-- Complete matrix-entry access with reusable zeroed address scratch. -/
theorem steps (write : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    Steps (machine write) (7 * row.val * columns + 9 * row.val + 7 * column.val + 20)
      (entry, frame matrix row column 0 element)
      (exit, frame (if write then MatrixAccess.update matrix row column element else matrix)
        row column 0 (if write then element else matrix row column)) := by
  have first := sequence_steps address (access write) 0 (address_steps matrix row column element)
    (by intro symbols; rfl)
    (access_steps write matrix row column element)
  have complete := sequence_steps (sequence address (access write) 0) clearAddress 0 first
    (by intro symbols; rfl)
    (clear_steps (if write then MatrixAccess.update matrix row column element else matrix)
      row column (row.val * columns + column.val) (if write then element else matrix row column))
  convert complete using 1 <;> first | rfl | ring

/-- Polynomial runtime in the independent matrix dimensions. The scratch
address is zero on entry and exit, so successive accesses can share it. -/
theorem realizes [Fintype Scalar] (write : Bool) :
    Realizes (machine (Scalar := Scalar) write) entry exit
      (fun assignment initial =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
          initial = frame matrix row column 0 element)
      (fun assignment initial final =>
        ∀ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
          initial = frame matrix row column 0 element →
          final = frame (if write then MatrixAccess.update matrix row column element else matrix)
            row column 0 (if write then element else matrix row column)) := by
  refine ⟨by intro symbols; rfl,
    7 * MvPolynomial.X false * MvPolynomial.X true + 9 * MvPolynomial.X false + 7 * MvPolynomial.X true + 20, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, row, column, element, rfl⟩ := valid
  refine ⟨7 * row.val * assignment true + 9 * row.val + 7 * column.val + 20, _, ?_,
    steps write matrix row column element, ?_⟩
  · have product := Nat.mul_le_mul_right (assignment true) row.isLt.le
    have rowBound := row.isLt
    have columnBound := column.isLt
    simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    nlinarith
  · intro otherMatrix otherRow otherColumn otherElement agreement
    have otherTrace : Steps (machine write)
        (7 * otherRow.val * assignment true + 9 * otherRow.val + 7 * otherColumn.val + 20)
        (entry, frame matrix row column 0 element)
        (exit, frame (if write then MatrixAccess.update otherMatrix otherRow otherColumn otherElement else otherMatrix)
          otherRow otherColumn 0 (if write then otherElement else otherMatrix otherRow otherColumn)) := by
      rw [agreement]
      exact steps write otherMatrix otherRow otherColumn otherElement
    exact congrArg Prod.snd ((steps write matrix row column element).final_eq otherTrace rfl rfl)

end Polytime2.MatrixEntry
