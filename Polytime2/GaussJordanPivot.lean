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


import Polytime2.GaussJordanClear

/-! # One complete Gauss–Jordan pivot operation

The pivot search leaves its selected entry in the source register. Preserve
that value as a coefficient, swap into the pivot row, normalize, and clear
every other row. The target traversal counter returns to zero.
-/

namespace Polytime2.GaussJordanPivot

open MultiTape GaussJordanWorkspace

variable {Scalar : Type} [Field Scalar] {rows columns : ℕ}

abbrev State := Sum (Sum (Sum Bool MatrixRows.State) MatrixRows.State) GaussJordanClear.State

instance statesFinite : Fintype State := inferInstance

noncomputable def machine : Machine (Alphabet Scalar) State :=
  sequence (sequence (sequence (loadCoefficient true id)
    (rowOperation true true MatrixRowField.swap) MatrixRows.entry)
      (rowOperation true false MatrixRowField.normalize) MatrixRows.entry)
        GaussJordanClear.machine GaussJordanClear.entry

def entry : State := .inl (.inl (.inl false))
def exit : State := .inr GaussJordanClear.exit

def bound (rows columns : ℕ) : ℕ :=
  2 * ((columns + 1) * (28 * rows * columns + 36 * rows + 32 * columns + 94) + 2 * columns + 5) +
    (2 * (rows + 1) * (GaussJordanClear.rowBound rows columns + 4 * rows + 9) + 4 * rows + 11) + 4

/-- The tape program computes the mathematical swap-normalize-clear operation. -/
theorem steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate pivot : Fin rows) (column : Fin columns) (targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget finalCoefficient, ticks ≤ bound rows columns ∧
      Steps machine ticks
        (entry, frame matrix candidate.val 0 pivot.val column.val (matrix candidate column) targetValue coefficient flag)
        (exit, frame (MatrixOperations.pivotStep matrix pivot candidate column)
          candidate.val 0 pivot.val column.val finalSource finalTarget finalCoefficient false) := by
  have loaded := loadCoefficient_steps true id matrix candidate.val 0 pivot.val column.val
    (matrix candidate column) targetValue coefficient flag
  simp only [ite_true, id_eq] at loaded
  obtain ⟨swapTicks, swappedSource, swappedTarget, swapCost, swapped⟩ :=
    row_steps true true MatrixRowField.swap matrix candidate.val 0 pivot.val column.val
      candidate.isLt pivot.isLt (matrix candidate column) targetValue (matrix candidate column) flag
  simp only [ite_true] at swapped
  rw [MatrixRowField.swap_transform] at swapped
  have swapComm : MatrixOperations.swapRows matrix candidate pivot = MatrixOperations.swapRows matrix pivot candidate := by
    ext row other
    simp [MatrixOperations.swapRows, Equiv.swap_comm]
  rw [swapComm] at swapped
  obtain ⟨normalizeTicks, normalizedSource, normalizedTarget, normalizeCost, normalized⟩ :=
    row_steps true false MatrixRowField.normalize (MatrixOperations.swapRows matrix pivot candidate)
      candidate.val 0 pivot.val column.val candidate.isLt pivot.isLt
        swappedSource swappedTarget (matrix candidate column) false
  simp only [ite_true] at normalized
  rw [MatrixRowField.normalize_transform] at normalized
  obtain ⟨clearTicks, finalSource, finalTarget, finalCoefficient, clearCost, cleared⟩ :=
    GaussJordanClear.steps
      (MatrixOperations.scaleRow (MatrixOperations.swapRows matrix pivot candidate) pivot (matrix candidate column)⁻¹)
      candidate.val pivot column normalizedSource normalizedTarget (matrix candidate column) false
  have first := sequence_steps _ _ MatrixRows.entry loaded (loadCoefficient_halt true id) swapped
  have second := sequence_steps _ _ MatrixRows.entry first
    (by intro symbols; simp [MultiTape.sequence, rowOperation_halt]) normalized
  have complete := sequence_steps _ _ GaussJordanClear.entry second
    (by intro symbols; simp [MultiTape.sequence, rowOperation_halt]) cleared
  refine ⟨_, finalSource, finalTarget, finalCoefficient, ?_, complete⟩
  dsimp [bound]
  omega

end Polytime2.GaussJordanPivot
