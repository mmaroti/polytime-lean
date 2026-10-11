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


import Polytime2.GaussJordanWorkspace

/-! # Clearing a pivot column in the shared workspace

Two guarded intervals visit rows below and above the pivot. The pivot itself
is skipped, and the saved pivot column survives every complete row traversal.
-/

namespace Polytime2.GaussJordanClear

open MultiTape GaussJordanWorkspace

variable {Scalar : Type} [Field Scalar] {rows columns : ℕ}

abbrev ClearState := Sum (Sum MatrixEntry.State Bool) MatrixRows.State

noncomputable def clearTarget : Machine (Alphabet Scalar) ClearState :=
  sequence (sequence readTarget (loadCoefficient false (- ·)) false)
    (rowOperation false false MatrixRowField.add) MatrixRows.entry

def clearEntry : ClearState := .inl (.inl MatrixEntry.entry)
def clearExit : ClearState := .inr MatrixRows.exit

def rowBound (rows columns : ℕ) : ℕ :=
  (columns + 1) * (28 * rows * columns + 36 * rows + 32 * columns + 94) +
    2 * columns + 5 + 7 * rows * columns + 9 * rows + 7 * columns + 23

theorem clearTarget_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (target pivot : Fin rows) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget, ticks ≤ rowBound rows columns ∧
      Steps clearTarget ticks
        (clearEntry, frame matrix candidate target.val pivot.val column.val sourceValue targetValue coefficient flag)
        (clearExit, frame (Function.update matrix target
          (fun other => matrix target other + (-matrix target column) * matrix pivot other))
          candidate target.val pivot.val column.val finalSource finalTarget (-matrix target column) false) := by
  have readTrace := readTarget_steps matrix candidate target pivot.val column sourceValue targetValue coefficient flag
  have loaded := loadCoefficient_steps false (- ·) matrix candidate target.val pivot.val column.val
    sourceValue (matrix target column) coefficient flag
  obtain ⟨rowTicks, finalSource, finalTarget, rowCost, rowTrace⟩ :=
    row_steps false false MatrixRowField.add matrix candidate target.val pivot.val column.val
      pivot.isLt target.isLt sourceValue (matrix target column) (-matrix target column) flag
  simp only [Bool.false_eq_true, ite_false] at loaded rowTrace
  rw [MatrixRowField.add_transform] at rowTrace
  have first := sequence_steps _ _ false readTrace readTarget_halt loaded
  have complete := sequence_steps _ _ MatrixRows.entry first
    (by intro symbols; simp [MultiTape.sequence, loadCoefficient_halt]) rowTrace
  refine ⟨_, finalSource, finalTarget, ?_, complete⟩
  have targetBound := target.isLt
  have columnBound := column.isLt
  have product := Nat.mul_le_mul_right columns targetBound.le
  dsimp [rowBound]
  nlinarith

private def clearedPrefix (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) (processed : ℕ) : Matrix (Fin rows) (Fin columns) Scalar :=
  fun row other => if row.val < processed then MatrixOperations.clearColumn matrix pivot column row other else matrix row other

private theorem prefix_zero (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) : clearedPrefix matrix pivot column 0 = matrix := by
  ext row other
  simp [clearedPrefix]

private theorem prefix_complete (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) :
    clearedPrefix matrix pivot column rows = MatrixOperations.clearColumn matrix pivot column := by
  ext row other
  simp [clearedPrefix, row.isLt]

private theorem prefix_pivot (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) (processed : ℕ) (other : Fin columns) :
    clearedPrefix matrix pivot column processed pivot other = matrix pivot other := by
  simp [clearedPrefix]

private theorem prefix_next (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot target : Fin rows) (column : Fin columns) (distinct : target ≠ pivot) :
    Function.update (clearedPrefix matrix pivot column target.val) target
      (fun other => clearedPrefix matrix pivot column target.val target other +
        (-clearedPrefix matrix pivot column target.val target column) *
          clearedPrefix matrix pivot column target.val pivot other) =
      clearedPrefix matrix pivot column (target.val + 1) := by
  ext row other
  by_cases same : row = target
  · subst row
    simp [Function.update, clearedPrefix, MatrixOperations.clearColumn, MatrixOperations.addPivotRow, distinct]
  · have unequal : row.val ≠ target.val := by intro equal; exact same (Fin.ext equal)
    have before : row.val < target.val + 1 ↔ row.val < target.val := by omega
    simp [Function.update, same, clearedPrefix, before]

private theorem prefix_skip (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (pivot : Fin rows) (column : Fin columns) :
    clearedPrefix matrix pivot column pivot.val = clearedPrefix matrix pivot column (pivot.val + 1) := by
  ext row other
  by_cases same : row = pivot
  · subst row; simp [clearedPrefix]
  · have unequal : row.val ≠ pivot.val := by intro equal; exact same (Fin.ext equal)
    have before : row.val < pivot.val + 1 ↔ row.val < pivot.val := by omega
    simp [clearedPrefix, before]

abbrev BodyState := Sum ClearState (Fin 3)

noncomputable def body : Machine (Alphabet Scalar) BodyState := sequence clearTarget (targetCounter false) 0

def bodyEntry : BodyState := .inl clearEntry
def bodyExit : BodyState := .inr 2

private theorem clearTarget_halt (symbols : Symbols (Alphabet Scalar)) : clearTarget clearExit symbols = none := by
  simp [clearTarget, clearExit, MultiTape.sequence, rowOperation_halt]

private theorem body_halt (symbols : Symbols (Alphabet Scalar)) : body bodyExit symbols = none := by
  simp [body, bodyExit, MultiTape.sequence, targetCounter_halt]

private theorem body_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (target pivot : Fin rows) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget, ticks ≤ rowBound rows columns + 2 * rows + 4 ∧
      Steps body ticks
        (bodyEntry, frame matrix candidate target.val pivot.val column.val sourceValue targetValue coefficient flag)
        (bodyExit, frame (Function.update matrix target
          (fun other => matrix target other + (-matrix target column) * matrix pivot other))
          candidate (target.val + 1) pivot.val column.val finalSource finalTarget (-matrix target column) false) := by
  obtain ⟨ticks, finalSource, finalTarget, cost, trace⟩ :=
    clearTarget_steps matrix candidate target pivot column sourceValue targetValue coefficient flag
  have advanced := advanceTarget_steps (Function.update matrix target
    (fun other => matrix target other + (-matrix target column) * matrix pivot other))
    candidate target.val pivot.val column.val finalSource finalTarget (-matrix target column) false
  refine ⟨ticks + (2 * target.val + 3) + 1, finalSource, finalTarget, ?_,
    sequence_steps _ _ 0 trace clearTarget_halt advanced⟩
  have targetBound := target.isLt
  omega

/-- Traverse one interval that excludes the pivot, retaining the prefix invariant. -/
private theorem interval_steps (untilRows : Bool) (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (pivot : Fin rows) (column : Fin columns) (start : ℕ)
    (bounded : start ≤ if untilRows then rows else pivot.val)
    (distinct : ∀ row : Fin rows, start ≤ row.val → row.val < (if untilRows then rows else pivot.val) → row ≠ pivot)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget finalCoefficient,
      ticks ≤ ((if untilRows then rows else pivot.val) - start + 1) * (rowBound rows columns + 4 * rows + 9) ∧
      Steps (whileMachine (compare false untilRows) body 0 bodyEntry result) ticks
        (.inl 0, frame (clearedPrefix matrix pivot column start)
          candidate start pivot.val column.val sourceValue targetValue coefficient flag)
        (.inl 2, frame (clearedPrefix matrix pivot column (if untilRows then rows else pivot.val))
          candidate (if untilRows then rows else pivot.val) pivot.val column.val
            finalSource finalTarget finalCoefficient false) := by
  let finish := if untilRows then rows else pivot.val
  have finishBound : finish ≤ rows := by dsimp [finish]; split <;> omega
  generalize ranking : finish - start = remaining
  induction remaining using Nat.strong_induction_on generalizing start sourceValue targetValue coefficient flag with
  | h remaining hypothesis =>
    have comparison := compare_steps false untilRows (clearedPrefix matrix pivot column start)
      candidate start pivot.val column.val sourceValue targetValue coefficient flag
    simp only [Bool.false_eq_true, ite_false] at comparison
    have liftedGuard := comparison.rename Sum.inl
      (target := whileMachine (compare false untilRows) body 0 bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    by_cases active : start < finish
    · have valid : start < rows := lt_of_lt_of_le active finishBound
      let target : Fin rows := ⟨start, valid⟩
      let current := clearedPrefix matrix pivot column start
      have different : target ≠ pivot := distinct target (by rfl) active
      obtain ⟨bodyTicks, nextSource, nextTarget, bodyCost, bodyTrace⟩ :=
        body_steps current candidate target pivot column sourceValue targetValue coefficient true
      have nextMatrix := prefix_next matrix pivot target column different
      change Function.update current target (fun other => current target other + (-current target column) * current pivot other) =
        clearedPrefix matrix pivot column (start + 1) at nextMatrix
      rw [nextMatrix] at bodyTrace
      have liftedBody := bodyTrace.rename Sum.inr
        (target := whileMachine (compare false untilRows) body 0 bodyEntry result)
        (by intro state symbols next actions transition; simp [whileMachine, transition])
      obtain ⟨restTicks, finalSource, finalTarget, finalCoefficient, restCost, restTrace⟩ :=
        hypothesis (finish - (start + 1)) (by omega) (start + 1) (by omega)
          (by intro row lower upper; exact distinct row (by omega) upper)
          nextSource nextTarget (-current target column) false rfl
      have tested : decide (start < (if untilRows then rows else pivot.val)) = true := by
        exact decide_eq_true active
      rw [tested] at liftedGuard
      have toBody : step (whileMachine (compare false untilRows) body 0 bodyEntry result)
          (.inl 2, frame current candidate start pivot.val column.val sourceValue targetValue coefficient true) =
          some (.inr bodyEntry, frame current candidate start pivot.val column.val sourceValue targetValue coefficient true) := by
        simp [step, whileMachine, compare_halt]
      have toGuard : step (whileMachine (compare false untilRows) body 0 bodyEntry result)
          (.inr bodyExit, frame (clearedPrefix matrix pivot column (start + 1))
            candidate (start + 1) pivot.val column.val nextSource nextTarget (-current target column) false) =
          some (.inl 0, frame (clearedPrefix matrix pivot column (start + 1))
            candidate (start + 1) pivot.val column.val nextSource nextTarget (-current target column) false) := by
        simp [step, whileMachine, body_halt]
      have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      refine ⟨_, finalSource, finalTarget, finalCoefficient, ?_, trace⟩
      have minimum := Nat.min_le_right start finish
      have stepCost : (2 * min start finish + 3) + bodyTicks + 2 ≤ rowBound rows columns + 4 * rows + 9 := by omega
      have split : finish - start + 1 = (finish - (start + 1) + 1) + 1 := by omega
      rw [← ranking, split, Nat.add_mul, one_mul]
      change 2 * min start finish + 3 + (bodyTicks + (restTicks + 1) + 1) ≤ _
      omega
    · have finalIndex : start = finish := by omega
      subst start
      have tested : decide (finish < (if untilRows then rows else pivot.val)) = false := by simp [finish]
      rw [tested] at liftedGuard
      refine ⟨2 * min finish finish + 3, sourceValue, targetValue, coefficient, ?_, liftedGuard⟩
      have dominates := Nat.mul_le_mul_right (rowBound rows columns + 4 * rows + 9)
        (show 1 ≤ remaining + 1 by omega)
      simp only [one_mul, min_self] at dominates ⊢
      omega

abbrev IntervalState := Sum (Sum (Fin 3) BodyState) Unit

-- Cache the finite enumeration before using the interval controller twice.
instance intervalStatesFinite : Fintype IntervalState := inferInstance

noncomputable def interval (untilRows : Bool) : Machine (Alphabet Scalar) IntervalState :=
  withExit (whileMachine (compare false untilRows) body 0 bodyEntry result)

abbrev State := Sum (Sum (Sum IntervalState (Fin 3)) IntervalState) (Fin 3)

instance statesFinite : Fintype State := inferInstance

noncomputable def machine : Machine (Alphabet Scalar) State :=
  sequence (sequence (sequence (interval false) (targetCounter false) 0)
    (interval true) (.inl (.inl 0))) (targetCounter true) 0

def entry : State := .inl (.inl (.inl (.inl (.inl 0))))
def exit : State := .inr 2

/-- Clear all rows except the pivot and restore the target counter to zero. -/
theorem steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (pivot : Fin rows) (column : Fin columns)
    (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalSource finalTarget finalCoefficient,
      ticks ≤ 2 * (rows + 1) * (rowBound rows columns + 4 * rows + 9) + 4 * rows + 11 ∧
      Steps machine ticks
        (entry, frame matrix candidate 0 pivot.val column.val sourceValue targetValue coefficient flag)
        (exit, frame (MatrixOperations.clearColumn matrix pivot column)
          candidate 0 pivot.val column.val finalSource finalTarget finalCoefficient false) := by
  obtain ⟨lowerTicks, middleSource, middleTarget, middleCoefficient, lowerCost, lowerTrace⟩ :=
    interval_steps false matrix candidate pivot column 0 (by simp)
      (by intro row _ upper equal; subst row; simp at upper) sourceValue targetValue coefficient flag
  simp only [Bool.false_eq_true, ite_false, prefix_zero] at lowerTrace lowerCost
  have lowerHalt : step (whileMachine (compare false false) body 0 bodyEntry result)
      (.inl 2, frame (clearedPrefix matrix pivot column pivot.val)
        candidate pivot.val pivot.val column.val middleSource middleTarget middleCoefficient false) = none := by
    simp [step, whileMachine, compare_halt]
  have lowerRun := withExit_steps _ lowerTrace lowerHalt
  have skipped := advanceTarget_steps (clearedPrefix matrix pivot column pivot.val)
    candidate pivot.val pivot.val column.val middleSource middleTarget middleCoefficient false
  obtain ⟨upperTicks, finalSource, finalTarget, finalCoefficient, upperCost, upperTrace⟩ :=
    interval_steps true matrix candidate pivot column (pivot.val + 1) (by simp)
      (by intro row lower _ equal; subst row; omega) middleSource middleTarget middleCoefficient false
  simp only [ite_true, prefix_complete] at upperTrace upperCost
  have upperHalt : step (whileMachine (compare false true) body 0 bodyEntry result)
      (.inl 2, frame (MatrixOperations.clearColumn matrix pivot column)
        candidate rows pivot.val column.val finalSource finalTarget finalCoefficient false) = none := by
    simp [step, whileMachine, compare_halt]
  have upperRun := withExit_steps _ upperTrace upperHalt
  have first := sequence_steps _ _ 0 lowerRun (by intro symbols; rfl) skipped
  rw [prefix_skip] at first
  have second := sequence_steps _ (interval true) (.inl (.inl 0)) first
    (by intro symbols; simp [MultiTape.sequence, targetCounter_halt]) upperRun
  have complete := sequence_steps _ _ 0 second (by intro symbols; rfl)
    (resetTarget_steps (MatrixOperations.clearColumn matrix pivot column)
      candidate rows pivot.val column.val finalSource finalTarget finalCoefficient false)
  refine ⟨_, finalSource, finalTarget, finalCoefficient, ?_, complete⟩
  have pivotBound := pivot.isLt
  have lowerBound := Nat.mul_le_mul_right (rowBound rows columns + 4 * rows + 9)
    (show pivot.val - 0 + 1 ≤ rows + 1 by omega)
  have upperBound := Nat.mul_le_mul_right (rowBound rows columns + 4 * rows + 9)
    (show rows - (pivot.val + 1) + 1 ≤ rows + 1 by omega)
  rw [Nat.mul_assoc, Nat.two_mul]
  omega

theorem realizes [Fintype Scalar] :
    Realizes (machine (Scalar := Scalar)) entry exit
      (fun assignment initial =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (candidate : ℕ) (pivot : Fin (assignment false)) (column : Fin (assignment true))
          (sourceValue targetValue coefficient : Scalar) (flag : Bool),
          candidate ≤ assignment false ∧
          initial = frame matrix candidate 0 pivot.val column.val sourceValue targetValue coefficient flag)
      (fun assignment initial final =>
        ∀ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (candidate : ℕ) (pivot : Fin (assignment false)) (column : Fin (assignment true))
          (sourceValue targetValue coefficient : Scalar) (flag : Bool),
          initial = frame matrix candidate 0 pivot.val column.val sourceValue targetValue coefficient flag →
          ∃ finalSource finalTarget finalCoefficient,
            final = frame (MatrixOperations.clearColumn matrix pivot column)
              candidate 0 pivot.val column.val finalSource finalTarget finalCoefficient false) := by
  let rowCost : MvPolynomial Bool ℕ :=
    (MvPolynomial.X true + 1) *
      (28 * MvPolynomial.X false * MvPolynomial.X true + 36 * MvPolynomial.X false + 32 * MvPolynomial.X true + 94) +
      2 * MvPolynomial.X true + 5 + 7 * MvPolynomial.X false * MvPolynomial.X true +
        9 * MvPolynomial.X false + 7 * MvPolynomial.X true + 23
  refine ⟨by intro symbols; rfl,
    2 * (MvPolynomial.X false + 1) * (rowCost + 4 * MvPolynomial.X false + 9) +
      4 * MvPolynomial.X false + 11, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, candidate, pivot, column, sourceValue, targetValue, coefficient, flag, _, rfl⟩ := valid
  obtain ⟨ticks, finalSource, finalTarget, finalCoefficient, cost, trace⟩ :=
    steps matrix candidate pivot column sourceValue targetValue coefficient flag
  refine ⟨ticks, _, ?_, trace, ?_⟩
  · simpa only [rowCost, rowBound, map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using cost
  · intro otherMatrix otherCandidate otherPivot otherColumn otherSourceValue otherTargetValue otherCoefficient otherFlag equal
    obtain ⟨otherTicks, otherFinalSource, otherFinalTarget, otherFinalCoefficient, _, otherTrace⟩ :=
      steps otherMatrix otherCandidate otherPivot otherColumn otherSourceValue otherTargetValue otherCoefficient otherFlag
    rw [← equal] at otherTrace
    exact ⟨otherFinalSource, otherFinalTarget, otherFinalCoefficient,
      congrArg Prod.snd (trace.final_eq otherTrace rfl rfl)⟩

end Polytime2.GaussJordanClear
