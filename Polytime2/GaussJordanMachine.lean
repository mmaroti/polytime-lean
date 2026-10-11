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


import Polytime2.GaussJordanColumn

/-! # Complete multi-tape Gauss–Jordan elimination

The outer guard compares the saved column counter with the column count.
Its body performs one certified column step and advances the column. Empty
rectangular matrices use the same finite program and guard conventions.
-/

namespace Polytime2.GaussJordanMachine

open MultiTape GaussJordanWorkspace

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {rows columns : ℕ}

abbrev BodyState := Sum GaussJordanColumn.State (Fin 3)

noncomputable def body : Machine (Alphabet Scalar) BodyState :=
  sequence GaussJordanColumn.machine (advancePivot true) 0

def bodyEntry : BodyState := .inl GaussJordanColumn.entry
def bodyExit : BodyState := .inr 2

abbrev State := Sum (Sum (Fin 3) BodyState) Unit

instance statesFinite : Fintype State := inferInstance

noncomputable def machine : Machine (Alphabet Scalar) State :=
  withExit (whileMachine compareColumn body 0 bodyEntry result)

def entry : State := .inl (.inl 0)
def exit : State := .inr ()

def bound (rows columns : ℕ) : ℕ :=
  (columns + 1) * (GaussJordanColumn.bound rows columns + 4 * columns + 9) + 1

private theorem body_halt (symbols : Symbols (Alphabet Scalar)) : body bodyExit symbols = none := by
  simp [body, bodyExit, MultiTape.sequence, advancePivot_halt]

private theorem body_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate pivotRow : ℕ) (candidateBound : candidate ≤ rows) (pivotBound : pivotRow ≤ rows)
    (column : Fin columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalCandidate finalSource finalTarget finalCoefficient,
      ticks ≤ GaussJordanColumn.bound rows columns + 2 * columns + 4 ∧
      Steps body ticks
        (bodyEntry, frame matrix candidate 0 pivotRow column.val sourceValue targetValue coefficient flag)
        (bodyExit, frame (GaussJordan.columnStep matrix pivotRow column).1 finalCandidate 0
          (GaussJordan.columnStep matrix pivotRow column).2 (column.val + 1) finalSource finalTarget finalCoefficient false) ∧
      finalCandidate ≤ rows := by
  obtain ⟨ticks, finalCandidate, finalSource, finalTarget, finalCoefficient, cost, trace, finalBound⟩ :=
    GaussJordanColumn.steps matrix candidate pivotRow candidateBound pivotBound column sourceValue targetValue coefficient flag
  have advanced := advancePivot_steps true (GaussJordan.columnStep matrix pivotRow column).1 finalCandidate 0
    (GaussJordan.columnStep matrix pivotRow column).2 column.val finalSource finalTarget finalCoefficient false
  simp only [ite_true] at advanced
  refine ⟨ticks + (2 * column.val + 3) + 1, finalCandidate, finalSource, finalTarget, finalCoefficient,
    ?_, sequence_steps _ _ 0 trace GaussJordanColumn.halt advanced, finalBound⟩
  have columnBound := column.isLt
  omega

private theorem drop_columns (start : ℕ) (valid : start < columns) :
    (List.finRange columns).drop start = ⟨start, valid⟩ :: (List.finRange columns).drop (start + 1) := by
  have dropped := List.drop_eq_getElem_cons (l := List.finRange columns) (by simpa using valid)
  rw [List.getElem_finRange] at dropped
  exact dropped

/-- The guard-driven execution agrees with the mathematical suffix traversal. -/
private theorem loop_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate pivotRow start : ℕ) (candidateBound : candidate ≤ rows) (pivotBound : pivotRow ≤ rows)
    (startBound : start ≤ columns) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∃ ticks finalCandidate finalSource finalTarget finalCoefficient,
      ticks ≤ (columns - start + 1) * (GaussJordanColumn.bound rows columns + 4 * columns + 9) ∧
      Steps (whileMachine compareColumn body 0 bodyEntry result) ticks
        (.inl 0, frame matrix candidate 0 pivotRow start sourceValue targetValue coefficient flag)
        (.inl 2, frame (GaussJordan.eliminateColumns matrix pivotRow ((List.finRange columns).drop start)).1
          finalCandidate 0 (GaussJordan.eliminateColumns matrix pivotRow ((List.finRange columns).drop start)).2
            columns finalSource finalTarget finalCoefficient false) ∧
      finalCandidate ≤ rows := by
  generalize ranking : columns - start = remaining
  induction remaining using Nat.strong_induction_on generalizing matrix candidate pivotRow start sourceValue targetValue coefficient flag with
  | h remaining hypothesis =>
    have comparison := compareColumn_steps matrix candidate 0 pivotRow start sourceValue targetValue coefficient flag
    have liftedGuard := comparison.rename Sum.inl
      (target := whileMachine compareColumn body 0 bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    by_cases active : start < columns
    · simp only [active, decide_true] at liftedGuard
      let column : Fin columns := ⟨start, active⟩
      let next := GaussJordan.columnStep matrix pivotRow column
      obtain ⟨bodyTicks, nextCandidate, nextSource, nextTarget, nextCoefficient, bodyCost, bodyTrace, nextBound⟩ :=
        body_steps matrix candidate pivotRow candidateBound pivotBound column sourceValue targetValue coefficient true
      have liftedBody := bodyTrace.rename Sum.inr
        (target := whileMachine compareColumn body 0 bodyEntry result)
        (by intro state symbols nextState actions transition; simp [whileMachine, transition])
      obtain ⟨restTicks, finalCandidate, finalSource, finalTarget, finalCoefficient, restCost, restTrace, finalBound⟩ :=
        hypothesis (columns - (start + 1)) (by omega) next.1 nextCandidate next.2 (start + 1) nextBound
          (GaussJordan.columnStep_row_bound matrix pivotRow column pivotBound).2 (by omega)
          nextSource nextTarget nextCoefficient false rfl
      have toBody : step (whileMachine compareColumn body 0 bodyEntry result)
          (.inl 2, frame matrix candidate 0 pivotRow start sourceValue targetValue coefficient true) =
          some (.inr bodyEntry, frame matrix candidate 0 pivotRow start sourceValue targetValue coefficient true) := by
        simp [step, whileMachine, compareColumn_halt]
      have toGuard : step (whileMachine compareColumn body 0 bodyEntry result)
          (.inr bodyExit, frame next.1 nextCandidate 0 next.2 (start + 1) nextSource nextTarget nextCoefficient false) =
          some (.inl 0, frame next.1 nextCandidate 0 next.2 (start + 1) nextSource nextTarget nextCoefficient false) := by
        simp [step, whileMachine, body_halt]
      have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      have value : GaussJordan.eliminateColumns matrix pivotRow ((List.finRange columns).drop start) =
          GaussJordan.eliminateColumns next.1 next.2 ((List.finRange columns).drop (start + 1)) := by
        rw [drop_columns start active]
        rfl
      refine ⟨_, finalCandidate, finalSource, finalTarget, finalCoefficient, ?_,
        by simpa only [value] using trace, finalBound⟩
      · have minimum := Nat.min_le_right start columns
        have stepCost : 2 * min start columns + 3 + bodyTicks + 2 ≤
            GaussJordanColumn.bound rows columns + 4 * columns + 9 := by omega
        have split : columns - start + 1 = (columns - (start + 1) + 1) + 1 := by omega
        rw [← ranking, split, Nat.add_mul, one_mul]
        omega
    · have finalIndex : start = columns := by omega
      subst start
      simp only [lt_self_iff_false, decide_false] at liftedGuard
      refine ⟨2 * min columns columns + 3, candidate, sourceValue, targetValue, coefficient, ?_, ?_, candidateBound⟩
      · have dominates := Nat.mul_le_mul_right (GaussJordanColumn.bound rows columns + 4 * columns + 9)
          (show 1 ≤ remaining + 1 by omega)
        simp only [one_mul, min_self] at dominates ⊢
        omega
      · have empty : (List.finRange columns).drop columns = [] := by
          exact List.drop_eq_nil_of_le (by simp)
        simpa only [empty, GaussJordan.eliminateColumns] using liftedGuard

/-- Complete elimination in a prepared frame, with its mathematical output and runtime bound. -/
theorem steps (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    ∃ ticks candidate rank sourceValue targetValue coefficient,
      ticks ≤ bound rows columns ∧
      Steps machine ticks (entry, frame matrix 0 0 0 0 0 0 0 false)
        (exit, frame (GaussJordan.eliminate matrix) candidate 0 rank columns sourceValue targetValue coefficient false) ∧
      candidate ≤ rows ∧ rank ≤ rows ∧
      Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧ Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) := by
  obtain ⟨ticks, candidate, sourceValue, targetValue, coefficient, cost, trace, candidateBound⟩ :=
    loop_steps matrix 0 0 0 (by omega) (by omega) (by omega) 0 0 0 false
  simp only [List.drop_zero, Nat.sub_zero] at trace cost
  let rank := (GaussJordan.eliminateColumns matrix 0 (List.finRange columns)).2
  have halted : step (whileMachine compareColumn body 0 bodyEntry result)
      (.inl 2, frame (GaussJordan.eliminate matrix) candidate 0 rank columns sourceValue targetValue coefficient false) = none := by
    simp [step, whileMachine, compareColumn_halt]
  exact ⟨ticks + 1, candidate, rank, sourceValue, targetValue, coefficient,
    by dsimp [bound]; omega, withExit_steps _ trace halted, candidateBound,
    (GaussJordan.eliminateColumns_row_bound matrix 0 (List.finRange columns) (by omega)).2,
    GaussJordan.rowEquivalent matrix, GaussJordan.reducedRowEchelon matrix⟩


/-- Internal runtime witness shared by prepared and external realization. -/
noncomputable def runtimePolynomial : MvPolynomial Bool ℕ :=
  let rowCount : MvPolynomial Bool ℕ := MvPolynomial.X false
  let columnCount : MvPolynomial Bool ℕ := MvPolynomial.X true
  let rowCost := (columnCount + 1) *
    (28 * rowCount * columnCount + 36 * rowCount + 32 * columnCount + 94) + 2 * columnCount + 5
  let clearCost := 2 * (rowCount + 1) *
    (rowCost + 7 * rowCount * columnCount + 9 * rowCount + 7 * columnCount + 23 + 4 * rowCount + 9) +
    4 * rowCount + 11
  let pivotCost := 2 * rowCost + clearCost + 4
  let columnCost := (rowCount + 1) * (7 * rowCount * columnCount + 13 * rowCount + 7 * columnCount + 33) +
    1 + pivotCost + 9 * rowCount + 23
  (columnCount + 1) * (columnCost + 4 * columnCount + 9) + 1

omit [Field Scalar] [DecidableEq Scalar] in
theorem eval_runtimePolynomial (assignment : Bool → ℕ) :
    MvPolynomial.eval assignment runtimePolynomial = bound (assignment false) (assignment true) := by
  simp only [runtimePolynomial, bound, GaussJordanColumn.bound, GaussJordanPivot.bound, GaussJordanClear.rowBound,
    map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X]

/-- A single finite program and polynomial work for every rectangular dimension. -/
theorem realizes [Fintype Scalar] :
    Realizes (machine (Scalar := Scalar)) entry exit
      (fun assignment initial =>
        ∃ matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar,
          initial = frame matrix 0 0 0 0 0 0 0 false)
      (fun assignment initial final =>
        ∀ matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar,
          initial = frame matrix 0 0 0 0 0 0 0 false →
          ∃ candidate rank sourceValue targetValue coefficient,
            final = frame (GaussJordan.eliminate matrix) candidate 0 rank (assignment true)
              sourceValue targetValue coefficient false ∧
            candidate ≤ assignment false ∧ rank ≤ assignment false ∧
            Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧
            Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix)) := by
  refine ⟨by intro symbols; rfl, runtimePolynomial, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, rfl⟩ := valid
  obtain ⟨ticks, candidate, rank, sourceValue, targetValue, coefficient, cost, trace, bounds⟩ := steps matrix
  refine ⟨ticks, _, ?_, trace, ?_⟩
  · simpa only [eval_runtimePolynomial] using cost
  · intro otherMatrix equal
    obtain ⟨otherTicks, otherCandidate, otherRank, otherSource, otherTarget, otherCoefficient,
      _, otherTrace, otherBounds⟩ := steps otherMatrix
    rw [← equal] at otherTrace
    exact ⟨otherCandidate, otherRank, otherSource, otherTarget, otherCoefficient,
      congrArg Prod.snd (trace.final_eq otherTrace rfl rfl), otherBounds⟩

theorem halt (symbols : Symbols (Alphabet Scalar)) : machine exit symbols = none := by rfl

end Polytime2.GaussJordanMachine
