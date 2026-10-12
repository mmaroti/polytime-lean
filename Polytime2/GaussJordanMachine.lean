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
import Polytime2.Fold

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

/-- Only the current column, matrix, and pivot row are logical state. -/
abbrev Value (Scalar : Type) (rows columns : ℕ) :=
  ℕ × (Matrix (Fin rows) (Fin columns) Scalar × ℕ)

def valid (value : Value Scalar rows columns) : Prop :=
  value.1 ≤ columns ∧ value.2.2 ≤ rows

def advance (value : Value Scalar rows columns) : Value Scalar rows columns :=
  if active : value.1 < columns then
    (value.1 + 1, GaussJordan.columnStep value.2.1 value.2.2 ⟨value.1, active⟩)
  else value

/-- Candidate and scalar scratch are existential; they are not fold components. -/
def representation (value : Value Scalar rows columns) (tapes : Tapes (Alphabet Scalar)) : Prop :=
  ∃ candidate sourceValue targetValue coefficient flag,
    candidate ≤ rows ∧
      tapes = frame value.2.1 candidate 0 value.2.2 value.1 sourceValue targetValue coefficient flag

def guardedRepresentation (value : Value Scalar rows columns) (tapes : Tapes (Alphabet Scalar)) : Prop :=
  representation value tapes ∧ result (read tapes) = decide (value.1 < columns)

omit [Field Scalar] [DecidableEq Scalar] in
private theorem guard_runs (value : Value Scalar rows columns) (initial : Tapes (Alphabet Scalar))
    (_valid : valid value) (represented : representation value initial) :
    ∃ ticks final, ticks ≤ 2 * columns + 3 ∧
      Steps compareColumn ticks (0, initial) (2, final) ∧ guardedRepresentation value final := by
  obtain ⟨candidate, sourceValue, targetValue, coefficient, flag, bounded, rfl⟩ := represented
  refine ⟨_, _, ?_, compareColumn_steps value.2.1 candidate 0 value.2.2 value.1
    sourceValue targetValue coefficient flag, ?_, by simp⟩
  · have minimum := Nat.min_le_right value.1 columns; omega
  · exact ⟨candidate, sourceValue, targetValue, coefficient, _, bounded, rfl⟩

private theorem body_runs (value : Value Scalar rows columns) (initial : Tapes (Alphabet Scalar))
    (bounded : valid value) (active : value.1 < columns) (represented : guardedRepresentation value initial) :
    ∃ ticks final, ticks ≤ GaussJordanColumn.bound rows columns + 2 * columns + 4 ∧
      Steps body ticks (bodyEntry, initial) (bodyExit, final) ∧ representation (advance value) final := by
  obtain ⟨candidate, sourceValue, targetValue, coefficient, flag, candidateBound, rfl⟩ := represented.1
  obtain ⟨ticks, finalCandidate, finalSource, finalTarget, finalCoefficient, cost, trace, finalBound⟩ :=
    body_steps value.2.1 candidate value.2.2 candidateBound bounded.2 ⟨value.1, active⟩
      sourceValue targetValue coefficient flag
  refine ⟨ticks, _, cost, trace, ?_⟩
  exact ⟨finalCandidate, finalSource, finalTarget, finalCoefficient, false, finalBound, by simp [advance, active]⟩

private theorem advance_valid (value : Value Scalar rows columns) (bounded : valid value)
    (active : value.1 < columns) : valid (advance value) := by
  have rowBound := (GaussJordan.columnStep_row_bound value.2.1 value.2.2 ⟨value.1, active⟩ bounded.2).2
  simp only [valid, advance, dite_eq_left active]
  exact ⟨by omega, rowBound⟩

private def remaining (value : Value Scalar rows columns) :=
  GaussJordan.eliminateColumns value.2.1 value.2.2 ((List.finRange columns).drop value.1)

private theorem remaining_advance (value : Value Scalar rows columns) :
    remaining (advance value) = remaining value := by
  by_cases active : value.1 < columns
  · simp only [remaining, advance, dite_eq_left active, drop_columns value.1 active,
      GaussJordan.eliminateColumns]
  · simp only [advance, dite_eq_right active]

private theorem remaining_iterate (value : Value Scalar rows columns) (count : ℕ) :
    remaining (advance^[count] value) = remaining value := by
  induction count with
  | zero => rfl
  | succ count hypothesis => rw [Function.iterate_succ_apply', remaining_advance, hypothesis]

/-- A generic mathematical fold supplies the physical traversal and its cost. -/
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
  let initialValue : Value Scalar rows columns := (start, matrix, pivotRow)
  obtain ⟨ticks, final, cost, trace, represented, finalValid, finalIndex⟩ :=
    fold_steps compareColumn body 0 2 bodyEntry bodyExit result representation guardedRepresentation
      columns Prod.fst valid advance (2 * columns + 3) (GaussJordanColumn.bound rows columns + 2 * columns + 4)
      compareColumn_halt body_halt guard_runs body_runs
      (by intro value tapes encoded; exact encoded.2)
      (by intro value bounded; exact bounded.1) advance_valid
      (by intro value _ active; simp [advance, active])
      initialValue (frame matrix candidate 0 pivotRow start sourceValue targetValue coefficient flag)
      ⟨startBound, pivotBound⟩ ⟨candidate, sourceValue, targetValue, coefficient, flag, candidateBound, rfl⟩
  let finalValue := advance^[columns - start] initialValue
  change finalValue.1 = columns at finalIndex
  have finalPair : finalValue.2 = remaining initialValue := by
    have preserved := remaining_iterate initialValue (columns - start)
    change remaining finalValue = remaining initialValue at preserved
    have empty : (List.finRange columns).drop columns = [] := List.drop_eq_nil_of_le (by simp)
    simpa only [remaining, finalIndex, empty, GaussJordan.eliminateColumns] using preserved
  have finalValue_eq : finalValue = (columns, remaining initialValue) := Prod.ext finalIndex finalPair
  change guardedRepresentation finalValue final at represented
  obtain ⟨finalCandidate, finalSource, finalTarget, finalCoefficient, finalFlag, finalBound, encoded⟩ := represented.1
  have stopped : finalFlag = false := by
    have tested := represented.2
    rw [encoded, result_frame, finalIndex] at tested
    simpa using tested
  subst finalFlag
  rw [finalValue_eq] at encoded
  refine ⟨ticks, finalCandidate, finalSource, finalTarget, finalCoefficient, ?_, ?_, finalBound⟩
  · dsimp only [initialValue] at cost
    convert cost using 1; ring
  · simpa only [encoded, remaining, initialValue] using trace

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


/-- Cost of a column operation, internal to the representation adapters. -/
noncomputable def columnPolynomial : MvPolynomial Bool ℕ :=
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
  columnCost

omit [Field Scalar] [DecidableEq Scalar] in
private theorem eval_columnPolynomial (assignment : Bool → ℕ) :
    MvPolynomial.eval assignment columnPolynomial = GaussJordanColumn.bound (assignment false) (assignment true) := by
  simp only [columnPolynomial, GaussJordanColumn.bound, GaussJordanPivot.bound, GaussJordanClear.rowBound,
    map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X]

/-- Internal runtime witness shared by prepared and external realization. -/
noncomputable def runtimePolynomial : MvPolynomial Bool ℕ :=
  (MvPolynomial.X true + 1) * (columnPolynomial + 4 * MvPolynomial.X true + 9) + 1

omit [Field Scalar] [DecidableEq Scalar] in
theorem eval_runtimePolynomial (assignment : Bool → ℕ) :
    MvPolynomial.eval assignment runtimePolynomial = bound (assignment false) (assignment true) := by
  simp only [runtimePolynomial, bound, map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X,
    eval_columnPolynomial]

omit [Field Scalar] [DecidableEq Scalar] in
private theorem guard_contract [Fintype Scalar] :
    Computes (compareColumn (Scalar := Scalar)) 0 2
      (fun sizes : Bool → ℕ => representation (rows := sizes false) (columns := sizes true))
      (fun _ => guardedRepresentation) (fun _ => valid) (fun _ value => value) := by
  refine ⟨compareColumn_halt, 2 * MvPolynomial.X true + 3, ?_⟩
  intro sizes value initial bounded represented
  obtain ⟨ticks, final, cost, trace, encoded⟩ := guard_runs value initial bounded represented
  exact ⟨ticks, final, by simpa using cost, trace, encoded⟩

private theorem body_contract [Fintype Scalar] :
    Computes (body (Scalar := Scalar)) bodyEntry bodyExit
      (fun sizes : Bool → ℕ => guardedRepresentation (rows := sizes false) (columns := sizes true))
      (fun _ => representation) (fun sizes value => valid value ∧ value.1 < sizes true)
      (fun _ => advance) := by
  refine ⟨body_halt, columnPolynomial + 2 * MvPolynomial.X true + 4, ?_⟩
  intro sizes value initial bounded represented
  obtain ⟨ticks, final, cost, trace, encoded⟩ := body_runs value initial bounded.1 bounded.2 represented
  exact ⟨ticks, final, by simpa only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X,
    eval_columnPolynomial] using cost, trace, encoded⟩

/-- The algorithm-level traversal is a mathematical fold. Temporary scalars,
controller sums, handovers, and runtime witnesses remain inside library rules. -/
theorem traversal_contract [Fintype Scalar] :
    Computes (machine (Scalar := Scalar)) entry exit
      (fun sizes : Bool → ℕ => representation (rows := sizes false) (columns := sizes true))
      (fun sizes value tapes => guardedRepresentation value tapes ∧ valid value ∧ value.1 = sizes true)
      (fun _ => valid) (fun sizes value => advance^[sizes true - value.1] value) := by
  exact Computes.fold result _ _ (fun sizes => sizes true) (fun _ => Prod.fst)
    (fun _ => valid) (fun _ => advance) guard_contract body_contract
    (by intro sizes value tapes represented; exact represented.2)
    (by intro sizes value bounded; exact bounded.1)
    (by intro sizes value bounded active; exact advance_valid value bounded active)
    (by intro sizes value _ active; simp [advance, active])
    ⟨MvPolynomial.X true, by intro sizes; simp⟩

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
