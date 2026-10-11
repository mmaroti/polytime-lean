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


import Polytime2.UnaryCompare
import Polytime2.MatrixEntry
import Polytime2.GaussJordan
import Polytime2.Branch
import Polytime2.While

/-! # Guarded pivot search on a runtime matrix

The candidate may equal the row count. The guard checks its bound before
looking up an entry, and continues exactly while an eligible entry is zero.
-/

namespace Polytime2.PivotSearch

open MultiTape

variable {Scalar : Type} [Zero Scalar] [DecidableEq Scalar] {rows columns : ℕ}

/-- Matrix access tapes, followed by a row-limit counter and Boolean flag. -/
abbrev TapeName := Sum MatrixEntry.TapeName Bool

def Alphabet (Scalar : Type) : TapeName → Type
  | .inl name => MatrixEntry.Alphabet Scalar name
  | .inr _ => Binary.Symbol

instance (name : TapeName) : Inhabited (Alphabet Scalar name) :=
  match name with
  | .inl name => MatrixEntry.instInhabitedAlphabet name
  | .inr _ => (⟨0⟩ : Inhabited Binary.Symbol)

instance [Fintype Scalar] (name : TapeName) : Fintype (Alphabet Scalar name) :=
  match name with
  | .inl name => MatrixEntry.instFintypeAlphabet name
  | .inr _ => inferInstanceAs (Fintype Binary.Symbol)

def flagTape (flag : Bool) : Turing.Tape Binary.Symbol := Binary.tape [3] [Binary.data flag] ()

def frame (matrix : Matrix (Fin rows) (Fin columns) Scalar) (candidate : ℕ)
    (column : Fin columns) (element : Scalar) (flag : Bool) : Tapes (Alphabet Scalar)
  | .inl (.inl name) => MatrixAddress.ready candidate columns column.val 0 name
  | .inl (.inr false) => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]))
  | .inl (.inr true) => Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk [some (some element)])
  | .inr false => MatrixAddress.counter 0 rows
  | .inr true => flagTape flag

def compareWiring : UnaryCompare.TapeName ↪ TapeName where
  toFun
    | some false => .inl (.inl .row)
    | some true => .inr false
    | none => .inr true
  inj' := by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all

def compareEquivalences (Scalar : Type) (name : UnaryCompare.TapeName) :
    UnaryCompare.Alphabet name ≃ Alphabet Scalar (compareWiring name) := by
  cases name with
  | none => exact Equiv.refl _
  | some name => cases name <;> exact Equiv.refl _

omit [Zero Scalar] [DecidableEq Scalar] in
theorem compareBlanks (name : UnaryCompare.TapeName) :
    compareEquivalences Scalar name default = default := by
  cases name with
  | none => rfl
  | some name => cases name <;> rfl

noncomputable def compare : Machine (Alphabet Scalar) (Fin 3) :=
  wire compareWiring (relabel (compareEquivalences Scalar) UnaryCompare.machine)

noncomputable def readEntry : Machine (Alphabet Scalar) MatrixEntry.State :=
  wire Function.Embedding.inl (MatrixEntry.machine false)

def zeroTest : Machine (Alphabet Scalar) Bool :=
  HeadTable.machine (fun symbols name => match name with
    | .inr true => Binary.data (decide ((show TableTraversal.Symbol Scalar from symbols (.inl (.inr true))) = some (some 0)))
    | .inl localName => symbols (.inl localName)
    | .inr false => symbols (.inr false))

noncomputable def readTest : Machine (Alphabet Scalar) (Sum MatrixEntry.State Bool) :=
  sequence readEntry zeroTest false

def idle : Machine (Alphabet Scalar) Unit := fun _ _ => none

def result (symbols : Symbols (Alphabet Scalar)) : Bool := decide ((show Binary.Symbol from symbols (.inr true)) = 2)

abbrev SelectState := Sum (Sum Unit (Sum (Sum MatrixEntry.State Bool) Unit)) Unit

noncomputable def select : Machine (Alphabet Scalar) SelectState :=
  withExit (branchMachine result readTest idle (.inl MatrixEntry.entry) ())

abbrev GuardState := Sum (Fin 3) SelectState

noncomputable def guard : Machine (Alphabet Scalar) GuardState := sequence compare select (.inl (.inl ()))

def guardEntry : GuardState := .inl 0
def guardExit : GuardState := .inr (.inr ())

noncomputable def advance : Machine (Alphabet Scalar) (Fin 3) :=
  wire (oneTape (Sum.inl (Sum.inl MatrixAddress.TapeName.row) : TapeName)) (Unary.machine false)

abbrev State := Sum (Sum GuardState (Fin 3)) Unit

noncomputable def machine : Machine (Alphabet Scalar) State :=
  withExit (whileMachine guard advance guardEntry 0 result)

def entry : State := .inl (.inl guardEntry)
def exit : State := .inr ()

omit [Zero Scalar] [DecidableEq Scalar] in
private theorem compare_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (column : Fin columns) (element : Scalar) (flag : Bool) :
    Steps compare (2 * min candidate rows + 3)
      (0, frame matrix candidate column element flag)
      (2, frame matrix candidate column element (decide (candidate < rows))) := by
  have trace := (UnaryCompare.steps candidate rows (flagTape flag)).relabel
    (compareEquivalences Scalar) compareBlanks
  apply wire_steps_of_eq compareWiring _ trace
  · intro name
    cases name with
    | none =>
      change flagTape flag = (flagTape flag).map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol)
      exact (mapTape_identity _).symm
    | some name =>
      cases name <;>
        change MatrixAddress.counter 0 _ = (MatrixAddress.counter 0 _).map
          (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) <;>
        exact (mapTape_identity _).symm
  · intro name
    cases name with
    | none =>
      change flagTape (decide (candidate < rows)) =
        ((flagTape flag).write (Binary.data (decide (candidate < rows)))).map
          (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol)
      rw [mapTape_identity]
      simp [flagTape, Binary.tape, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
    | some name =>
      cases name <;>
        change MatrixAddress.counter 0 _ = (MatrixAddress.counter 0 _).map
          (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) <;>
        exact (mapTape_identity _).symm
  · intro name outside
    cases name with
    | inl name => cases name with
      | inl name => cases name <;> first
        | exact False.elim (outside ⟨some false, rfl⟩)
        | rfl
      | inr name => cases name <;> rfl
    | inr name => cases name with
      | false => exact False.elim (outside ⟨some true, rfl⟩)
      | true => exact False.elim (outside ⟨none, rfl⟩)

omit [Zero Scalar] [DecidableEq Scalar] in
private theorem read_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : Fin rows) (column : Fin columns) (element : Scalar) (flag : Bool) :
    Steps readEntry (7 * candidate.val * columns + 9 * candidate.val + 7 * column.val + 20)
      (MatrixEntry.entry, frame matrix candidate.val column element flag)
      (MatrixEntry.exit, frame matrix candidate.val column (matrix candidate column) flag) := by
  apply wire_steps_of_eq Function.Embedding.inl _ (MatrixEntry.steps false matrix candidate column element)
  · intro name; cases name with
    | inl name => cases name <;> rfl
    | inr name => cases name <;> rfl
  · intro name; cases name with
    | inl name => cases name <;> rfl
    | inr name => cases name <;> rfl
  · intro name outside
    cases name with
    | inl name => exact False.elim (outside ⟨name, rfl⟩)
    | inr name => cases name <;> rfl

private theorem zero_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (column : Fin columns) (element : Scalar) (flag : Bool) :
    Steps zeroTest 1
      (false, frame matrix candidate column element flag)
      (true, frame matrix candidate column element (decide (element = 0))) := by
  refine .next ?_ (.zero _)
  simp only [step, zeroTest, HeadTable.machine, Bool.false_eq_true, ite_false, Option.map_some]
  apply congrArg some
  apply Prod.ext
  · rfl
  funext name
  cases name with
  | inl name =>
    change (frame matrix candidate column element flag (.inl name)).write
      (frame matrix candidate column element flag (.inl name)).head = _
    have unchanged : frame matrix candidate column element flag (.inl name) =
        frame matrix candidate column element (decide (element = 0)) (.inl name) := by
      cases name with
      | inl name => cases name <;> rfl
      | inr name => cases name <;> rfl
    exact (Turing.Tape.write_self (frame matrix candidate column element flag (.inl name))).trans unchanged
  | inr name => cases name with
    | false =>
      change (MatrixAddress.counter 0 rows).write (MatrixAddress.counter 0 rows).head = _
      exact Turing.Tape.write_self (MatrixAddress.counter 0 rows)
    | true =>
      change (flagTape flag).write
        (Binary.data (decide (some (some element) = some (some (0 : Scalar))))) = flagTape (decide (element = 0))
      simp only [Option.some.injEq]
      simp only [flagTape, Binary.tape, Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
        List.tail_cons, Turing.ListBlank.cons_mk]


def continues (matrix : Matrix (Fin rows) (Fin columns) Scalar) (candidate : ℕ)
    (column : Fin columns) : Bool :=
  if valid : candidate < rows then decide (matrix ⟨candidate, valid⟩ column = 0) else false

def observed (matrix : Matrix (Fin rows) (Fin columns) Scalar) (candidate : ℕ)
    (column : Fin columns) (element : Scalar) : Scalar :=
  if valid : candidate < rows then matrix ⟨candidate, valid⟩ column else element

omit [Zero Scalar] [DecidableEq Scalar] in
@[simp] theorem result_frame (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (column : Fin columns) (element : Scalar) (flag : Bool) :
    result (read (frame matrix candidate column element flag)) = flag := by
  cases flag <;> simp [result, MultiTape.read, frame, flagTape, Binary.tape, Binary.data]

theorem guard_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (bounded : candidate ≤ rows) (column : Fin columns)
    (element : Scalar) (flag : Bool) :
    ∃ ticks, ticks ≤ 7 * rows * columns + 11 * rows + 7 * columns + 28 ∧
      Steps guard ticks (guardEntry, frame matrix candidate column element flag)
        (guardExit, frame matrix candidate column (observed matrix candidate column element)
          (continues matrix candidate column)) := by
  have comparison := compare_steps matrix candidate column element flag
  by_cases valid : candidate < rows
  · simp only [valid, decide_true] at comparison
    have readTrace := read_steps matrix ⟨candidate, valid⟩ column element true
    have tested := zero_steps matrix candidate column (matrix ⟨candidate, valid⟩ column) true
    have readTestTrace := sequence_steps readEntry zeroTest false readTrace
      (by intro symbols; simp [readEntry, wire, MatrixEntry.machine, MatrixEntry.exit, MultiTape.sequence, MatrixEntry.clearAddress, Unary.machine]; rfl) tested
    have selected := branch_steps_true result readTest idle (.inl MatrixEntry.entry) ()
      (by simp) readTestTrace (by intro symbols; simp [readTest, MultiTape.sequence, zeroTest, HeadTable.machine])
    have complete := sequence_steps compare select (.inl (.inl ())) comparison
      (by intro symbols; simp [compare, wire, relabel, UnaryCompare.machine]) selected
    refine ⟨_, ?_, by
      simpa only [guard, guardEntry, guardExit, select, observed, continues, valid, ↓reduceDIte] using complete⟩
    have product := Nat.mul_le_mul_right columns valid.le
    have columnBound := column.isLt
    have minimum := Nat.min_le_left candidate rows
    nlinarith
  · have selected := branch_steps_false result readTest idle (.inl MatrixEntry.entry) ()
      (initial := frame matrix candidate column element false)
      (by simp) (Steps.zero ((), frame matrix candidate column element false)) (by intro symbols; rfl)
    simp only [valid, decide_false] at comparison
    have complete := sequence_steps compare select (.inl (.inl ())) comparison
      (by intro symbols; simp [compare, wire, relabel, UnaryCompare.machine]) selected
    refine ⟨_, ?_, by
      simpa only [guard, guardEntry, guardExit, select, observed, continues, valid, ↓reduceDIte] using complete⟩
    have minimum := Nat.min_le_right candidate rows
    omega

omit [Zero Scalar] [DecidableEq Scalar] in
private theorem advance_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (candidate : ℕ) (column : Fin columns) (element : Scalar) (flag : Bool) :
    Steps advance (2 * candidate + 3)
      (0, frame matrix candidate column element flag)
      (2, frame matrix (candidate + 1) column element flag) := by
  have blank : Turing.ListBlank.mk (List.replicate (candidate + 1) (2 : Binary.Symbol) ++ [0]) =
      Turing.ListBlank.mk (List.replicate (candidate + 1) (2 : Binary.Symbol)) :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  apply wire_steps_of_eq (oneTape (Sum.inl (Sum.inl MatrixAddress.TapeName.row) : TapeName)) _
    (Unary.increment_steps candidate [] [])
  · intro name; cases name; rfl
  · intro name; cases name
    change Turing.Tape.mk' _ (Turing.ListBlank.mk (List.replicate (candidate + 1) 2 ++ [0])) = _
    rw [blank]
    simp [Binary.tape]
  · intro name outside
    cases name with
    | inl name => cases name with
      | inl name => cases name <;> first
        | exact False.elim (outside ⟨(), rfl⟩)
        | rfl
      | inr name => cases name <;> rfl
    | inr name => cases name <;> rfl

private theorem guard_halt (symbols : Symbols (Alphabet Scalar)) : guard guardExit symbols = none := by
  rfl

omit [Zero Scalar] [DecidableEq Scalar] in
private theorem advance_halt (symbols : Symbols (Alphabet Scalar)) : advance 2 symbols = none := by
  simp [advance, wire, Unary.machine]
  rfl

/-- The search preserves the matrix and records exactly which rows were skipped. -/
private theorem loop_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (start : ℕ) (bounded : start ≤ rows) (column : Fin columns) (element : Scalar) (flag : Bool) :
    ∃ ticks candidate finalElement,
      ticks ≤ (rows - start + 1) * (7 * rows * columns + 13 * rows + 7 * columns + 33) ∧
      Steps (whileMachine guard advance guardEntry 0 result) ticks
        (.inl guardEntry, frame matrix start column element flag)
        (.inl guardExit, frame matrix candidate column finalElement false) ∧
      start ≤ candidate ∧ candidate ≤ rows ∧
      (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
      (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
      (∀ valid : candidate < rows, finalElement = matrix ⟨candidate, valid⟩ column) := by
  generalize ranking : rows - start = remaining
  induction remaining using Nat.strong_induction_on generalizing start element flag with
  | h remaining hypothesis =>
    obtain ⟨guardTicks, guardCost, guardTrace⟩ := guard_steps matrix start bounded column element flag
    have liftedGuard := guardTrace.rename Sum.inl
      (target := whileMachine guard advance guardEntry 0 result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    by_cases active : continues matrix start column = true
    · have valid : start < rows := by
        by_contra invalid
        simp [continues, invalid] at active
      have zero : matrix ⟨start, valid⟩ column = 0 := by
        simpa [continues, valid] using active
      have smaller : rows - (start + 1) < remaining := by omega
      obtain ⟨restTicks, candidate, finalElement, restCost, restTrace,
        eligible, candidateBound, skipped, nonzero, foundValue⟩ :=
        hypothesis (rows - (start + 1)) smaller (start + 1) (by omega)
          (observed matrix start column element) true rfl
      have bodyTrace := advance_steps matrix start column (observed matrix start column element) true
      have liftedBody := bodyTrace.rename Sum.inr
        (target := whileMachine guard advance guardEntry 0 result)
        (by intro state symbols next actions transition; simp [whileMachine, transition])
      rw [active] at liftedGuard
      have toBody : step (whileMachine guard advance guardEntry 0 result)
          (.inl guardExit, frame matrix start column (observed matrix start column element) true) =
          some (.inr 0, frame matrix start column (observed matrix start column element) true) := by
        simp [step, whileMachine, guard_halt]
      have toGuard : step (whileMachine guard advance guardEntry 0 result)
          (.inr 2, frame matrix (start + 1) column (observed matrix start column element) true) =
          some (.inl guardEntry, frame matrix (start + 1) column (observed matrix start column element) true) := by
        simp [step, whileMachine, advance_halt]
      have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      refine ⟨_, candidate, finalElement, ?_, trace, by omega, candidateBound, ?_, nonzero, foundValue⟩
      · have stepCost : guardTicks + (2 * start + 3) + 2 ≤
            7 * rows * columns + 13 * rows + 7 * columns + 33 := by omega
        have split : rows - start + 1 = (rows - (start + 1) + 1) + 1 := by omega
        rw [← ranking, split, Nat.add_mul, one_mul]
        omega
      · intro row lower upper
        by_cases same : row.val = start
        · have equal : row = ⟨start, valid⟩ := Fin.ext same
          simpa only [equal] using zero
        · exact skipped row (by omega) upper
    · have stopped : continues matrix start column = false := Bool.eq_false_iff.mpr active
      rw [stopped] at liftedGuard
      refine ⟨guardTicks, start, observed matrix start column element, ?_, liftedGuard,
        le_rfl, bounded, ?_, ?_, ?_⟩
      · have dominates := Nat.mul_le_mul_right
          (7 * rows * columns + 13 * rows + 7 * columns + 33)
          (show 1 ≤ rows - start + 1 by omega)
        simp only [one_mul] at dominates
        rw [← ranking]
        omega
      · intro row lower upper; omega
      · intro valid
        simpa [continues, valid] using stopped
      · intro valid; simp [observed, valid]

theorem steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (start : ℕ) (bounded : start ≤ rows) (column : Fin columns) (element : Scalar) (flag : Bool) :
    ∃ ticks candidate finalElement,
      ticks ≤ (rows + 1) * (7 * rows * columns + 13 * rows + 7 * columns + 33) + 1 ∧
      Steps machine ticks (entry, frame matrix start column element flag)
        (exit, frame matrix candidate column finalElement false) ∧
      start ≤ candidate ∧ candidate ≤ rows ∧
      (∀ row : Fin rows, start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
      (∀ valid : candidate < rows, matrix ⟨candidate, valid⟩ column ≠ 0) ∧
      (∀ valid : candidate < rows, finalElement = matrix ⟨candidate, valid⟩ column) := by
  obtain ⟨ticks, candidate, finalElement, cost, trace, eligible, candidateBound, skipped, nonzero, foundValue⟩ :=
    loop_steps matrix start bounded column element flag
  have halted : step (whileMachine guard advance guardEntry 0 result)
      (.inl guardExit, frame matrix candidate column finalElement false) = none := by
    simp [step, whileMachine, guard_halt]
  refine ⟨ticks + 1, candidate, finalElement, ?_, withExit_steps _ trace halted,
    eligible, candidateBound, skipped, nonzero, foundValue⟩
  exact Nat.add_le_add_right (cost.trans (Nat.mul_le_mul_right _ (by omega))) 1

/-- One fixed finite machine searches every matrix size, with a hidden polynomial bound. -/
theorem realizes [Fintype Scalar] :
    Realizes (machine (Scalar := Scalar)) entry exit
      (fun assignment initial =>
        ∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (start : ℕ) (column : Fin (assignment true)) (element : Scalar) (flag : Bool),
          start ≤ assignment false ∧ initial = frame matrix start column element flag)
      (fun assignment initial final =>
        ∀ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
          (start : ℕ) (column : Fin (assignment true)) (element : Scalar) (flag : Bool),
          start ≤ assignment false → initial = frame matrix start column element flag →
          ∃ candidate finalElement,
            final = frame matrix candidate column finalElement false ∧
            start ≤ candidate ∧ candidate ≤ assignment false ∧
            (∀ row : Fin (assignment false), start ≤ row.val → row.val < candidate → matrix row column = 0) ∧
            (∀ valid : candidate < assignment false, matrix ⟨candidate, valid⟩ column ≠ 0)) := by
  refine ⟨by intro symbols; rfl,
    (MvPolynomial.X false + 1) *
      (7 * MvPolynomial.X false * MvPolynomial.X true + 13 * MvPolynomial.X false +
        7 * MvPolynomial.X true + 33) + 1, ?_⟩
  intro assignment initial valid
  obtain ⟨matrix, start, column, element, flag, bounded, rfl⟩ := valid
  obtain ⟨ticks, candidate, finalElement, cost, trace, eligible, candidateBound, skipped, nonzero, _⟩ :=
    steps matrix start bounded column element flag
  refine ⟨ticks, _, ?_, trace, ?_⟩
  · simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using cost
  · intro otherMatrix otherStart otherColumn otherElement otherFlag otherBound equal
    obtain ⟨otherTicks, otherCandidate, otherFinalElement, _, otherTrace,
      otherEligible, otherCandidateBound, otherSkipped, otherNonzero, _⟩ :=
      steps otherMatrix otherStart otherBound otherColumn otherElement otherFlag
    rw [← equal] at otherTrace
    refine ⟨otherCandidate, otherFinalElement, ?_, otherEligible, otherCandidateBound, otherSkipped, otherNonzero⟩
    exact congrArg Prod.snd (trace.final_eq otherTrace rfl rfl)

omit [Zero Scalar] [DecidableEq Scalar] in
/-- The machine's row-count sentinel agrees with mathematical Gauss–Jordan pivot search. -/
theorem findPivot_steps {FieldScalar : Type} [Field FieldScalar] [DecidableEq FieldScalar]
    (matrix : Matrix (Fin rows) (Fin columns) FieldScalar) (start : ℕ) (bounded : start ≤ rows)
    (column : Fin columns) (element : FieldScalar) (flag : Bool) :
    ∃ ticks candidate finalElement,
      ticks ≤ (rows + 1) * (7 * rows * columns + 13 * rows + 7 * columns + 33) + 1 ∧
      Steps machine ticks (entry, frame matrix start column element flag)
        (exit, frame matrix candidate column finalElement false) ∧
      candidate ≤ rows ∧ GaussJordan.findPivot matrix start column =
        if valid : candidate < rows then some ⟨candidate, valid⟩ else none := by
  obtain ⟨ticks, candidate, finalElement, cost, trace, eligible, candidateBound, skipped, nonzero, _⟩ :=
    steps matrix start bounded column element flag
  exact ⟨ticks, candidate, finalElement, cost, trace, candidateBound,
    GaussJordan.findPivot_eq_of_minimal matrix start candidate column eligible candidateBound skipped nonzero⟩

end Polytime2.PivotSearch
