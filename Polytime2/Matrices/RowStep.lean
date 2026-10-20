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

import Polytime2.Machine.Pipeline

import Polytime2.Matrices.RowEntryContract
import Polytime2.Arithmetic.BinaryIncrement
import Polytime2.Primitives.TapeCommands

/-! # The internal column step of a matrix row traversal

The working matrix and column counter are private writable tapes. A row-entry
call writes a separate result; copying commits that result to the working
matrix. A separate increment output is then copied to the column counter.
All these calls restore their heads and preserve the fixed tape regions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.StandardMatrixRowStep

open MultiTape CallingConvention

abbrev TapeName := Sum StandardMatrixRowEntry.TapeName Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev StageState (width : ℕ) : Fin 4 → Type
  | 0 => StandardMatrixRowEntry.State width
  | 1 | 3 => Fin 3
  | 2 => IncrementState
abbrev State (width : ℕ) := Pipeline.State (StageState width)

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardMatrixRowEntry.State width) := inferInstance
  letI (stage : Fin 4) : Fintype (StageState width stage) := by
    match stage with
    | 0 | 1 | 2 | 3 => infer_instance
  infer_instance

/-- The extra tape holds the next binary column counter. -/
noncomputable def domains (scalar : EncodedDomain.{0, 0} Empty) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardMatrixRowEntry.domains scalar name
  | .inr _ => EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl (.inl _) => true
  | .inl (.inr name) => decide (name = 0 ∨ name = 1 ∨ name = 3)
  | .inr _ => false

def entryWiring : StandardMatrixRowEntry.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem entryWiring_apply (name : StandardMatrixRowEntry.TapeName) :
    entryWiring name = .inl name := rfl

def incrementWiring : Sum (Fin 3) Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl parameter => .inl (.inl parameter)
    | .inr false => .inl (.inr 2)
    | .inr true => .inr ()), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem incrementWiring_apply (name : Sum (Fin 3) Bool) :
    incrementWiring name = (match name with
    | .inl parameter => .inl (.inl parameter)
    | .inr false => .inl (.inr 2)
    | .inr true => .inr ()) := rfl

noncomputable def commit : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy (.inl (.inr 5)) (.inl (.inr 4)) (by decide)

noncomputable def increment : Machine Alphabet IncrementState :=
  MultiTape.wire incrementWiring (StandardBinaryScan.algorithm BinaryScan.increment)

noncomputable def advance : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy (.inr ()) (.inl (.inr 2)) (by decide)

noncomputable def components (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∀ stage, Machine Alphabet (StageState (scalar.width Empty.elim) stage)
  | 0 => MultiTape.wire entryWiring (StandardMatrixRowEntry.machine writeSource scalar operation)
  | 1 => commit
  | 2 => increment
  | 3 => advance

def entries (width : ℕ) : ∀ stage, StageState width stage
  | 0 => StandardMatrixRowEntry.entry width
  | 1 | 3 => 0
  | 2 => .inl (.inl true)

def exits (width : ℕ) : ∀ stage, StageState width stage
  | 0 => StandardMatrixRowEntry.exit width
  | 1 | 3 => 2
  | 2 => .inr ()

noncomputable def machine (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (State (scalar.width Empty.elim)) :=
  Pipeline.machine (components writeSource scalar operation) (entries (scalar.width Empty.elim))

def entry (width : ℕ) : State width := Pipeline.position (entries width) 0
def exit (width : ℕ) : State width := none

@[simp] theorem halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (symbols : Symbols Alphabet) :
    machine writeSource scalar operation (exit (scalar.width Empty.elim)) symbols = none := rfl

/-- One column is processed and committed before the fixed-capacity counter
advances. The caller supplies the private working values; every scratch region
may otherwise start arbitrary; only the live matrices and counter are encoded. -/
theorem runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (coefficient : scalar.Carrier Empty.elim)
      (sourceWithin : sourceRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length)
      (targetWithin : targetRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → sourceRow.val < sizes 1 → targetRow.val < sizes 1 →
      column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (.inl (.inr 0)) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (.inl (.inr 1)) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial (.inl (.inr 3)) = encoded scalar Empty.elim coefficient →
      initial (.inl (.inr 4)) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (.inl (.inl parameter)) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
        ⟨sourceRow.val * sizes 2 + column.val, sourceWithin⟩
      let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
        ⟨targetRow.val * sizes 2 + column.val, targetWithin⟩
      let result := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
        coefficient (array sourceIndex) (array targetIndex)
      let resultArray := Function.update (Function.update array sourceIndex result.1) targetIndex result.2
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (machine writeSource scalar operation) ticks
          (entry (scalar.width Empty.elim)) (fun _ => 0) initial (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (.inl (.inr 4)) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray ∧
        final (.inl (.inr 5)) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray ∧
        final (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes column)  := by
  classical
  obtain ⟨entryBound, executeEntry⟩ := StandardMatrixRowEntry.runs writeSource scalar operation
  obtain ⟨incrementBound, executeIncrement⟩ := StandardBinaryIncrement.wired_runs 0
    (fun sizes name => (domains scalar name).width sizes) readOnly incrementWiring
    (by intro sizes name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
  let matrixBound := (scalar.constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨4 * (entryBound + incrementBound + 2 * matrixBound + 2 * MvPolynomial.X 0 + 7), ?_⟩
  intro sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin
    columnsFit sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers regions
    sourceIndex targetIndex result resultArray
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  obtain ⟨entryTicks, localFinal, entryCost, localTrace, localResult⟩ :=
    executeEntry sizes (fun name => initial (.inl name)) sourceRow targetRow column array coefficient
      sourceWithin targetWithin columnsFit sourceValid targetValid columnValid capacity
      sourceEq targetEq columnEq coefficientEq arrayEq headers (fun name => regions (.inl name))
  obtain ⟨afterEntry, entryTrace, afterEntryAt, _, entryImmutable⟩ :=
    localTrace.wire_restoring entryWiring width readOnly (fun _ => rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (fun _ => rfl)
  have matrixEq : afterEntry (.inl (.inr 5)) =
      encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray :=
    (afterEntryAt (.inr 5)).trans localResult
  have columnPreserved : afterEntry (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes column :=
    (entryImmutable (.inr 2) rfl).trans columnEq
  have entryFrame := entryTrace.frame ⟨regions, (by intros; rfl)⟩
  let committed := Function.update afterEntry (.inl (.inr 4))
    (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray)
  have commitTrace : Runs width readOnly commit
      (2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes + 2)
      0 (fun _ => 0) afterEntry 2 (fun _ => 0) committed := by
    dsimp only [commit, committed]
    simpa only [EncodedDomain.binaryNaturals_width] using
      StandardTapeCommands.copy_encoded_runs (TapeName := TapeName)
      (scalar.constant.arrayOfLength StandardMatrixEntry.length)
      sizes resultArray (.inl (.inr 5)) (.inl (.inr 4))
      (by decide) width readOnly rfl rfl rfl afterEntry matrixEq (entryFrame.1 _)
  have committedFrame := commitTrace.frame entryFrame
  obtain ⟨incrementTicks, afterIncrement, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes committed column
      (by simpa only [incrementWiring_apply, committed,
        Function.update_of_ne (by decide : (.inl (.inr 2) : TapeName) ≠ .inl (.inr 4))] using columnPreserved)
      (fun parameter => (committedFrame.2 (.inl (.inl parameter)) rfl).trans (headers parameter))
      (by simpa [width, domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using committedFrame.1 (.inr ()))
  have incrementFrame := incrementTrace.frame committedFrame
  let nextColumn := StandardBinaryIncrement.next 0 sizes column
  let final := Function.update afterIncrement (.inl (.inr 2))
    (encoded (EncodedDomain.binaryNaturals 0) sizes nextColumn)
  have advanceTrace : Runs width readOnly advance (2 * sizes 0 + 2)
      0 (fun _ => 0) afterIncrement 2 (fun _ => 0) final := by
    dsimp only [advance, final]
    simpa only [EncodedDomain.binaryNaturals_width] using
      StandardTapeCommands.copy_encoded_runs (TapeName := TapeName)
      (EncodedDomain.binaryNaturals 0) sizes nextColumn (.inr ()) (.inl (.inr 2))
      (by decide) width readOnly rfl rfl rfl afterIncrement nextEq (incrementFrame.1 _)
  obtain ⟨total, totalCost, complete⟩ := Pipeline.runs_chain width readOnly (components writeSource scalar operation)
    (entries (scalar.width Empty.elim)) (exits (scalar.width Empty.elim))
    ![initial, afterEntry, committed, afterIncrement, final]
    ![entryTicks, 2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes + 2, incrementTicks, 2 * sizes 0 + 2]
    (by intro stage symbols; fin_cases stage <;> rfl)
    (by intro stage; fin_cases stage <;> first
      | exact entryTrace
      | exact commitTrace
      | exact incrementTrace
      | exact advanceTrace)
  have finalPreserved (name : StandardMatrixRowEntry.TapeName) (notColumn : name ≠ .inr 2) :
      final (.inl name) = committed (.inl name) := by
    change Function.update afterIncrement _ _ (.inl name) = _
    rw [Function.update_of_ne (by simpa using notColumn)]
    exact incrementOutside (.inl name) (by simp)
  refine ⟨total, final, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
      Nat.add_zero, EncodedDomain.width] at totalCost
    simp only [matrixBound, map_add, map_mul, map_ofNat, MvPolynomial.eval_X] at totalCost ⊢
    omega
  · simpa [machine, entry, exit, width, Fin.last] using complete
  · exact (finalPreserved (.inr 4) (by decide)).trans (Function.update_self _ _ _)
  · rw [finalPreserved (.inr 5) (by decide)]
    exact (Function.update_of_ne (by decide : (.inl (.inr 5) : TapeName) ≠ .inl (.inr 4)) _ _).trans matrixEq
  · exact Function.update_self _ _ _
end Polytime2.StandardMatrixRowStep
