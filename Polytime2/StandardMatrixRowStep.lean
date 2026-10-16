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

import Polytime2.StandardMatrixRowEntryContract
import Polytime2.StandardBinaryIncrement
import Polytime2.StandardTapeCommands

/-! # The internal column step of a matrix row traversal

The working matrix and column counter are private writable tapes. A row-entry
call writes a separate result; copying commits that result to the working
matrix. A separate increment output is then copied to the column counter.
All these calls restore their heads and preserve the fixed tape regions.
-/

namespace Polytime2.StandardMatrixRowStep

open MultiTape CallingConvention

abbrev TapeName := Sum StandardMatrixRowEntry.TapeName Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev State (width : ℕ) := Sum (StandardMatrixRowEntry.State width)
  (Sum (Fin 3) (Sum IncrementState (Fin 3)))

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardMatrixRowEntry.State width) := inferInstance
  dsimp only [State]
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

noncomputable def machine (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (State (scalar.width Empty.elim)) :=
  MultiTape.sequence
    (MultiTape.wire entryWiring (StandardMatrixRowEntry.machine writeSource scalar operation))
    (MultiTape.sequence commit (MultiTape.sequence increment advance 0) (.inl (.inl (.inl true))))
    (.inl 0)

def entry (width : ℕ) : State width := .inl (StandardMatrixRowEntry.entry width)
def exit (width : ℕ) : State width := .inr (.inr (.inr 2))

@[simp] theorem halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (symbols : Symbols Alphabet) :
    machine writeSource scalar operation (exit (scalar.width Empty.elim)) symbols = none := by
  simp [machine, exit, MultiTape.sequence, advance, StandardTapeCommands.copy,
    MultiTape.wire, StandardTerminatedCopy.machine]

/-- Incrementing a private counter uses a distinct output, even when the
counter's old value was produced by another routine in the same workspace. -/
theorem increment_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (column : Fin (2 ^ sizes 0)),
      initial (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      (∀ parameter, initial (.inl (.inl parameter)) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial (.inr ())) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly increment ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final (.inr ()) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes column) ∧
        (∀ name, name ≠ .inr () → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (StandardBinaryIncrement.contract (0 : Fin 3)).wired_runs incrementWiring
  refine ⟨bound, ?_⟩
  intro sizes initial column columnEq headers region
  let input : Inputs (StandardBinaryScan.domains (EncodedDomain.binaryNaturals (0 : Fin 3))
      (EncodedDomain.binaryNaturals 0)) StandardTerminatedCopy.readOnly sizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name => cases name with
      | false => exact column
      | true => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (.inl (.inl parameter)) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr name => cases name with
          | false => exact columnEq
          | true => contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | simpa [domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using region)
      headers
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = StandardBinaryIncrement.next 0 sizes column at correct
    rw [correct] at result
    exact result
  · intro name different
    apply preserved_of_wiring incrementWiring StandardTerminatedCopy.readOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr localName => cases localName with
      | false => rfl
      | true => exact False.elim (different equal.symm)

/-- One column is processed and committed before the fixed-capacity counter
advances. The caller supplies the private working values; every scratch region
may otherwise start arbitrary, and every writable tape is valid on return. -/
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
          (StandardBinaryIncrement.next 0 sizes column) ∧
        (∀ name, readOnly name = false → ∃ value : (domains scalar name).Carrier sizes,
          final name = encoded (domains scalar name) sizes value) := by
  classical
  obtain ⟨entryBound, executeEntry⟩ := StandardMatrixRowEntry.runs writeSource scalar operation
  obtain ⟨incrementBound, executeIncrement⟩ := increment_runs scalar
  let matrixBound := (scalar.constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨entryBound + incrementBound + 2 * matrixBound + 2 * MvPolynomial.X 0 + 7, ?_⟩
  intro sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin
    columnsFit sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers regions
    sourceIndex targetIndex result resultArray
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  obtain ⟨entryTicks, localFinal, entryCost, localTrace, localResult, localCanonical⟩ :=
    executeEntry sizes (fun name => initial (.inl name)) sourceRow targetRow column array coefficient
      sourceWithin targetWithin columnsFit sourceValid targetValid columnValid capacity
      sourceEq targetEq columnEq coefficientEq arrayEq headers (fun name => regions (.inl name))
  let afterEntry : Tapes Alphabet := install entryWiring localFinal initial
  have entryTrace : Runs width readOnly
      (MultiTape.wire entryWiring (StandardMatrixRowEntry.machine writeSource scalar operation)) entryTicks
      (StandardMatrixRowEntry.entry (scalar.width Empty.elim)) (fun _ => 0) initial
      (StandardMatrixRowEntry.exit (scalar.width Empty.elim)) (fun _ => 0) afterEntry := by
    have trace := localTrace.wire entryWiring width readOnly (fun _ => rfl)
      (by
        intro name premise
        cases name with
        | inl parameter => rfl
        | inr name => fin_cases name <;> first | rfl | contradiction)
      initial (fun _ => 0)
    have zeroPositions : install entryWiring (fun _ : StandardMatrixRowEntry.TapeName => (0 : ℤ))
        (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self entryWiring _
    have start : install entryWiring (fun name => initial (.inl name)) initial = initial :=
      install_self entryWiring initial
    rw [zeroPositions, start] at trace
    exact trace
  have afterEntryAt (name : StandardMatrixRowEntry.TapeName) : afterEntry (.inl name) = localFinal name :=
    install_at entryWiring localFinal initial name
  have matrixEq : afterEntry (.inl (.inr 5)) =
      encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray :=
    (afterEntryAt (.inr 5)).trans localResult
  have columnPreserved : afterEntry (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes column :=
    (afterEntryAt (.inr 2)).trans ((localTrace.readOnly_tape (.inr 2) rfl).trans columnEq)
  have entryRegions : ∀ name, Region (width name) 0 (afterEntry name) :=
    fun name => entryTrace.region name (regions name)
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
      (by decide) width readOnly rfl rfl rfl afterEntry matrixEq (entryRegions _)
  have committedRegions : ∀ name, Region (width name) 0 (committed name) :=
    fun name => commitTrace.region name (entryRegions name)
  obtain ⟨incrementTicks, afterIncrement, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes committed column
      (by simpa only [committed, Function.update_of_ne (by decide : (.inl (.inr 2) : TapeName) ≠ .inl (.inr 4))] using columnPreserved)
      (by
        intro parameter
        have header := (entryTrace.readOnly_tape (.inl (.inl parameter)) rfl).trans (headers parameter)
        simpa only [committed, Function.update_of_ne (by simp : (.inl (.inl parameter) : TapeName) ≠ .inl (.inr 4))] using header)
      (by simpa [width, domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using committedRegions (.inr ()))
  have incrementRegions : ∀ name, Region (width name) 0 (afterIncrement name) :=
    fun name => incrementTrace.region name (committedRegions name)
  let nextColumn := StandardBinaryIncrement.next 0 sizes column
  let final := Function.update afterIncrement (.inl (.inr 2))
    (encoded (EncodedDomain.binaryNaturals 0) sizes nextColumn)
  have advanceTrace : Runs width readOnly advance (2 * sizes 0 + 2)
      0 (fun _ => 0) afterIncrement 2 (fun _ => 0) final := by
    dsimp only [advance, final]
    simpa only [EncodedDomain.binaryNaturals_width] using
      StandardTapeCommands.copy_encoded_runs (TapeName := TapeName)
      (EncodedDomain.binaryNaturals 0) sizes nextColumn (.inr ()) (.inl (.inr 2))
      (by decide) width readOnly rfl rfl rfl afterIncrement nextEq (incrementRegions _)
  have tail := incrementTrace.sequence advance 0
    (by intro symbols; simp [increment, MultiTape.wire, StandardBinaryScan.algorithm, MultiTape.withExit]) advanceTrace
  have middle := commitTrace.sequence (MultiTape.sequence increment advance 0) (.inl (.inl (.inl true)))
    (by intro symbols; simp [commit, StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) tail
  have complete := entryTrace.sequence _ (Sum.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardMatrixRowEntry.halt]) middle
  have finalPreserved (name : StandardMatrixRowEntry.TapeName) (notColumn : name ≠ .inr 2) :
      final (.inl name) = committed (.inl name) := by
    change Function.update afterIncrement _ _ (.inl name) = _
    rw [Function.update_of_ne (by simpa using notColumn)]
    exact incrementOutside (.inl name) (by simp)
  refine ⟨entryTicks + ((2 * (scalar.constant.arrayOfLength StandardMatrixEntry.length).width sizes + 2) +
    (incrementTicks + (2 * sizes 0 + 2) + 1) + 1) + 1, final, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [matrixBound, EncodedDomain.width, map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · simpa only [machine, entry, exit] using complete
  · exact (finalPreserved (.inr 4) (by decide)).trans (Function.update_self _ _ _)
  · rw [finalPreserved (.inr 5) (by decide)]
    exact (Function.update_of_ne (by decide : (.inl (.inr 5) : TapeName) ≠ .inl (.inr 4)) _ _).trans matrixEq
  · exact Function.update_self _ _ _
  · intro name writable
    cases name with
    | inr name =>
      cases name
      refine ⟨nextColumn, ?_⟩
      exact (Function.update_of_ne (by decide : (.inr () : TapeName) ≠ .inl (.inr 2)) _ _).trans nextEq
    | inl name =>
      cases name with
      | inl parameter => contradiction
      | inr name =>
        by_cases isColumn : name = 2
        · subst name
          exact ⟨nextColumn, Function.update_self _ _ _⟩
        · by_cases isMatrix : name = 4
          · subst name
            exact ⟨resultArray, (finalPreserved (.inr 4) (by decide)).trans (Function.update_self _ _ _)⟩
          · have localWritable : StandardMatrixRowEntry.readOnly (.inr name) = false := by
              fin_cases name <;> first | rfl | contradiction
            obtain ⟨value, canonical⟩ := localCanonical (.inr name) localWritable
            refine ⟨value, ?_⟩
            rw [finalPreserved (.inr name) (by simpa using isColumn)]
            change Function.update afterEntry _ _ (.inl (.inr name)) = _
            rw [Function.update_of_ne (by simpa using isMatrix)]
            exact (afterEntryAt (.inr name)).trans canonical

end Polytime2.StandardMatrixRowStep
