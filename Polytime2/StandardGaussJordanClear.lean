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

import Polytime2.StandardGaussJordanClearIntervalMath
import Polytime2.StandardSizeReadContract

/-! # Shared caller workspace for complete pivot-column clearing

The original matrix has its own immutable tape. The two interval calls share
the working matrix, target counter, and arithmetic scratch. The interval limit
is private here, so the handover can replace it with the unary row count.
-/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanClearInterval.TapeName Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName

instance tapeNamesDecidableEq : DecidableEq TapeName := by
  letI : DecidableEq StandardMatrixRows.TapeName := inferInstance
  letI : DecidableEq StandardGaussJordanClearTarget.TapeName := inferInstance
  letI : DecidableEq StandardGaussJordanClearStep.TapeName := inferInstance
  letI : DecidableEq StandardGaussJordanClearInterval.TapeName := inferInstance
  infer_instance

def dataTape (slot : Fin 18) : TapeName := .inl (StandardGaussJordanClearInterval.dataTape slot)
def workingTape : TapeName := .inl StandardGaussJordanClearInterval.workingTape
def columnTape : TapeName := .inl StandardGaussJordanClearInterval.columnTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanClearInterval.sizeTape parameter)
def limitTape : TapeName := .inl StandardGaussJordanClearInterval.limitTape
def differenceTape : TapeName := .inl StandardGaussJordanClearInterval.differenceTape
def guardTape : TapeName := .inl StandardGaussJordanClearInterval.guardTape
def nextTape : TapeName := .inl (.inl StandardGaussJordanClearStep.nextTape)
def originalTape : TapeName := .inr ()

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanClearInterval.domains enumeration name
  | .inr _ => (FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length

def readOnly : TapeName → Bool
  | .inl name => if name = StandardGaussJordanClearInterval.limitTape then false
      else StandardGaussJordanClearInterval.readOnly name
  | .inr _ => true

def intervalWiring : StandardGaussJordanClearInterval.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem intervalWiring_apply (name : StandardGaussJordanClearInterval.TapeName) :
    intervalWiring name = .inl name := rfl

noncomputable def interval (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanClearInterval.State
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire intervalWiring (StandardGaussJordanClearInterval.machine enumeration)

def stepWiring : StandardGaussJordanClearStep.TapeName ↪ TapeName :=
  StandardGaussJordanClearInterval.bodyWiring.trans intervalWiring

@[simp] theorem stepWiring_apply (name : StandardGaussJordanClearStep.TapeName) :
    stepWiring name = .inl (.inl name) := rfl

noncomputable def increment : Machine Alphabet StandardGaussJordanClearStep.IncrementState :=
  MultiTape.wire stepWiring StandardGaussJordanClearStep.increment

noncomputable def advance : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy nextTape (dataTape 1) (by decide)

abbrev SkipState := Sum StandardGaussJordanClearStep.IncrementState (Fin 3)

noncomputable def skipPivot : Machine Alphabet SkipState :=
  MultiTape.sequence increment advance 0

def skipEntry : SkipState := .inl (.inl (.inl true))
def skipExit : SkipState := .inr 2

@[simp] theorem skipPivot_halt (symbols : Symbols Alphabet) : skipPivot skipExit symbols = none := by
  simp [skipPivot, skipExit, MultiTape.sequence, advance, StandardTapeCommands.copy,
    MultiTape.wire, StandardTerminatedCopy.machine]

omit [Field Scalar] in
/-- Counter increment uses a separate output and leaves every other tape
unchanged, including the original and working matrices and the interval limit. -/
theorem increment_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (targetRow : Fin (2 ^ sizes 0)),
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial nextTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly increment ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final nextTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes targetRow) ∧
        (∀ name, name ≠ nextTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanClearStep.increment_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial targetRow targetEq headers region
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, outside⟩ :=
    execute sizes (fun name => initial (stepWiring name)) targetRow targetEq headers region
  have trace := localTrace.wire stepWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (fun _ => rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
    initial (fun _ => 0)
  have start : install stepWiring (fun name => initial (stepWiring name)) initial = initial :=
    install_self stepWiring initial
  have positions : install stepWiring
      (fun _ : StandardGaussJordanClearStep.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self stepWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install stepWiring localFinal initial, cost, trace,
    (install_at stepWiring localFinal initial _).trans resultEq, ?_⟩
  intro name notNext
  by_cases located : name ∈ Set.range stepWiring
  · obtain ⟨localName, rfl⟩ := located
    rw [install_at]
    exact outside localName (by
      intro equal
      subst localName
      exact notNext rfl)
  · exact install_outside stepWiring localFinal initial name located

omit [Field Scalar] in
/-- Skipping the pivot commits the separate increment output to the private
target counter. Only those two counter tapes change. -/
theorem skipPivot_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (pivot : Fin (2 ^ sizes 0)),
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial nextTape) → Region (sizes 0) 0 (initial (dataTape 1)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly skipPivot ticks
          skipEntry (fun _ => 0) initial skipExit (fun _ => 0) final ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes pivot) ∧
        final nextTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes pivot) ∧
        (∀ name, name ≠ nextTape → name ≠ dataTape 1 → final name = initial name) := by
  obtain ⟨bound, execute⟩ := increment_runs enumeration
  refine ⟨bound + 2 * MvPolynomial.X 0 + 3, ?_⟩
  intro sizes initial pivot pivotEq headers nextRegion targetRegion
  obtain ⟨ticks, incremented, cost, trace, nextEq, outside⟩ :=
    execute sizes initial pivot pivotEq headers nextRegion
  have copyTrace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
    sizes (StandardBinaryIncrement.next 0 sizes pivot) nextTape (dataTape 1) (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl
    incremented nextEq (trace.region (dataTape 1) targetRegion)
  have complete := trace.sequence advance 0 (by intro symbols; rfl) copyTrace
  let final := Function.update incremented (dataTape 1)
    (encoded (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes pivot))
  refine ⟨ticks + (2 * sizes 0 + 2) + 1, final, ?_, ?_, Function.update_self _ _ _, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · simpa only [skipPivot, skipEntry, skipExit, advance, final,
      EncodedDomain.binaryNaturals] using complete
  · exact (Function.update_of_ne (by decide) _ _).trans nextEq
  · intro name notNext notTarget
    exact (Function.update_of_ne notTarget _ _).trans (outside name notNext)

def rowLimitWiring : Sum Bool Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl false => sizeTape 1 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => differenceTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp_all [sizeTape, limitTape, differenceTape, StandardGaussJordanClearInterval.sizeTape,
        StandardGaussJordanClearInterval.limitTape, StandardGaussJordanClearInterval.differenceTape,
        StandardGaussJordanClearStep.sizeTape, StandardGaussJordanClearTarget.sizeTape,
        StandardMatrixRows.sizeTape]⟩

@[simp] theorem rowLimitWiring_apply (name : Sum Bool Bool) : rowLimitWiring name =
    (match name with
    | .inl false => sizeTape 1 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => differenceTape) := rfl

noncomputable def readRows : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire rowLimitWiring StandardSizeRead.algorithm

@[simp] theorem readRows_halt (symbols : Symbols Alphabet) : readRows StandardSizeRead.exit symbols = none := by
  simp [readRows, MultiTape.wire, StandardSizeRead.algorithm]

omit [Field Scalar] in
/-- Read the immutable unary row size into the second interval's fixed-width
limit. Both writable counter regions may initially contain arbitrary symbols. -/
theorem readRows_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (fits : sizes 1 < 2 ^ sizes 0),
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial limitTape) → Region (sizes 0) 0 (initial differenceTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly readRows ticks
          StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ limitTape → name ≠ differenceTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := StandardSizeRead.contract.wired_runs rowLimitWiring
  let parameter : Bool → Fin 3 := fun name => if name then 0 else 1
  refine ⟨MvPolynomial.rename parameter bound, ?_⟩
  intro sizes initial fits headers limitRegion scratchRegion
  let localSizes : Bool → ℕ := fun name => sizes (parameter name)
  let input : Inputs StandardSizeRead.domains StandardSizeRead.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl name => exact PUnit.unit
    | inr name => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute localSizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      fits
      (by
        intro name readonly
        cases name with
        | inl name =>
          change initial (rowLimitWiring (.inl name)) = encoded (EncodedDomain.unary name) localSizes PUnit.unit
          rw [encoded_unary]
          cases name <;> exact headers _
        | inr name => contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | exact limitRegion | exact scratchRegion)
      (by intro name; cases name <;> exact headers _)
  have valueEq : output ⟨.inr false, rfl⟩ = (⟨sizes 1, fits⟩ : Fin (2 ^ sizes 0)) := Fin.ext correct
  refine ⟨ticks, final, ?_, trace, ?_, ⟨output ⟨.inr true, rfl⟩, canonical (.inr true) rfl⟩, ?_⟩
  · simpa only [MvPolynomial.eval_rename, localSizes, Function.comp_def] using cost
  · have result := canonical (.inr false) rfl
    rw [valueEq] at result
    exact result
  · intro name notLimit notScratch
    apply preserved_of_wiring rowLimitWiring StandardSizeRead.argumentReadOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr name => cases name with
      | false => exact False.elim (notLimit equal.symm)
      | true => exact False.elim (notScratch equal.symm)

abbrev HandoverState := Sum SkipState StandardSizeRead.State

noncomputable def handover : Machine Alphabet HandoverState :=
  MultiTape.sequence skipPivot readRows StandardSizeRead.entry

def handoverEntry : HandoverState := .inl skipEntry
def handoverExit : HandoverState := .inr StandardSizeRead.exit

@[simp] theorem handover_halt (symbols : Symbols Alphabet) : handover handoverExit symbols = none := by
  simp [handover, handoverExit, MultiTape.sequence, readRows_halt]

omit [Field Scalar] in
/-- Between the intervals, skip the pivot and install the row-count limit.
The matrices, pivot, column, unary sizes, and all other scratch are preserved. -/
theorem handover_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot : Fin (2 ^ sizes 0)) (fits : sizes 1 < 2 ^ sizes 0),
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly handover ticks
          handoverEntry (fun _ => 0) initial handoverExit (fun _ => 0) final ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes pivot) ∧
        final nextTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes pivot) ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ nextTape → name ≠ dataTape 1 → name ≠ limitTape →
          name ≠ differenceTape → final name = initial name) := by
  obtain ⟨skipBound, executeSkip⟩ := skipPivot_runs enumeration
  obtain ⟨readBound, executeRead⟩ := readRows_runs enumeration
  refine ⟨skipBound + readBound + 1, ?_⟩
  intro sizes initial pivot fits pivotEq headers regions
  obtain ⟨skipTicks, skipped, skipCost, skipTrace, targetEq, nextEq, skipOutside⟩ :=
    executeSkip sizes initial pivot pivotEq headers (regions nextTape) (regions (dataTape 1))
  obtain ⟨readTicks, final, readCost, readTrace, limitEq, differenceEq, readOutside⟩ :=
    executeRead sizes skipped fits
      (fun parameter => (skipTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (skipTrace.region limitTape (regions limitTape))
      (skipTrace.region differenceTape (regions differenceTape))
  have complete := skipTrace.sequence readRows StandardSizeRead.entry skipPivot_halt readTrace
  refine ⟨skipTicks + readTicks + 1, final, ?_, ?_,
    (readOutside (dataTape 1) (by decide) (by decide)).trans targetEq,
    (readOutside nextTape (by decide) (by decide)).trans nextEq, limitEq, differenceEq, ?_⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [handover, handoverEntry, handoverExit] using complete
  · intro name notNext notTarget notLimit notDifference
    exact (readOutside name notLimit notDifference).trans (skipOutside name notNext notTarget)

end Polytime2.StandardGaussJordanClear

