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

import Polytime2.StandardBinaryDivisionStep
import Polytime2.StandardTerminatedCopy
import Polytime2.StandardBitFold

/-! # Binary long remainder with private fixed-width scratch

The dividend and divisor are immutable. A marker-free dividend cursor visits
bits from high to low; each iteration shifts, reduces, and copies a separately
computed remainder into private storage. All heads return to their starts.
-/

namespace Polytime2.StandardBinaryRemainder

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 7 => Symbol
/-- Remainder, shifted word, difference, next remainder, and borrow storage. -/
abbrev Workspace := List Bool × List Symbol × List Symbol × List Symbol × Symbol

def frame (source : Turing.Tape Symbol) (divisor : List Bool) (work : Workspace) : Tapes Alphabet :=
  fun name => if name = 0 then buffer (word work.1)
    else if name = 1 then buffer (word divisor)
    else if name = 2 then buffer work.2.1
    else if name = 3 then buffer work.2.2.1
    else if name = 4 then buffer [work.2.2.2.2]
    else if name = 5 then buffer work.2.2.2.1
    else source

def widths (sourceWidth digits : ℕ) (name : Fin 7) : ℕ :=
  if name = 6 then sourceWidth else if name = 4 then 1 else digits

def readOnly (name : Fin 7) : Bool := decide (name = 1 ∨ name = 6)

def position (sourcePosition : ℤ) (name : Fin 7) : ℤ := if name = 6 then sourcePosition else 0

def Fits (digits : ℕ) (work : Workspace) : Prop :=
  work.1.length = digits ∧ work.2.1.length = digits ∧
    work.2.2.1.length = digits ∧ work.2.2.2.1.length = digits

def advance (bit : Bool) (divisor : List Bool) (work : Workspace) : Workspace :=
  let shifted := StandardBinaryDivisionStep.shifted bit work.1
  let difference := BinarySubtraction.ripple false shifted divisor
  let next := StandardBinaryDivisionStep.next bit work.1 divisor
  (next, word shifted, word difference.1, word next, data difference.2)

private theorem next_length (bit : Bool) (remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length) :
    (StandardBinaryDivisionStep.next bit remainder divisor).length = remainder.length := by
  have shiftedLength := StandardBinaryDivisionStep.shifted_length bit remainder
  have differenceLength := BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false (StandardBinaryDivisionStep.shifted bit remainder) divisor (by omega)
  dsimp only [StandardBinaryDivisionStep.next, StandardBinaryReduce.reduced]
  split
  · exact shiftedLength
  · exact differenceLength.trans shiftedLength

private theorem advance_fits (bit : Bool) (divisor : List Bool) (work : Workspace)
    (fits : Fits divisor.length work) : Fits divisor.length (advance bit divisor work) := by
  dsimp only [Fits] at fits
  have nextLength := next_length bit work.1 divisor fits.1.symm
  have shiftedLength := StandardBinaryDivisionStep.shifted_length bit work.1
  have differenceLength := BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false (StandardBinaryDivisionStep.shifted bit work.1) divisor (by omega)
  simp only [Fits, advance, word, List.length_map]
  exact ⟨nextLength.trans fits.1, shiftedLength.trans fits.1,
    differenceLength.trans (shiftedLength.trans fits.1), nextLength.trans fits.1⟩

def stepWiring : Fin 6 ↪ Fin 7 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 7 => name.val) equal)⟩

def copyWiring : Bool ↪ Fin 7 :=
  ⟨(fun name => if name then 0 else 5), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem stepWiring_apply (name : Fin 6) : stepWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem copyWiring_apply (name : Bool) : copyWiring name = (if name then 0 else 5) := rfl

noncomputable def stepMachine : Machine Alphabet StandardBinaryDivisionStep.State :=
  MultiTape.wire stepWiring StandardBinaryDivisionStep.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  MultiTape.wire copyWiring StandardTerminatedCopy.machine

abbrev BodyState := Sum StandardBinaryDivisionStep.State (Fin 3)

noncomputable def bodyMachine : Machine Alphabet BodyState :=
  MultiTape.sequence stepMachine copyMachine 0

def bodyEntry (bit : Bool) : BodyState := .inl (StandardBinaryDivisionStep.entry bit)
def bodyExit : BodyState := .inr 2

private theorem step_install (source : Turing.Tape Symbol) (divisor remainder : List Bool)
    (work : Workspace) (shifted difference result : List Symbol) (flag : Symbol) :
    install stepWiring (StandardBinaryDivisionStep.frame remainder divisor shifted difference result flag)
      (frame source divisor work) = frame source divisor (remainder, shifted, difference, result, flag) := by
  funext name
  fin_cases name
  all_goals first
    | (change install stepWiring _ _ (stepWiring 0) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 1) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 2) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 3) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 4) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 5) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 7 => name.val) equal;
        have bounded := localName.isLt; simp only [stepWiring_apply] at values; omega)

private theorem copy_install (source : Turing.Tape Symbol) (divisor : List Bool) (work : Workspace)
    (result newRemainder : List Bool) :
    install copyWiring (Copy.frame [0] (word result ++ [0]) [0] (word newRemainder ++ [0]))
      (frame source divisor (work.1, work.2.1, work.2.2.1, word result, work.2.2.2.2)) =
      frame source divisor (newRemainder, work.2.1, work.2.2.1, word result, work.2.2.2.2) := by
  funext name
  fin_cases name
  · change install copyWiring _ _ (copyWiring true) = _
    rw [install_at]
    exact buffer_padding (word newRemainder)
  all_goals first
    | (change install copyWiring _ _ (copyWiring false) = _;
        rw [install_at]; exact buffer_padding (word result))
    | (apply install_outside; rintro ⟨localName, equal⟩;
        cases localName <;> simp [copyWiring_apply] at equal)

private theorem step_positions (offset : ℤ) :
    install stepWiring (fun _ : Fin 6 => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  all_goals first
    | (change install stepWiring _ _ (stepWiring 0) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 1) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 2) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 3) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 4) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 5) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 7 => name.val) equal;
        have bounded := localName.isLt; simp only [stepWiring_apply] at values; omega)

private theorem copy_positions (offset : ℤ) :
    install copyWiring (fun _ : Bool => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  all_goals first
    | (change install copyWiring _ _ (copyWiring false) = _; rw [install_at]; rfl)
    | (change install copyWiring _ _ (copyWiring true) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        cases localName <;> simp [copyWiring_apply] at equal)

/-- One internal iteration can update private remainder storage, while the
source cursor stays stationary wherever the outer loop placed it. -/
theorem body_runs (bit : Bool) (divisor : List Bool) (work : Workspace)
    (fits : Fits divisor.length work) (source : Turing.Tape Symbol) (sourceWidth : ℕ) (offset : ℤ) :
    Runs (widths sourceWidth divisor.length) readOnly bodyMachine (8 * divisor.length + 13)
      (bodyEntry bit) (position offset) (frame source divisor work)
      bodyExit (position offset) (frame source divisor (advance bit divisor work)) := by
  have first := (StandardBinaryDivisionStep.runs bit work.1 divisor fits.1.symm
    work.2.1 work.2.2.1 work.2.2.2.1
    (fits.2.1.trans fits.1.symm) (fits.2.2.1.trans fits.1.symm)
    (fits.2.2.2.trans fits.1.symm) work.2.2.2.2).wire
    stepWiring (widths sourceWidth divisor.length) readOnly
    (by intro name; fin_cases name <;>
        simp [widths, stepWiring_apply, StandardBinaryDivisionStep.widths, fits.1])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, stepWiring_apply, StandardBinaryDivisionStep.readOnly])
    (frame source divisor work) (position offset)
  rw [step_positions, step_install, step_install] at first
  let next := StandardBinaryDivisionStep.next bit work.1 divisor
  let shifted := StandardBinaryDivisionStep.shifted bit work.1
  let difference := BinarySubtraction.ripple false shifted divisor
  have nextLength : next.length = divisor.length := (next_length bit work.1 divisor fits.1.symm).trans fits.1
  have second := (StandardTerminatedCopy.runs next (word work.1)
    (by simp only [word, List.length_map, nextLength, fits.1])).wire
    copyWiring (widths sourceWidth divisor.length) readOnly
    (by intro name; cases name <;> simp [widths, copyWiring_apply, nextLength])
    (by intro name premise; cases name <;> simp [readOnly, copyWiring_apply] at premise)
    (frame source divisor (work.1, word shifted, word difference.1, word next, data difference.2))
    (position offset)
  rw [copy_positions,
    copy_install source divisor (work.1, word shifted, word difference.1, word next, data difference.2) next work.1,
    copy_install source divisor (work.1, word shifted, word difference.1, word next, data difference.2) next next] at second
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryDivisionStep.machine,
      StandardBinaryDivisionStep.exit, MultiTape.sequence, StandardBinaryDivisionStep.reduceMachine,
      StandardBinaryReduce.machine, StandardBinaryReduce.exit, StandardBinaryReduce.selection, MultiTape.withExit]) second
  simp only [fits.1, nextLength] at complete
  convert complete using 1 <;> first | rfl | omega

def clearWiring : Bool ↪ Fin 7 :=
  ⟨(fun name => if name then 0 else 1), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem clearWiring_apply (name : Bool) : clearWiring name = (if name then 0 else 1) := rfl

noncomputable def clearMachine : Machine Alphabet (StandardBinaryScan.State Unit) :=
  MultiTape.wire clearWiring (StandardBinaryScan.machine BinaryScan.clear)

abbrev LoopState := StandardBitFold.State BodyState

noncomputable def loopMachine : Machine Alphabet LoopState :=
  StandardBitFold.machine 6 bodyMachine bodyEntry

abbrev State := Sum (StandardBinaryScan.State Unit) LoopState

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence clearMachine loopMachine StandardBitFold.entry

def entry : State := .inl (.inl ())
def exit : State := .inr StandardBitFold.exit

def finish (divisor : List Bool) : List Bool → Workspace → Workspace
  | [], work => work
  | bit :: bits, work => finish divisor bits (advance bit divisor work)

private theorem fold_frame (source : Turing.Tape Symbol) (divisor : List Bool) (work : Workspace) :
    StandardBitFold.frame 6 (fun work => frame (buffer []) divisor work) source work =
      frame source divisor work := by
  funext name
  fin_cases name <;> rfl

private theorem fold_finish (bits divisor : List Bool) (work : Workspace) :
    StandardBitFold.fold (fun bit work => advance bit divisor work) bits work = finish divisor bits work := by
  induction bits generalizing work with
  | nil => rfl
  | cons bit bits hypothesis => exact hypothesis _

private theorem loop_runs (input divisor : List Bool) (work : Workspace)
    (fits : Fits divisor.length work) :
    Runs (widths input.length divisor.length) readOnly loopMachine
      (input.length * (8 * divisor.length + 17) + 3)
      StandardBitFold.entry (fun _ => 0) (frame (buffer (word input)) divisor work)
      StandardBitFold.exit (fun _ => 0)
      (frame (buffer (word input)) divisor (finish divisor input.reverse work)) := by
  have trace := StandardBitFold.runs 6 bodyMachine bodyEntry (fun work => frame (buffer []) divisor work)
    (widths input.length divisor.length) readOnly (fun bit work => advance bit divisor work)
    (Fits divisor.length) bodyExit (8 * divisor.length + 13)
    (by intro symbols; simp [bodyMachine, bodyExit, MultiTape.sequence, copyMachine,
      MultiTape.wire, StandardTerminatedCopy.machine])
    (fun bit work valid => advance_fits bit divisor work valid)
    (by
      intro bit work valid source offset
      rw [fold_frame, fold_frame]
      exact body_runs bit divisor work valid source input.length offset)
    input work fits
  rw [fold_frame, fold_frame, fold_finish] at trace
  exact trace

/-- The remainder region is arbitrary on entry, just like the other outputs. -/
def initialFrame (source : Turing.Tape Symbol) (divisor : List Bool)
    (old : List Symbol) (work : Workspace) : Tapes Alphabet :=
  fun name => if name = 0 then buffer old else frame source divisor work name

private theorem clear_install (source : Turing.Tape Symbol) (divisor remainder : List Bool)
    (old : List Symbol) (work : Workspace) :
    install clearWiring (Copy.frame [0] (word divisor ++ [0]) [0] (word remainder ++ [0]))
      (initialFrame source divisor old work) =
      frame source divisor (remainder, work.2.1, work.2.2.1, work.2.2.2.1, work.2.2.2.2) := by
  funext name
  fin_cases name
  · change install clearWiring _ _ (clearWiring true) = _
    rw [install_at]
    exact buffer_padding (word remainder)
  · change install clearWiring _ _ (clearWiring false) = _
    rw [install_at]
    exact buffer_padding (word divisor)
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [clearWiring_apply] at equal

private theorem clear_initial (source : Turing.Tape Symbol) (divisor : List Bool)
    (old : List Symbol) (work : Workspace) :
    install clearWiring (Copy.frame [0] (word divisor ++ [0]) [0] (old ++ [0]))
      (initialFrame source divisor old work) = initialFrame source divisor old work := by
  funext name
  fin_cases name
  · change install clearWiring _ _ (clearWiring true) = _
    rw [install_at]
    exact buffer_padding old
  · change install clearWiring _ _ (clearWiring false) = _
    rw [install_at]
    exact buffer_padding (word divisor)
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [clearWiring_apply] at equal

/-- Complete runtime-width long division. Neither its finite controller nor its
tape count depends on the input widths. Every writable region starts arbitrarily. -/
theorem runs (input divisor : List Bool) (old shifted difference result : List Symbol)
    (oldLength : old.length = divisor.length) (shiftedLength : shifted.length = divisor.length)
    (differenceLength : difference.length = divisor.length) (resultLength : result.length = divisor.length)
    (flag : Symbol) :
    let work : Workspace := (List.replicate divisor.length false, shifted, difference, result, flag)
    Runs (widths input.length divisor.length) readOnly machine
      (input.length * (8 * divisor.length + 17) + 2 * divisor.length + 6)
      entry (fun _ => 0) (initialFrame (buffer (word input)) divisor old work)
      exit (fun _ => 0) (frame (buffer (word input)) divisor (finish divisor input.reverse work)) := by
  dsimp only
  let work : Workspace := (List.replicate divisor.length false, shifted, difference, result, flag)
  have fits : Fits divisor.length work := ⟨List.length_replicate, shiftedLength, differenceLength, resultLength⟩
  have cleared := (StandardBinaryScan.runs BinaryScan.clear () divisor old oldLength).wire
    clearWiring (widths input.length divisor.length) readOnly
    (by intro name; cases name <;> simp [widths, clearWiring_apply])
    (by intro name premise; cases name <;> simp [readOnly, clearWiring_apply] at premise ⊢)
    (initialFrame (buffer (word input)) divisor old work) (fun _ => 0)
  simp only [StandardBinaryScan.run, BinaryScan.clear_run] at cleared
  have positions : install clearWiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Fin 7 => (0 : ℤ)) = fun _ => 0 := install_self clearWiring _
  rw [positions, clear_initial, clear_install] at cleared
  have iterated := loop_runs input divisor work fits
  have complete := cleared.sequence loopMachine StandardBitFold.entry
    (by intro symbols; simp [MultiTape.wire, StandardBinaryScan.machine]) iterated
  convert complete using 1 <;> first | rfl | ring

theorem finish_fits (bits divisor : List Bool) (work : Workspace)
    (fits : Fits divisor.length work) : Fits divisor.length (finish divisor bits work) := by
  induction bits generalizing work with
  | nil => exact fits
  | cons bit bits hypothesis => exact hypothesis _ (advance_fits bit divisor work fits)

/-- The logical loop computes remainder, independently of initial scratch data. -/
theorem finish_value (bits divisor : List Bool) (work : Workspace)
    (fits : Fits divisor.length work) (bounded : value work.1 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length) :
    value (finish divisor bits work).1 = Binary.prefixValue bits (value work.1) % value divisor := by
  induction bits generalizing work with
  | nil => simpa [finish, Binary.prefixValue] using (Nat.mod_eq_of_lt bounded).symm
  | cons bit bits hypothesis =>
    have nextValue := StandardBinaryDivisionStep.next_value bit work.1 divisor fits.1.symm bounded
      (by simpa only [fits.1] using capacity)
    have positive : 0 < value divisor := by omega
    have nextBound : value (advance bit divisor work).1 < value divisor := by
      change value (StandardBinaryDivisionStep.next bit work.1 divisor) < value divisor
      rw [nextValue]
      exact Nat.mod_lt _ positive
    rw [finish, hypothesis _ (advance_fits bit divisor work fits) nextBound]
    change Binary.prefixValue bits (value (StandardBinaryDivisionStep.next bit work.1 divisor)) % value divisor = _
    rw [nextValue, Binary.prefixValue_mod]
    rfl

/-- An initialized zero remainder yields the ordinary mathematical remainder. -/
theorem result_value (input divisor : List Bool) (shifted difference result : List Symbol) (flag : Symbol)
    (shiftedLength : shifted.length = divisor.length) (differenceLength : difference.length = divisor.length)
    (resultLength : result.length = divisor.length) (positive : 0 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length) :
    value (finish divisor input.reverse
      (List.replicate divisor.length false, shifted, difference, result, flag)).1 = value input % value divisor := by
  have zeroValue : value (List.replicate divisor.length false) = 0 := by
    induction divisor.length with
    | zero => rfl
    | succ count hypothesis => simp [List.replicate_succ, value, hypothesis]
  have correct := finish_value input.reverse divisor
    (List.replicate divisor.length false, shifted, difference, result, flag)
    ⟨List.length_replicate, shiftedLength, differenceLength, resultLength⟩
    (by simpa only [zeroValue] using positive) capacity
  simpa only [zeroValue, Binary.prefixValue_reverse, Nat.mul_zero, Nat.add_zero] using correct

/-- The dividend and divisor are separate inputs, with unary digit capacity.
All five writable tapes have bounded mathematical domains, including scratch. -/
def domains : Sum Unit (Fin 7) → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

def argumentReadOnly : Sum Unit (Fin 7) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 7 ↪ Sum Unit (Fin 7) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Unit ↪ Sum Unit (Fin 7) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def outputTapes : Unit ↪ Sum Unit (Fin 7) := oneTape (.inr 0)

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit (Fin 7))) State :=
  MultiTape.wire dataTapes machine

/-- Polynomial-time remainder under the standard convention. A positive
divisor reserves one shift-capacity bit; zero divisors are outside the hypothesis. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment input =>
      0 < (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ∧
      2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
    (fun assignment input output =>
      (output () : Fin (2 ^ assignment ())).val =
        (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment ())).val %
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire, machine, exit, MultiTape.sequence, loopMachine,
      StandardBitFold.machine, StandardBitFold.exit]),
    8 * MvPolynomial.X () ^ 2 + 19 * MvPolynomial.X () + 6, ?_⟩
  intro assignment input initial valid represented sizes
  let dividend := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  let divisor := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  have dividendLength : dividend.length = assignment () := List.length_ofFn
  have divisorLength : divisor.length = assignment () := List.length_ofFn
  have dividendValue : value dividend = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  have divisorValue : value divisor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldDifference, differenceLength, differenceEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr 5) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 4) rfl
  change flags.length = 1 at flagLength
  obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  have sourceEq : initial (.inr 6) = buffer (word dividend) := represented.1 (.inr 6) rfl
  have divisorEq : initial (.inr 1) = buffer (word divisor) := represented.1 (.inr 1) rfl
  let work : Workspace :=
    (List.replicate divisor.length false, oldShifted, oldDifference, oldResult, oldFlag)
  have oldFits : old.length = divisor.length := oldLength.trans divisorLength.symm
  have shiftedFits : oldShifted.length = divisor.length := shiftedLength.trans divisorLength.symm
  have differenceFits : oldDifference.length = divisor.length := differenceLength.trans divisorLength.symm
  have resultFits : oldResult.length = divisor.length := resultLength.trans divisorLength.symm
  have fits : Fits divisor.length work := ⟨List.length_replicate, shiftedFits, differenceFits, resultFits⟩
  have start : install dataTapes (initialFrame (buffer (word dividend)) divisor old work) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      fin_cases name
      · exact oldEq.symm
      · exact divisorEq.symm
      · exact shiftedEq.symm
      · exact differenceEq.symm
      · exact flagEq.symm
      · exact resultEq.symm
      · exact sourceEq.symm
  have localTrace := runs dividend divisor old oldShifted oldDifference oldResult
    oldFits shiftedFits differenceFits resultFits oldFlag
  have trace := localTrace.wire dataTapes (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains (.inr name)).width assignment = widths dividend.length divisor.length name
      fin_cases name <;> norm_num [domains, EncodedDomain.booleans, EncodedDomain.fixed,
        EncodedDomain.binaryNaturals, widths, dividendLength, divisorLength])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install dataTapes (fun _ : Fin 7 => (0 : ℤ))
      (fun _ : Sum Unit (Fin 7) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let remainder := (finish divisor dividend.reverse work).1
  have remainderFits : remainder.length = assignment () :=
    (finish_fits dividend.reverse divisor work fits).1.trans divisorLength
  have positive : 0 < value divisor := by rw [divisorValue]; exact valid.1
  have capacity : 2 * value divisor ≤ 2 ^ divisor.length := by
    rw [divisorValue, divisorLength]
    exact valid.2
  have correct := result_value dividend divisor oldShifted oldDifference oldResult oldFlag
    shiftedFits differenceFits resultFits positive capacity
  let remainderValue : Fin (2 ^ assignment ()) := ⟨value remainder,
    by simpa only [remainderFits] using Binary.value_lt_pow_length remainder⟩
  let output : Outputs domains outputTapes assignment := fun _ => remainderValue
  refine ⟨dividend.length * (8 * divisor.length + 17) + 2 * divisor.length + 6, output,
    install dataTapes (frame (buffer (word dividend)) divisor (finish divisor dividend.reverse work)) initial,
    ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
    rw [dividendLength, divisorLength]
    nlinarith
  · simpa only [dividendValue, divisorValue] using correct
  · intro name
    cases name
    change install dataTapes _ initial (dataTapes 0) = _
    rw [install_at]
    exact (encoded_binaryNaturals () assignment remainder remainderFits).symm

end Polytime2.StandardBinaryRemainder
