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
import Polytime2.StandardTapeCommands
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
def widths (sourceWidth digits : ℕ) (name : Fin 7) : ℕ :=
  if name = 6 then sourceWidth else if name = 4 then 1 else digits

def readOnly (name : Fin 7) : Bool := decide (name = 1 ∨ name = 6)

def position (sourcePosition : ℤ) (name : Fin 7) : ℤ := if name = 6 then sourcePosition else 0

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

def stepWiring : Fin 6 ↪ Fin 7 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 7 => name.val) equal)⟩


@[simp] theorem stepWiring_apply (name : Fin 6) : stepWiring name = ⟨name.val, by omega⟩ := rfl


noncomputable def stepMachine : Machine Alphabet StandardBinaryDivisionStep.State :=
  MultiTape.wire stepWiring StandardBinaryDivisionStep.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 5 0 (by decide)

abbrev BodyState := Sum StandardBinaryDivisionStep.State (Fin 3)

noncomputable def bodyMachine : Machine Alphabet BodyState :=
  MultiTape.sequence stepMachine copyMachine 0

def bodyEntry (bit : Bool) : BodyState := .inl (StandardBinaryDivisionStep.entry bit)
def bodyExit : BodyState := .inr 2

private def Represents (sourceWidth : ℕ) (divisor current : List Bool) (tapes : Tapes Alphabet) : Prop :=
  current.length = divisor.length ∧ tapes 0 = buffer (word current) ∧
    tapes 1 = buffer (word divisor) ∧
    ∀ name, name ≠ 6 → Region (widths sourceWidth divisor.length name) 0 (tapes name)

private theorem represents_cursor (sourceWidth : ℕ) (divisor current : List Bool)
    (tapes : Tapes Alphabet) (source : Turing.Tape Symbol)
    (represented : Represents sourceWidth divisor current tapes) :
    Represents sourceWidth divisor current (StandardBitFold.frame 6 id source tapes) := by
  rcases represented with ⟨length, currentEq, divisorEq, regions⟩
  refine ⟨length, currentEq, divisorEq, ?_⟩
  intro name different
  simpa [StandardBitFold.frame, different] using regions name different

/-- One body call returns only the live remainder; private scratch stays bounded. -/
private theorem body_runs (bit : Bool) (divisor current : List Bool) (sourceWidth : ℕ)
    (initial : Tapes Alphabet) (represented : Represents sourceWidth divisor current initial) :
    ∃ final, Runs (widths sourceWidth divisor.length) readOnly bodyMachine (8 * divisor.length + 13)
      (bodyEntry bit) (fun _ => 0) initial bodyExit (fun _ => 0) final ∧
      Represents sourceWidth divisor (StandardBinaryDivisionStep.next bit current divisor) final := by
  rcases represented with ⟨length, currentEq, divisorEq, regions⟩
  obtain ⟨shifted, shiftedLength, shiftedEq⟩ := (regions 2 (by decide)).exists_buffer
  obtain ⟨difference, differenceLength, differenceEq⟩ := (regions 3 (by decide)).exists_buffer
  obtain ⟨result, resultLength, resultEq⟩ := (regions 5 (by decide)).exists_buffer
  obtain ⟨flags, flagLength, flagEq⟩ := (regions 4 (by decide)).exists_buffer
  change flags.length = 1 at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  obtain ⟨after, first, located, outside, immutable⟩ :=
    (StandardBinaryDivisionStep.runs bit current divisor length.symm shifted difference result
      (shiftedLength.trans length.symm) (differenceLength.trans length.symm)
      (resultLength.trans length.symm) flag).wire_restoring
      stepWiring (widths sourceWidth divisor.length) readOnly
      (by intro name; fin_cases name <;> simp [widths, StandardBinaryDivisionStep.widths, length])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (by intro name; fin_cases name <;> assumption)
  let next := StandardBinaryDivisionStep.next bit current divisor
  have nextLength : next.length = divisor.length := (next_length bit current divisor length.symm).trans length
  have copied := StandardTapeCommands.copy_runs (5 : Fin 7) 0 (by decide)
    (widths sourceWidth divisor.length) readOnly rfl next (word current)
    nextLength.symm nextLength.symm (by simp [word, nextLength, length]) after (located 5) (located 0)
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryDivisionStep.machine,
      StandardBinaryDivisionStep.exit, MultiTape.sequence, StandardBinaryDivisionStep.reduceMachine,
      StandardBinaryReduce.machine, StandardBinaryReduce.exit, StandardBinaryReduce.selection, MultiTape.withExit]) copied
  refine ⟨Function.update after 0 (buffer (word next)), ?_, nextLength, Function.update_self _ _ _, ?_, ?_⟩
  · convert complete using 1 <;> first | rfl | omega
  · exact (complete.readOnly_tape 1 rfl).trans divisorEq
  · intro name different
    exact complete.region name (regions name different)

noncomputable def clearMachine : Machine Alphabet (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear 1 0 (by decide)
abbrev LoopState := StandardBitFold.State BodyState
noncomputable def loopMachine : Machine Alphabet LoopState := StandardBitFold.machine 6 bodyMachine bodyEntry
abbrev State := Sum (StandardBinaryScan.State Unit) LoopState
noncomputable def machine : Machine Alphabet State := MultiTape.sequence clearMachine loopMachine StandardBitFold.entry
def entry : State := .inl (.inl ())
def exit : State := .inr StandardBitFold.exit

/-- The logical recurrence contains no scratch words. -/
def finish (divisor bits current : List Bool) : List Bool :=
  StandardBitFold.fold (fun bit current => StandardBinaryDivisionStep.next bit current divisor) bits current

theorem finish_length (divisor bits current : List Bool) (length : current.length = divisor.length) :
    (finish divisor bits current).length = divisor.length := by
  induction bits generalizing current with
  | nil => exact length
  | cons bit bits hypothesis => exact hypothesis _ ((next_length bit current divisor length.symm).trans length)

/-- The logical accumulator computes remainder independently of private contents. -/
theorem finish_value (bits divisor current : List Bool) (length : current.length = divisor.length)
    (bounded : value current < value divisor) (capacity : 2 * value divisor ≤ 2 ^ divisor.length) :
    value (finish divisor bits current) = Binary.prefixValue bits (value current) % value divisor := by
  induction bits generalizing current with
  | nil => simpa [finish, StandardBitFold.fold, Binary.prefixValue] using (Nat.mod_eq_of_lt bounded).symm
  | cons bit bits hypothesis =>
    have nextValue := StandardBinaryDivisionStep.next_value bit current divisor length.symm bounded
      (by simpa only [length] using capacity)
    have nextBound : value (StandardBinaryDivisionStep.next bit current divisor) < value divisor := by
      rw [nextValue]
      exact Nat.mod_lt _ (by omega)
    change value (finish divisor bits (StandardBinaryDivisionStep.next bit current divisor)) = _
    rw [hypothesis _ ((next_length bit current divisor length.symm).trans length) nextBound]
    rw [nextValue, Binary.prefixValue_mod]
    rfl

theorem result_value (input divisor : List Bool) (positive : 0 < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ divisor.length) :
    value (finish divisor input.reverse (List.replicate divisor.length false)) = value input % value divisor := by
  simpa [Binary.prefixValue_reverse] using finish_value input.reverse divisor
    (List.replicate divisor.length false) List.length_replicate (by simpa using positive) capacity

private theorem loop_runs (input divisor current : List Bool) (initial : Tapes Alphabet)
    (source : initial 6 = buffer (word input)) (represented : Represents input.length divisor current initial) :
    ∃ final, Runs (widths input.length divisor.length) readOnly loopMachine
      (input.length * (8 * divisor.length + 17) + 3) StandardBitFold.entry (fun _ => 0) initial
      StandardBitFold.exit (fun _ => 0) final ∧ Represents input.length divisor (finish divisor input.reverse current) final := by
  apply StandardBitFold.runsValues 6 bodyMachine bodyEntry (widths input.length divisor.length) readOnly
    (fun bit current => StandardBinaryDivisionStep.next bit current divisor)
    (Represents input.length divisor) (by intro value tapes source valid; exact represents_cursor _ _ _ _ _ valid)
    rfl bodyExit (8 * divisor.length + 13)
    (by intro symbols; simp [bodyMachine, bodyExit, MultiTape.sequence, copyMachine,
      StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) ?_ input current initial source represented
  intro bit current tapes valid source offset
  obtain ⟨final, trace, correct⟩ := body_runs bit divisor current input.length
    (StandardBitFold.frame 6 id source tapes) (represents_cursor _ _ _ _ _ valid)
  refine ⟨final, ?_, correct⟩
  have shifted := trace.regions (widths input.length divisor.length) (position offset)
    (by intro name writable; fin_cases name <;> simp_all [position, readOnly])
  convert shifted using 1 <;> funext name <;> simp [position, StandardBitFold.position]

/-- Runtime-width long remainder accepts arbitrary private regions and specifies
only its result. Every head is restored and the immutable operands are preserved. -/
theorem runs (input divisor : List Bool) (initial : Tapes Alphabet)
    (sourceEq : initial 6 = buffer (word input)) (divisorEq : initial 1 = buffer (word divisor))
    (regions : ∀ name, Region (widths input.length divisor.length name) 0 (initial name)) :
    ∃ final, Runs (widths input.length divisor.length) readOnly machine
      (input.length * (8 * divisor.length + 17) + 2 * divisor.length + 6)
      entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final 0 = buffer (word (finish divisor input.reverse (List.replicate divisor.length false))) := by
  obtain ⟨old, oldLength, oldEq⟩ := (regions 0).exists_buffer
  have cleared := StandardTapeCommands.clear_runs (1 : Fin 7) 0 (by decide)
    (widths input.length divisor.length) readOnly rfl divisor old rfl rfl oldLength initial divisorEq oldEq
  let prepared := Function.update initial 0 (buffer (word (List.replicate divisor.length false)))
  have represented : Represents input.length divisor (List.replicate divisor.length false) prepared := by
    refine ⟨List.length_replicate, Function.update_self _ _ _, ?_, ?_⟩
    · exact divisorEq
    · intro name different
      exact cleared.region name (regions name)
  obtain ⟨final, iterated, length, result, preserved, finalRegions⟩ :=
    loop_runs input divisor (List.replicate divisor.length false) prepared sourceEq represented
  have complete := cleared.sequence loopMachine StandardBitFold.entry
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) iterated
  refine ⟨final, ?_, result⟩
  convert complete using 1 <;> first | rfl | ring

/-- The dividend and divisor are separate inputs, with unary digit capacity.
All five writable tapes have bounded mathematical domains, including scratch. -/
noncomputable def domains : Sum Unit (Fin 7) → EncodedDomain Unit
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

/-- Polynomial-time remainder needs one capacity bit beyond a positive divisor. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment input =>
      0 < (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ∧
      2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
    (fun assignment input output =>
      (output () : Fin (2 ^ assignment ())).val =
        (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment ())).val %
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [algorithm, MultiTape.wire, machine, exit, MultiTape.sequence,
      loopMachine, StandardBitFold.machine, StandardBitFold.exit]),
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
  have sourceEq : initial (.inr 6) = buffer (word dividend) :=
    (represented.1 (.inr 6) rfl).trans (encoded_binaryNaturals_value () assignment _)
  have divisorEq : initial (.inr 1) = buffer (word divisor) :=
    (represented.1 (.inr 1) rfl).trans (encoded_binaryNaturals_value () assignment _)
  have widthsMatch : ∀ name, (domains (.inr name)).width assignment = widths dividend.length divisor.length name := by
    intro name
    fin_cases name <;> norm_num [domains, widths, EncodedDomain.booleans, EncodedDomain.fixed,
      EncodedDomain.binaryNaturals, dividendLength, divisorLength]
  obtain ⟨localFinal, localTrace, result⟩ := runs dividend divisor (fun name => initial (.inr name))
    sourceEq divisorEq (by intro name; rw [← widthsMatch]; exact represented.region (.inr name))
  obtain ⟨final, trace, located, outside, immutable⟩ := localTrace.wire_restoring dataTapes
    (fun name => (domains name).width assignment) argumentReadOnly widthsMatch
    (by intro name premise; exact premise) initial (fun _ => rfl)
  let remainder := finish divisor dividend.reverse (List.replicate divisor.length false)
  have remainderLength : remainder.length = assignment () :=
    (finish_length divisor dividend.reverse _ List.length_replicate).trans divisorLength
  have correct : value remainder = value dividend % value divisor :=
    result_value dividend divisor (by rw [divisorValue]; exact valid.1)
      (by rw [divisorValue, divisorLength]; exact valid.2)
  let remainderValue : Fin (2 ^ assignment ()) := ⟨value remainder,
    by simpa only [remainderLength] using Binary.value_lt_pow_length remainder⟩
  refine ⟨_, (fun _ => remainderValue), final, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
    rw [dividendLength, divisorLength]
    nlinarith
  · simpa only [dividendValue, divisorValue] using correct
  · intro name
    cases name
    exact ((located 0).trans result).trans (encoded_binaryNaturals () assignment remainder remainderLength).symm

end Polytime2.StandardBinaryRemainder
