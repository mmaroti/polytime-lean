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

import Polytime2.Arithmetic.DivisionMath
import Polytime2.Primitives.TapeCommands

/-! # Binary long division with shared quotient and remainder storage

One high-bit-first pass computes both results. The quotient accumulator reuses
the shifted-remainder scratch after each remainder step. Operands remain
immutable, private regions may contain arbitrary symbols, and heads restore.
-/

namespace Polytime2.StandardBinaryDivision

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 8 => Symbol

def widths (sourceWidth digits : ℕ) (name : Fin 8) : ℕ :=
  if name = 6 then sourceWidth else if name = 4 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 1 ∨ name = 6)

def position (sourcePosition : ℤ) (name : Fin 8) : ℤ := if name = 6 then sourcePosition else 0

def stepWiring : Fin 6 ↪ Fin 8 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 8 => name.val) equal)⟩

@[simp] theorem stepWiring_apply (name : Fin 6) : stepWiring name = ⟨name.val, by omega⟩ := rfl

noncomputable def stepMachine : Machine Alphabet StandardBinaryDivisionStep.State :=
  MultiTape.wire stepWiring StandardBinaryDivisionStep.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 5 0 (by decide)

noncomputable def shiftQuotient : Machine Alphabet (StandardBinaryScan.State Bool) :=
  StandardTapeCommands.scan BinaryScan.shift 7 2 (by decide)

def quotientCondition (symbols : Symbols Alphabet) : Bool := symbols 4 == 1

abbrev QuotientSelectionState :=
  Sum (Sum Unit (Sum (StandardBinaryScan.State Bool) (StandardBinaryScan.State Bool))) Unit

noncomputable def selectQuotient : Machine Alphabet QuotientSelectionState :=
  MultiTape.withExit (branchMachine quotientCondition shiftQuotient shiftQuotient (.inl true) (.inl false))

noncomputable def copyQuotient : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 2 7 (by decide)

abbrev QuotientState := Sum QuotientSelectionState (Fin 3)
noncomputable def quotientMachine : Machine Alphabet QuotientState :=
  MultiTape.sequence selectQuotient copyQuotient 0

def quotientEntry : QuotientState := .inl (.inl (.inl ()))
def quotientExit : QuotientState := .inr 2

private theorem quotient_runs (sourceWidth : ℕ) (quotient : List Bool) (borrowed : Bool)
    (initial : Tapes Alphabet) (sourceEq : initial 7 = buffer (word quotient))
    (flagEq : initial 4 = buffer [data borrowed])
    (region : Region quotient.length 0 (initial 2)) :
    ∃ final, Runs (widths sourceWidth quotient.length) readOnly quotientMachine
      (4 * quotient.length + 7) quotientEntry (fun _ => 0) initial quotientExit (fun _ => 0) final ∧
      final 7 = buffer (word (BinaryScan.run BinaryScan.shift (!borrowed) quotient).2) ∧
      final 0 = initial 0 := by
  obtain ⟨old, oldLength, oldEq⟩ := region.exists_buffer
  let shifted := (BinaryScan.run BinaryScan.shift (!borrowed) quotient).2
  have shiftedLength : shifted.length = quotient.length := BinaryScan.run_length _ _ _
  have scan := StandardTapeCommands.scan_runs BinaryScan.shift (!borrowed) (7 : Fin 8) 2
    (by decide) (widths sourceWidth quotient.length) readOnly rfl quotient old rfl rfl
    oldLength initial sourceEq oldEq
  have selected : Runs (widths sourceWidth quotient.length) readOnly selectQuotient
      (2 * quotient.length + 4) (.inl (.inl ())) (fun _ => 0) initial
      (.inr ()) (fun _ => 0) (Function.update initial 2 (buffer (word shifted))) := by
    cases borrowed with
    | false =>
      exact scan.branch_true quotientCondition shiftQuotient (.inl false)
        (by simp [quotientCondition, MultiTape.read, flagEq, buffer, data,
          Turing.Tape.mk₁, Turing.Tape.mk₂])
        (by intro symbols; simp [shiftQuotient, StandardTapeCommands.scan, MultiTape.wire,
          StandardBinaryScan.machine])
    | true =>
      exact scan.branch_false quotientCondition shiftQuotient (.inl true)
        (by simp [quotientCondition, MultiTape.read, flagEq, buffer, data,
          Turing.Tape.mk₁, Turing.Tape.mk₂])
        (by intro symbols; simp [shiftQuotient, StandardTapeCommands.scan, MultiTape.wire,
          StandardBinaryScan.machine])
  let after := Function.update initial 2 (buffer (word shifted))
  have copied := StandardTapeCommands.copy_runs (2 : Fin 8) 7 (by decide)
    (widths sourceWidth quotient.length) readOnly rfl shifted (word quotient)
    shiftedLength.symm shiftedLength.symm (by simp [word, shiftedLength]) after
    (Function.update_self _ _ _) sourceEq
  have complete := selected.sequence copyQuotient 0
    (by intro symbols; simp [selectQuotient, MultiTape.withExit]) copied
  refine ⟨Function.update after 7 (buffer (word shifted)), ?_, Function.update_self _ _ _, ?_⟩
  · convert complete using 1 <;> first | rfl | omega
  · simp [after]

abbrev BodyState := Sum StandardBinaryDivisionStep.State (Sum (Fin 3) QuotientState)

noncomputable def bodyMachine : Machine Alphabet BodyState :=
  MultiTape.sequence stepMachine (MultiTape.sequence copyMachine quotientMachine quotientEntry) (.inl 0)

def bodyEntry (bit : Bool) : BodyState := .inl (StandardBinaryDivisionStep.entry bit)
def bodyExit : BodyState := .inr (.inr quotientExit)

private def Represents (sourceWidth : ℕ) (divisor : List Bool)
    (current : List Bool × List Bool) (tapes : Tapes Alphabet) : Prop :=
  current.1.length = divisor.length ∧ current.2.length = divisor.length ∧
    tapes 7 = buffer (word current.1) ∧ tapes 0 = buffer (word current.2) ∧
    tapes 1 = buffer (word divisor) ∧
    ∀ name, name ≠ 6 → Region (widths sourceWidth divisor.length name) 0 (tapes name)

private theorem represents_cursor (sourceWidth : ℕ) (divisor : List Bool)
    (current : List Bool × List Bool) (tapes : Tapes Alphabet) (source : Turing.Tape Symbol)
    (represented : Represents sourceWidth divisor current tapes) :
    Represents sourceWidth divisor current (StandardBitFold.frame 6 id source tapes) := by
  rcases represented with ⟨quotientLength, remainderLength, quotientEq, remainderEq, divisorEq, regions⟩
  refine ⟨quotientLength, remainderLength, ?_, ?_, ?_, ?_⟩
  · simpa [StandardBitFold.frame] using quotientEq
  · simpa [StandardBitFold.frame] using remainderEq
  · simpa [StandardBitFold.frame] using divisorEq
  · intro name different
    simpa [StandardBitFold.frame, different] using regions name different

private theorem body_runs (bit : Bool) (divisor : List Bool)
    (current : List Bool × List Bool) (sourceWidth : ℕ)
    (initial : Tapes Alphabet) (represented : Represents sourceWidth divisor current initial) :
    ∃ final, Runs (widths sourceWidth divisor.length) readOnly bodyMachine
      (12 * divisor.length + 21) (bodyEntry bit) (fun _ => 0) initial
      bodyExit (fun _ => 0) final ∧ Represents sourceWidth divisor (next bit divisor current) final := by
  rcases represented with ⟨quotientLength, length, quotientEq, currentEq, divisorEq, regions⟩
  obtain ⟨shifted, shiftedLength, shiftedEq⟩ := (regions 2 (by decide)).exists_buffer
  obtain ⟨difference, differenceLength, differenceEq⟩ := (regions 3 (by decide)).exists_buffer
  obtain ⟨result, resultLength, resultEq⟩ := (regions 5 (by decide)).exists_buffer
  obtain ⟨flags, flagLength, flagEq⟩ := (regions 4 (by decide)).exists_buffer
  change flags.length = 1 at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  obtain ⟨after, first, located, outside, immutable⟩ :=
    (StandardBinaryDivisionStep.runs bit current.2 divisor length.symm shifted difference result
      (shiftedLength.trans length.symm) (differenceLength.trans length.symm)
      (resultLength.trans length.symm) flag).wire_restoring
      stepWiring (widths sourceWidth divisor.length) readOnly
      (by intro name; fin_cases name <;> simp [widths, StandardBinaryDivisionStep.widths, length])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (by intro name; fin_cases name <;> assumption)
  let nextRemainder := StandardBinaryDivisionStep.next bit current.2 divisor
  have lengths := next_lengths bit divisor current quotientLength length
  have nextLength : nextRemainder.length = divisor.length := lengths.2
  have copied := StandardTapeCommands.copy_runs (5 : Fin 8) 0 (by decide)
    (widths sourceWidth divisor.length) readOnly rfl nextRemainder (word current.2)
    nextLength.symm nextLength.symm (by simp [word, nextLength, length]) after (located 5) (located 0)
  let changed := Function.update after 0 (buffer (word nextRemainder))
  have afterQuotient : changed 7 = buffer (word current.1) := by
    have kept := outside 7 (by rintro ⟨name, equal⟩; fin_cases name <;> cases equal)
    exact kept.trans quotientEq
  have afterFlag : changed 4 = buffer [data (BinarySubtraction.ripple false
      (StandardBinaryDivisionStep.shifted bit current.2) divisor).2] := located 4
  have changedRegion : Region current.1.length 0 (changed 2) := by
    simpa [quotientLength, widths, changed] using copied.region 2 (first.region 2 (regions 2 (by decide)))
  obtain ⟨final, quotientTrace, nextQuotient, keptRemainder⟩ := quotient_runs sourceWidth current.1
    (BinarySubtraction.ripple false (StandardBinaryDivisionStep.shifted bit current.2) divisor).2
    changed afterQuotient afterFlag changedRegion
  rw [quotientLength] at quotientTrace
  have rest := copied.sequence quotientMachine quotientEntry
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire,
      StandardTerminatedCopy.machine]) quotientTrace
  have complete := first.sequence (MultiTape.sequence copyMachine quotientMachine quotientEntry) (.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardBinaryDivisionStep.machine,
      StandardBinaryDivisionStep.exit, MultiTape.sequence, StandardBinaryDivisionStep.reduceMachine,
      StandardBinaryReduce.machine, StandardBinaryReduce.exit, StandardBinaryReduce.selection, MultiTape.withExit]) rest
  refine ⟨final, ?_, lengths.1, lengths.2, nextQuotient, ?_, ?_, ?_⟩
  · convert complete using 1 <;> first | rfl | (simp only [length, nextLength]; ring)
  · exact keptRemainder.trans (Function.update_self _ _ _)
  · exact (complete.readOnly_tape 1 rfl).trans divisorEq
  · intro name different
    exact complete.region name (regions name different)

noncomputable def clearRemainder : Machine Alphabet (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear 1 0 (by decide)
noncomputable def clearQuotient : Machine Alphabet (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear 1 7 (by decide)

abbrev LoopState := StandardBitFold.State BodyState
noncomputable def loopMachine : Machine Alphabet LoopState := StandardBitFold.machine 6 bodyMachine bodyEntry
abbrev State := Sum (StandardBinaryScan.State Unit) (Sum (StandardBinaryScan.State Unit) LoopState)
noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence clearRemainder
    (MultiTape.sequence clearQuotient loopMachine StandardBitFold.entry) (.inl (.inl ()))
def entry : State := .inl (.inl ())
def exit : State := .inr (.inr StandardBitFold.exit)

private theorem loop_runs (input divisor : List Bool) (current : List Bool × List Bool)
    (initial : Tapes Alphabet) (source : initial 6 = buffer (word input))
    (represented : Represents input.length divisor current initial) :
    ∃ final, Runs (widths input.length divisor.length) readOnly loopMachine
      (input.length * (12 * divisor.length + 25) + 3) StandardBitFold.entry (fun _ => 0) initial
      StandardBitFold.exit (fun _ => 0) final ∧
      Represents input.length divisor (finish divisor input.reverse current) final := by
  apply StandardBitFold.runsValues 6 bodyMachine bodyEntry (widths input.length divisor.length) readOnly
    (fun bit current => next bit divisor current) (Represents input.length divisor)
    (by intro value tapes source valid; exact represents_cursor _ _ _ _ _ valid)
    rfl bodyExit (12 * divisor.length + 21)
    (by intro symbols; simp [bodyMachine, bodyExit, MultiTape.sequence, quotientMachine,
      quotientExit, copyQuotient, StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine])
    ?_ input current initial source represented
  intro bit current tapes valid source offset
  obtain ⟨final, trace, correct⟩ := body_runs bit divisor current input.length
    (StandardBitFold.frame 6 id source tapes) (represents_cursor _ _ _ _ _ valid)
  refine ⟨final, ?_, correct⟩
  have shifted := trace.regions (widths input.length divisor.length) (position offset)
    (by intro name writable; fin_cases name <;> simp_all [position, readOnly])
  convert shifted using 1 <;> funext name <;> simp [position, StandardBitFold.position]

/-- One pass returns both words, preserving the operands and restoring all heads. -/
theorem runs (input divisor : List Bool) (initial : Tapes Alphabet)
    (sourceEq : initial 6 = buffer (word input)) (divisorEq : initial 1 = buffer (word divisor))
    (regions : ∀ name, Region (widths input.length divisor.length name) 0 (initial name)) :
    ∃ final, Runs (widths input.length divisor.length) readOnly machine
      (input.length * (12 * divisor.length + 25) + 4 * divisor.length + 9)
      entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final 7 = buffer (word (finish divisor input.reverse
        (List.replicate divisor.length false, List.replicate divisor.length false)).1) ∧
      final 0 = buffer (word (finish divisor input.reverse
        (List.replicate divisor.length false, List.replicate divisor.length false)).2) := by
  obtain ⟨oldRemainder, remainderLength, remainderEq⟩ := (regions 0).exists_buffer
  have clearedRemainder := StandardTapeCommands.clear_runs (1 : Fin 8) 0 (by decide)
    (widths input.length divisor.length) readOnly rfl divisor oldRemainder rfl rfl
    remainderLength initial divisorEq remainderEq
  let afterRemainder := Function.update initial 0 (buffer (word (List.replicate divisor.length false)))
  obtain ⟨oldQuotient, quotientLength, quotientEq⟩ := (clearedRemainder.region 7 (regions 7)).exists_buffer
  have clearedQuotient := StandardTapeCommands.clear_runs (1 : Fin 8) 7 (by decide)
    (widths input.length divisor.length) readOnly rfl divisor oldQuotient rfl rfl
    quotientLength afterRemainder divisorEq quotientEq
  let prepared := Function.update afterRemainder 7 (buffer (word (List.replicate divisor.length false)))
  have represented : Represents input.length divisor
      (List.replicate divisor.length false, List.replicate divisor.length false) prepared := by
    refine ⟨List.length_replicate, List.length_replicate, Function.update_self _ _ _, ?_, ?_, ?_⟩
    · simp [prepared, afterRemainder]
    · exact divisorEq
    · intro name different
      exact clearedQuotient.region name (clearedRemainder.region name (regions name))
  obtain ⟨final, iterated, quotientLength, remainderLength, quotientResult, remainderResult,
    divisorPreserved, finalRegions⟩ := loop_runs input divisor
      (List.replicate divisor.length false, List.replicate divisor.length false) prepared sourceEq represented
  have rest := clearedQuotient.sequence loopMachine StandardBitFold.entry
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) iterated
  have complete := clearedRemainder.sequence
    (MultiTape.sequence clearQuotient loopMachine StandardBitFold.entry) (.inl (.inl ()))
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) rest
  refine ⟨final, ?_, quotientResult, remainderResult⟩
  convert complete using 1 <;> first | rfl | ring

end Polytime2.StandardBinaryDivision
