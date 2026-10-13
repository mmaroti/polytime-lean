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

import Polytime2.StandardBinaryIncrement
import Polytime2.StandardCounterZero

/-! # Reading a unary size into a fixed-width binary counter

Both size tapes are immutable. The result and scratch counters are first
cleared using their unary capacity, then incremented once per size symbol.
-/

namespace Polytime2.StandardSizeRead

open MultiTape CallingConvention
open Binary (Symbol data word)

abbrev Alphabet := CallingConvention.Alphabet (Fin 4)
abbrev LoopState := Sum Unit (Sum (StandardBinaryScan.State Bool) (Fin 3))
abbrev InitialState := Sum (StandardBinaryScan.State Unit) (StandardBinaryScan.State Unit)
abbrev State := Sum (Sum InitialState (Sum LoopState Unit)) (Sum (Fin 2) (Fin 3))

def widths (count capacity : ℕ) (name : Fin 4) : ℕ :=
  if name = 0 then count else capacity

def readOnly (name : Fin 4) : Bool := decide (name.val < 2)

def position (processed : ℤ) (name : Fin 4) : ℤ := if name = 0 then processed else 0

def frame (processed remaining capacity : ℕ) (result : List Bool)
    (scratch : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then Turing.Tape.mk'
    (Turing.ListBlank.mk (List.replicate processed 2 ++ [0]))
    (Turing.ListBlank.mk (List.replicate remaining 2 ++ [0]))
  else if name = 1 then unary capacity
  else if name = 2 then buffer (word result) else buffer scratch

noncomputable def prepareCounters : Machine Alphabet InitialState :=
  MultiTape.sequence (StandardTapeCommands.clear 1 2 (by decide))
    (StandardTapeCommands.clear 1 3 (by decide)) (.inl ())

noncomputable def increment : Machine Alphabet (StandardBinaryScan.State Bool) :=
  MultiTape.wire (twoTapes 2 3 (by decide)) (StandardBinaryScan.machine BinaryScan.increment)

noncomputable def copy : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 3 2 (by decide)

noncomputable def loop : Machine Alphabet LoopState
  | .inl _, symbols => if symbols 0 = 0 then none
      else some (.inr (.inl (.inl true)), stationary symbols)
  | .inr (.inl state), symbols => match increment state symbols with
    | some (next, actions) => some (.inr (.inl next), actions)
    | none => some (.inr (.inr 0), stationary symbols)
  | .inr (.inr state), symbols => match copy state symbols with
    | some (next, actions) => some (.inr (.inr next), actions)
    | none => some (.inl (), fun name => (symbols name, if name = 0 then some .right else none))

noncomputable def restore : Machine Alphabet (Sum (Fin 2) (Fin 3)) :=
  MultiTape.wire (oneTape 0) StandardHead.BlankReturn.fromEnd

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence
    (MultiTape.sequence prepareCounters (MultiTape.withExit loop) (.inl (.inl ()))) restore (.inl 1)

def entry : State := .inl (.inl (.inl (.inl ())))
def exit : State := .inr (.inr 2)

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, restore, MultiTape.sequence, MultiTape.wire,
    StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]

/-- One increment preserves the size tapes and current result while replacing
all scratch digits, including arbitrary blank initial digits. -/
theorem increment_runs (processed remaining capacity : ℕ) (result : List Bool)
    (resultLength : result.length = capacity) (scratch : List Symbol)
    (scratchLength : scratch.length = capacity) :
    Runs (widths (processed + remaining) capacity) readOnly increment (2 * capacity + 2)
      (.inl true) (position processed) (frame processed remaining capacity result scratch)
      (.inr ((BinaryScan.run BinaryScan.increment true result).1, true)) (position processed)
      (frame processed remaining capacity result
        (word (BinaryScan.run BinaryScan.increment true result).2)) := by
  let initial := frame processed remaining capacity result scratch
  let final := frame processed remaining capacity result
    (word (BinaryScan.run BinaryScan.increment true result).2)
  have trace := (StandardBinaryScan.runs BinaryScan.increment true result scratch
    (scratchLength.trans resultLength.symm)).wire_of_eq (twoTapes (2 : Fin 4) 3 (by decide))
    (widths (processed + remaining) capacity) readOnly
    (by intro name; cases name <;> simpa [widths] using resultLength.symm)
    (by intro name premise; cases name <;> first | rfl | contradiction)
    initial final
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · rfl
      · rfl
      · exact False.elim (outside ⟨false, rfl⟩)
      · exact False.elim (outside ⟨true, rfl⟩))
  have offsetTrace := trace.regions (widths (processed + remaining) capacity) (position processed) (by
    intro name writable
    fin_cases name <;> first | contradiction | simp [widths, position])
  simpa only [zero_add, resultLength, increment, initial, final] using offsetTrace

/-- Repeated increment retains the same binary capacity. -/
def advanceBits : ℕ → List Bool → List Bool
  | 0, bits => bits
  | count + 1, bits => advanceBits count (BinaryScan.run BinaryScan.increment true bits).2

@[simp] theorem advanceBits_length (count : ℕ) (bits : List Bool) :
    (advanceBits count bits).length = bits.length := by
  induction count generalizing bits <;> simp_all [advanceBits]

/-- Reading a unary count computes addition modulo the fixed binary capacity. -/
theorem advanceBits_value (count : ℕ) (bits : List Bool) :
    Binary.value (advanceBits count bits) = (Binary.value bits + count) % 2 ^ bits.length := by
  induction count generalizing bits with
  | zero => simp [advanceBits, Nat.mod_eq_of_lt (Binary.value_lt_pow_length bits)]
  | succ count hypothesis =>
    rw [advanceBits, hypothesis]
    simp only [BinaryScan.run_length, BinaryScan.increment_value]
    rw [Nat.mod_add_mod]
    congr 1
    omega

private theorem stationary_run (processed remaining capacity : ℕ) (tapes : Tapes Alphabet)
    (state next : LoopState)
    (instruction : loop state (MultiTape.read tapes) = some (next, stationary (MultiTape.read tapes))) :
    Runs (widths (processed + remaining) capacity) readOnly loop 1
      state (position processed) tapes next (position processed) tapes := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [act_stationary, stationary, displacement, add_zero] using
    Runs.zero (machine := loop) next (position processed) tapes

/-- The size head advances by one unary symbol per increment. All other heads
stay restored between calls; both counters remain canonical at loop boundaries. -/
theorem loop_runs (processed remaining capacity : ℕ) (result scratch : List Bool)
    (resultLength : result.length = capacity) (scratchLength : scratch.length = capacity) :
    ∃ finalScratch : List Bool, finalScratch.length = capacity ∧
      Runs (widths (processed + remaining) capacity) readOnly loop
        (remaining * (4 * capacity + 7)) (.inl ()) (position processed)
        (frame processed remaining capacity result (word scratch))
        (.inl ()) (position (processed + remaining))
        (frame (processed + remaining) 0 capacity (advanceBits remaining result) (word finalScratch)) := by
  induction remaining generalizing processed result scratch with
  | zero =>
    refine ⟨scratch, scratchLength, ?_⟩
    simpa [advanceBits] using
      (Runs.zero (machine := loop) (.inl ()) (position processed) (frame processed 0 capacity result (word scratch)))
  | succ remaining hypothesis =>
    let next := (BinaryScan.run BinaryScan.increment true result).2
    have nextLength : next.length = capacity := by simpa [next] using resultLength
    let initial := frame processed (remaining + 1) capacity result (word scratch)
    let incremented := frame processed (remaining + 1) capacity result (word next)
    let copied := frame processed (remaining + 1) capacity next (word next)
    have chosen := stationary_run processed (remaining + 1) capacity initial (.inl ())
      (.inr (.inl (.inl true))) (by simp [loop, initial, frame, MultiTape.read, List.replicate_succ])
    have increased := (increment_runs processed (remaining + 1) capacity result resultLength (word scratch)
      (by simpa [word] using scratchLength)).rename (fun state => .inr (.inl state))
      (target := loop) (by intro state symbols next actions instruction; simp [loop, instruction])
    have toCopy := stationary_run processed (remaining + 1) capacity incremented
      (.inr (.inl (.inr ((BinaryScan.run BinaryScan.increment true result).1, true))))
      (.inr (.inr 0)) (by simp [loop, increment, MultiTape.wire, StandardBinaryScan.machine])
    have copyTrace := StandardTapeCommands.copy_runs (3 : Fin 4) 2 (by decide)
      (widths (processed + (remaining + 1)) capacity) readOnly rfl next (word result)
      (by simpa [widths] using nextLength.symm) (by simpa [widths] using nextLength.symm)
      (by simp [word, resultLength, nextLength]) incremented rfl rfl
    have copiedEq : Function.update incremented 2 (buffer (word next)) = copied := by
      funext name
      fin_cases name <;> simp [incremented, copied, frame]
    rw [copiedEq] at copyTrace
    have copyOffset := copyTrace.regions (widths (processed + (remaining + 1)) capacity)
      (position processed) (by intro name writable; fin_cases name <;> first | contradiction | simp [widths, position])
    simp only [zero_add, nextLength] at copyOffset
    have copiedRun := copyOffset.rename (fun state => .inr (.inr state)) (target := loop)
      (by
        intro state symbols next actions instruction
        change copy state symbols = some (next, actions) at instruction
        simp [loop, instruction])
    obtain ⟨finalScratch, finalLength, rest⟩ :=
      hypothesis (processed + 1) next next nextLength nextLength
    have widthsEqual : processed + (remaining + 1) = processed + 1 + remaining := by omega
    rw [← widthsEqual] at rest
    have stepToCheck : Runs (widths (processed + (remaining + 1)) capacity) readOnly loop 1
        (.inr (.inr 2)) (position processed) copied
        (.inl ()) (position (processed + 1))
        (frame (processed + 1) remaining capacity next (word next)) := by
      apply Runs.next (nextState := Sum.inl ())
        (actions := fun name => (MultiTape.read copied name, if name = 0 then some .right else none))
        (by simp [loop, copy, StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine])
        (by intro name premise; rfl)
      have positions : (fun name => position processed name +
          displacement (if name = 0 then some Turing.Dir.right else none)) = position (processed + 1) := by
        funext name
        fin_cases name <;> simp [position, displacement]
      have moved : act (fun name => (MultiTape.read copied name, if name = 0 then some Turing.Dir.right else none)) copied =
          frame (processed + 1) remaining capacity next (word next) := by
        funext name
        fin_cases name <;>
          simp [copied, frame, act, MultiTape.read, Turing.Tape.write_self, List.replicate_succ,
            Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      rw [positions, moved]
      exact Runs.zero (machine := loop) (.inl ()) (position (processed + 1))
        (frame (processed + 1) remaining capacity next (word next))
    have complete := chosen.trans (increased.trans (toCopy.trans (copiedRun.trans (stepToCheck.trans rest))))
    refine ⟨finalScratch, finalLength, ?_⟩
    convert complete using 1 <;> first | rfl | (congr 1 <;> omega) | ring

def entryFrame (count capacity : ℕ) (result scratch : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then unary count else if name = 1 then unary capacity
  else if name = 2 then buffer result else buffer scratch

/-- The capacity tape clears both counters without a prefilled output region. -/
theorem prepareCounters_runs (count capacity : ℕ) (result scratch : List Symbol)
    (resultLength : result.length = capacity) (scratchLength : scratch.length = capacity) :
    Runs (widths count capacity) readOnly prepareCounters (4 * capacity + 5)
      (.inl (.inl ())) (fun _ => 0) (entryFrame count capacity result scratch)
      (.inr (.inr ((), true))) (fun _ => 0)
      (frame 0 count capacity (List.replicate capacity false) (word (List.replicate capacity false))) := by
  let initial := entryFrame count capacity result scratch
  let zeros := List.replicate capacity false
  let middle := Function.update initial 2 (buffer (word zeros))
  have first := StandardTapeCommands.clear_runs (1 : Fin 4) 2 (by decide)
    (widths count capacity) readOnly rfl (List.replicate capacity true) result
    (by simp [widths]) (by simp [widths]) (by simpa using resultLength) initial rfl rfl
  have second := StandardTapeCommands.clear_runs (1 : Fin 4) 3 (by decide)
    (widths count capacity) readOnly rfl (List.replicate capacity true) scratch
    (by simp [widths]) (by simp [widths]) (by simpa using scratchLength) middle
    (by simp [middle, initial, entryFrame, unary, CallingConvention.tape, buffer]) (by simp [middle, initial, entryFrame, buffer])
  simp only [List.length_replicate] at first second
  have finalEqual : Function.update middle 3 (buffer (word zeros)) =
      frame 0 count capacity zeros (word zeros) := by
    funext name
    fin_cases name <;> simp [middle, initial, entryFrame, frame, unary, CallingConvention.tape, buffer, word, data, buffer_padding]
  rw [finalEqual] at second
  have complete := first.sequence (StandardTapeCommands.clear 1 3 (by decide)) (.inl ())
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) second
  convert complete using 1 <;> first | rfl | omega

/-- Complete unary-to-binary reading uses fixed-size counters, accepts arbitrary
writable contents, and restores every head. The result is modular in capacity. -/
theorem runs (count capacity : ℕ) (oldResult oldScratch : List Symbol)
    (resultLength : oldResult.length = capacity) (scratchLength : oldScratch.length = capacity) :
    ∃ finalScratch : List Bool, finalScratch.length = capacity ∧
      Runs (widths count capacity) readOnly machine (4 * capacity + count * (4 * capacity + 8) + 11)
        entry (fun _ => 0) (entryFrame count capacity oldResult oldScratch)
        exit (fun _ => 0)
        (entryFrame count capacity
          (word (advanceBits count (List.replicate capacity false))) (word finalScratch)) := by
  let zeros := List.replicate capacity false
  have prepared := prepareCounters_runs count capacity oldResult oldScratch resultLength scratchLength
  obtain ⟨finalScratch, finalLength, loopTrace⟩ := loop_runs 0 count capacity zeros zeros (by simp [zeros]) (by simp [zeros])
  have loopHalt : loop (.inl ())
      (MultiTape.read (frame count 0 capacity (advanceBits count zeros) (word finalScratch))) = none := by
    simp [loop, frame, MultiTape.read]
  simp only [zero_add, Nat.cast_zero] at loopTrace
  have loopExit := loopTrace.withExit_at loopHalt
  have zeroPosition : position (0 : ℤ) = fun _ => 0 := by funext name; simp [position]
  rw [zeroPosition] at loopExit
  have preparedLoop := prepared.sequence (MultiTape.withExit loop) (.inl (.inl ()))
    (by intro symbols; simp [prepareCounters, MultiTape.sequence, StandardTapeCommands.clear,
      MultiTape.wire, StandardBinaryScan.machine]) loopExit
  let ending := frame count 0 capacity (advanceBits count zeros) (word finalScratch)
  have returned := (StandardHead.BlankReturn.fromEnd_runs (List.replicate count true)).wire
    (oneTape (0 : Fin 4)) (widths count capacity) readOnly
    (by intro name; simp [widths]) (by intro name premise; rfl) ending (position count)
  simp only [List.length_replicate, install_one] at returned
  have sourceEq : (Binary.tape (word (List.replicate count true).reverse ++ [0]) [0]) () = ending 0 := by
    simp [ending, frame, word, data, Binary.tape]
  rw [sourceEq, Function.update_eq_self] at returned
  have initialPosition : Function.update (position count) 0 (count : ℤ) = position count := by
    funext name
    fin_cases name <;> simp [position]
  have finalPosition : Function.update (position count) 0 (0 : ℤ) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [position]
  have finalEqual : Function.update ending 0 (buffer (word (List.replicate count true))) =
      entryFrame count capacity (word (advanceBits count zeros)) (word finalScratch) := by
    funext name
    fin_cases name <;> simp [ending, entryFrame, frame, unary, CallingConvention.tape, buffer]
  rw [initialPosition, finalPosition, finalEqual] at returned
  have complete := preparedLoop.sequence restore (.inl 1)
    (by intro symbols; simp [MultiTape.sequence, MultiTape.withExit]) returned
  refine ⟨finalScratch, finalLength, ?_⟩
  convert complete using 1 <;> first | rfl | ring

end Polytime2.StandardSizeRead
