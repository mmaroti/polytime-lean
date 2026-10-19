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

import Polytime2.Arithmetic.BinaryMultiplyStep
import Polytime2.Arithmetic.BitFold
import Polytime2.Primitives.TapeCommands

/-! # Fixed-width multiplication with immutable operand tapes

The high-bit-first loop maintains an accumulator, doubles it, and optionally
adds the factor. The multiplier supplies an immutable cursor. Neither words nor
counters grow; the result capacity is fixed before execution.
-/

namespace Polytime2.StandardBinaryMultiplication

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 6)
abbrev Workspace := List Bool × List Symbol × List Symbol × Symbol

def storage (factor : List Bool) (work : Workspace) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word work.1)
  else if name = 1 then buffer (word factor)
  else if name = 2 then buffer work.2.1
  else if name = 3 then buffer work.2.2.1
  else if name = 4 then buffer [work.2.2.2]
  else buffer []

def frame (source : Turing.Tape Symbol) (factor : List Bool) (work : Workspace) : Tapes Alphabet :=
  StandardBitFold.frame 5 (storage factor) source work

def position (offset : ℤ) : Fin 6 → ℤ := StandardBitFold.position 5 offset

def widths (sourceWidth digits : ℕ) (name : Fin 6) : ℕ :=
  if name = 5 then sourceWidth else if name = 4 then 1 else digits

def readOnly (name : Fin 6) : Bool := decide (name = 1 ∨ name = 5)

def stepWiring : Fin 5 ↪ Fin 6 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 6 => name.val) equal)⟩


@[simp] theorem stepWiring_apply (name : Fin 5) : stepWiring name = ⟨name.val, by omega⟩ := rfl


noncomputable def stepMachine (bit : Bool) : Machine Alphabet StandardBinaryMultiplyStep.State :=
  MultiTape.wire stepWiring (StandardBinaryMultiplyStep.machine bit)

abbrev ChoiceState := Sum StandardBinaryMultiplyStep.State StandardBinaryMultiplyStep.State

noncomputable def choice : Machine Alphabet ChoiceState
  | .inl state, symbols => (stepMachine true state symbols).map (fun command => (.inl command.1, command.2))
  | .inr state, symbols => (stepMachine false state symbols).map (fun command => (.inr command.1, command.2))

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 3 0 (by decide)

abbrev BodyState := Sum (Sum ChoiceState Unit) (Fin 3)

noncomputable def body : Machine Alphabet BodyState :=
  MultiTape.sequence (MultiTape.withExit choice) copyMachine 0

def bodyEntry (bit : Bool) : BodyState :=
  .inl (.inl (if bit then .inl StandardBinaryMultiplyStep.entry else .inr StandardBinaryMultiplyStep.entry))

def bodyExit : BodyState := .inr 2

private def Represents (sourceWidth : ℕ) (factor current : List Bool) (tapes : Tapes Alphabet) : Prop :=
  current.length = factor.length ∧ tapes 0 = buffer (word current) ∧
    tapes 1 = buffer (word factor) ∧
    ∀ name, name ≠ 5 → Region (widths sourceWidth factor.length name) 0 (tapes name)

private theorem represents_cursor (sourceWidth : ℕ) (factor current : List Bool)
    (tapes : Tapes Alphabet) (source : Turing.Tape Symbol)
    (represented : Represents sourceWidth factor current tapes) :
    Represents sourceWidth factor current (StandardBitFold.frame 5 id source tapes) := by
  rcases represented with ⟨length, currentEq, factorEq, regions⟩
  refine ⟨length, currentEq, factorEq, ?_⟩
  intro name different
  simpa [StandardBitFold.frame, different] using regions name different

/-- Only the accumulator is live; scratch requires its preserved region. -/
private theorem body_runs (bit : Bool) (factor current : List Bool) (sourceWidth : ℕ)
    (initial : Tapes Alphabet) (represented : Represents sourceWidth factor current initial) :
    ∃ final, Runs (widths sourceWidth factor.length) readOnly body (6 * factor.length + 10)
      (bodyEntry bit) (fun _ => 0) initial bodyExit (fun _ => 0) final ∧
      Represents sourceWidth factor (StandardBinaryMultiplyStep.added bit current factor).1 final := by
  rcases represented with ⟨length, currentEq, factorEq, regions⟩
  obtain ⟨shifted, shiftedLength, shiftedEq⟩ := (regions 2 (by decide)).exists_buffer
  obtain ⟨result, resultLength, resultEq⟩ := (regions 3 (by decide)).exists_buffer
  obtain ⟨flags, flagLength, flagEq⟩ := (regions 4 (by decide)).exists_buffer
  change flags.length = 1 at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  obtain ⟨after, lifted, located, outside, immutable⟩ :=
    (StandardBinaryMultiplyStep.runs bit current factor length.symm shifted result
      (shiftedLength.trans length.symm) (resultLength.trans length.symm) flag).wire_restoring
      stepWiring (widths sourceWidth factor.length) readOnly
      (by intro name; fin_cases name <;> simp [widths, StandardBinaryMultiplyStep.widths, length])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (by intro name; fin_cases name <;> assumption)
  have selected : Runs (widths sourceWidth factor.length) readOnly choice (4 * current.length + 6)
      (if bit then .inl StandardBinaryMultiplyStep.entry else .inr StandardBinaryMultiplyStep.entry)
      (fun _ => 0) initial
      (if bit then .inl StandardBinaryMultiplyStep.exit else .inr StandardBinaryMultiplyStep.exit)
      (fun _ => 0) after := by
    cases bit
    · exact lifted.rename Sum.inr (by intro state symbols next actions transition; simp [choice, stepMachine, transition])
    · exact lifted.rename Sum.inl (by intro state symbols next actions transition; simp [choice, stepMachine, transition])
  have common := selected.withExit (by intro symbols; cases bit <;>
    simp [choice, stepMachine, MultiTape.wire, StandardBinaryMultiplyStep.machine,
      StandardBinaryMultiplyStep.exit, MultiTape.withExit])
  let next := (StandardBinaryMultiplyStep.added bit current factor).1
  have nextLength : next.length = factor.length :=
    (StandardBinaryMultiplyStep.added_length bit current factor length.symm).trans length
  have copied := StandardTapeCommands.copy_runs (3 : Fin 6) 0 (by decide)
    (widths sourceWidth factor.length) readOnly rfl next (word current)
    nextLength.symm nextLength.symm (by simp [word, nextLength, length]) after (located 3) (located 0)
  have complete := common.sequence copyMachine 0 (by intro symbols; rfl) copied
  refine ⟨Function.update after 0 (buffer (word next)), ?_, nextLength, Function.update_self _ _ _, ?_, ?_⟩
  · convert complete using 1 <;> first | rfl | omega
  · exact (complete.readOnly_tape 1 rfl).trans factorEq
  · intro name different
    exact complete.region name (regions name different)

abbrev LoopState := StandardBitFold.State BodyState
noncomputable def loop : Machine Alphabet LoopState := StandardBitFold.machine 5 body bodyEntry
def loopEntry : LoopState := StandardBitFold.entry
def loopExit : LoopState := StandardBitFold.exit

/-- The logical recurrence contains only the accumulator. -/
def finish (factor bits current : List Bool) : List Bool :=
  StandardBitFold.fold (fun bit current => (StandardBinaryMultiplyStep.added bit current factor).1) bits current

theorem finish_length (factor bits current : List Bool) (length : current.length = factor.length) :
    (finish factor bits current).length = factor.length := by
  induction bits generalizing current with
  | nil => exact length
  | cons bit bits hypothesis =>
    exact hypothesis _ ((StandardBinaryMultiplyStep.added_length bit current factor length.symm).trans length)

/-- The accumulator computes the product prefix modulo its fixed capacity. -/
theorem finish_value (factor bits current : List Bool) (length : current.length = factor.length) :
    value (finish factor bits current) =
      (2 ^ bits.length * value current + value factor * value bits.reverse) % 2 ^ factor.length := by
  induction bits generalizing current with
  | nil =>
    have bounded : value current < 2 ^ factor.length := by
      simpa only [length] using Binary.value_lt_pow_length current
    simp [finish, StandardBitFold.fold, value, Nat.mod_eq_of_lt bounded]
  | cons bit bits hypothesis =>
    have nextLength := (StandardBinaryMultiplyStep.added_length bit current factor length.symm).trans length
    have rest := hypothesis _ nextLength
    have step := StandardBinaryMultiplyStep.added_mod bit current factor length.symm
    rw [length] at step
    have reverseValue : value (bit :: bits).reverse =
        value bits.reverse + 2 ^ bits.length * bit.toNat := by
      have previous := Binary.prefixValue_reverse bits.reverse bit.toNat
      have whole := Binary.prefixValue_reverse (bit :: bits).reverse 0
      simp only [List.reverse_reverse, List.length_reverse, Nat.mul_zero, Nat.add_zero] at previous whole
      rw [← whole]
      change Binary.prefixValue bits (bit.toNat + 2 * 0) = _
      simpa using previous
    change value (finish factor bits (StandardBinaryMultiplyStep.added bit current factor).1) = _
    rw [rest, step, reverseValue, List.length_cons, pow_succ]
    calc
      _ = (2 ^ bits.length * (2 * value current + (if bit then value factor else 0)) +
          value factor * value bits.reverse) % 2 ^ factor.length := by
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      _ = _ := by congr 1; cases bit <;> simp <;> ring

theorem result_value (input factor : List Bool)
    (capacity : value factor * value input < 2 ^ factor.length) :
    value (finish factor input.reverse (List.replicate factor.length false)) = value factor * value input := by
  simpa [Nat.mod_eq_of_lt capacity] using finish_value factor input.reverse
    (List.replicate factor.length false) List.length_replicate

private theorem loop_runs (input factor current : List Bool) (initial : Tapes Alphabet)
    (source : initial 5 = buffer (word input)) (represented : Represents input.length factor current initial) :
    ∃ final, Runs (widths input.length factor.length) readOnly loop
      (input.length * (6 * factor.length + 14) + 3) loopEntry (fun _ => 0) initial loopExit (fun _ => 0) final ∧
      Represents input.length factor (finish factor input.reverse current) final := by
  apply StandardBitFold.runsValues 5 body bodyEntry (widths input.length factor.length) readOnly
    (fun bit current => (StandardBinaryMultiplyStep.added bit current factor).1)
    (Represents input.length factor) (by intro value tapes source valid; exact represents_cursor _ _ _ _ _ valid)
    rfl bodyExit (6 * factor.length + 10)
    (by intro symbols; simp [body, bodyExit, MultiTape.sequence, copyMachine, StandardTapeCommands.copy,
      MultiTape.wire, StandardTerminatedCopy.machine]) ?_ input current initial source represented
  intro bit current tapes valid source offset
  obtain ⟨final, trace, correct⟩ := body_runs bit factor current input.length
    (StandardBitFold.frame 5 id source tapes) (represents_cursor _ _ _ _ _ valid)
  refine ⟨final, ?_, correct⟩
  have shifted := trace.regions (widths input.length factor.length) (position offset)
    (by intro name writable; fin_cases name <;> simp_all [position, StandardBitFold.position, readOnly])
  simpa only [zero_add, position] using shifted


noncomputable def initializeResult : Machine Alphabet (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear 1 0 (by decide)

noncomputable def cleanup : Machine Alphabet
    (Sum (StandardBinaryScan.State Unit) (Sum (StandardBinaryScan.State Unit) Bool)) :=
  MultiTape.sequence (StandardTapeCommands.clear 1 2 (by decide))
    (MultiTape.sequence (StandardTapeCommands.clear 1 3 (by decide))
      (StandardTapeCommands.setBoolean 4 false) false) (.inl (.inl ()))

abbrev CleanupState := Sum (StandardBinaryScan.State Unit) (Sum (StandardBinaryScan.State Unit) Bool)

def cleanupEntry : CleanupState := .inl (.inl ())
def cleanupExit : CleanupState := .inr (.inr true)

/-- Scratch is canonical even when the multiplier was empty and the loop did
not write any of it. The immutable factor supplies every word extent. -/
theorem cleanup_runs (source : Turing.Tape Symbol) (sourceWidth : ℕ)
    (factor : List Bool) (work : Workspace)
    (shiftedLength : work.2.1.length = factor.length) (resultLength : work.2.2.1.length = factor.length) :
    Runs (widths sourceWidth factor.length) readOnly cleanup (4 * factor.length + 7)
      cleanupEntry (fun _ => 0) (frame source factor work)
      cleanupExit (fun _ => 0) (frame source factor (work.1,
        word (List.replicate factor.length false), word (List.replicate factor.length false), data false)) := by
  let first : Workspace := (work.1, word (List.replicate factor.length false), work.2.2.1, work.2.2.2)
  let second : Workspace := (work.1, first.2.1, word (List.replicate factor.length false), work.2.2.2)
  have clearFirst := StandardTapeCommands.clear_runs (1 : Fin 6) 2 (by decide)
    (widths sourceWidth factor.length) readOnly rfl factor work.2.1 rfl rfl shiftedLength
    (frame source factor work) rfl rfl
  have firstEq : Function.update (frame source factor work) 2
      (buffer (word (List.replicate factor.length false))) = frame source factor first := by
    funext name
    fin_cases name <;> simp [frame, StandardBitFold.frame, storage, first]
  rw [firstEq] at clearFirst
  have clearSecond := StandardTapeCommands.clear_runs (1 : Fin 6) 3 (by decide)
    (widths sourceWidth factor.length) readOnly rfl factor work.2.2.1 rfl rfl resultLength
    (frame source factor first) rfl rfl
  have secondEq : Function.update (frame source factor first) 3
      (buffer (word (List.replicate factor.length false))) = frame source factor second := by
    funext name
    fin_cases name <;> simp [frame, StandardBitFold.frame, storage, first, second]
  rw [secondEq] at clearSecond
  have clearFlag := StandardTapeCommands.setBoolean_runs (4 : Fin 6) false
    (widths sourceWidth factor.length) readOnly rfl rfl (frame source factor second) work.2.2.2 rfl
  have flagEq : Function.update (frame source factor second) 4 (buffer [data false]) =
      frame source factor (work.1, word (List.replicate factor.length false),
        word (List.replicate factor.length false), data false) := by
    funext name
    fin_cases name <;> simp [frame, StandardBitFold.frame, storage, first, second]
  rw [flagEq] at clearFlag
  have tail := clearSecond.sequence (StandardTapeCommands.setBoolean 4 false) false
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) clearFlag
  have complete := clearFirst.sequence _ (Sum.inl (Sum.inl ()))
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) tail
  convert complete using 1 <;> first | rfl | omega

abbrev State := Sum (StandardBinaryScan.State Unit) (Sum LoopState CleanupState)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence initializeResult (MultiTape.sequence loop cleanup cleanupEntry) (.inl loopEntry)

def entry : State := .inl (.inl ())
def exit : State := .inr (.inr cleanupExit)

/-- The result region may initially contain any symbols, like the scratch. -/
def initialFrame (input factor : List Bool) (old shifted result : List Symbol) (flag : Symbol) :
    Tapes Alphabet := Function.update
      (frame (buffer (word input)) factor (List.replicate factor.length false, shifted, result, flag)) 0 (buffer old)

/-- Multiplication initializes its result and restores every head. Cleanup is
retained for the existing matrix-address caller's concrete scratch format. -/
theorem runs (input factor : List Bool) (old shifted result : List Symbol)
    (oldLength : old.length = factor.length) (shiftedLength : shifted.length = factor.length)
    (resultLength : result.length = factor.length) (flag : Symbol) :
    let product := finish factor input.reverse (List.replicate factor.length false)
    Runs (widths input.length factor.length) readOnly machine
      (input.length * (6 * factor.length + 14) + 6 * factor.length + 14)
      entry (fun _ => 0) (initialFrame input factor old shifted result flag)
      exit (fun _ => 0) (frame (buffer (word input)) factor
        (product, word (List.replicate factor.length false), word (List.replicate factor.length false), data false)) := by
  let work : Workspace := (List.replicate factor.length false, shifted, result, flag)
  have cleared := StandardTapeCommands.clear_runs (1 : Fin 6) 0 (by decide)
    (widths input.length factor.length) readOnly rfl factor old rfl rfl oldLength
    (initialFrame input factor old shifted result flag) rfl (Function.update_self _ _ _)
  have initialized : Function.update (initialFrame input factor old shifted result flag) 0
      (buffer (word (List.replicate factor.length false))) = frame (buffer (word input)) factor work := by
    funext name
    fin_cases name <;> simp [initialFrame, frame, StandardBitFold.frame, storage, work]
  rw [initialized] at cleared
  have represented : Represents input.length factor (List.replicate factor.length false)
      (frame (buffer (word input)) factor work) := by
    refine ⟨List.length_replicate, rfl, rfl, ?_⟩
    intro name different
    fin_cases name
    · simpa [widths, frame, storage, StandardBitFold.frame, work, word] using
        buffer_region (word (List.replicate factor.length false))
    · simpa [widths, frame, storage, StandardBitFold.frame, word] using buffer_region (word factor)
    · simpa [widths, frame, storage, StandardBitFold.frame, work, shiftedLength] using buffer_region shifted
    · simpa [widths, frame, storage, StandardBitFold.frame, work, resultLength] using buffer_region result
    · simpa [widths, frame, storage, StandardBitFold.frame, work] using buffer_region [flag]
    · exact False.elim (different rfl)
  obtain ⟨after, iterated, productLength, productEq, factorEq, regions⟩ :=
    loop_runs input factor (List.replicate factor.length false) _ rfl represented
  obtain ⟨lastShifted, lastShiftedLength, lastShiftedEq⟩ := (regions 2 (by decide)).exists_buffer
  obtain ⟨lastResult, lastResultLength, lastResultEq⟩ := (regions 3 (by decide)).exists_buffer
  obtain ⟨lastFlags, lastFlagLength, lastFlagEq⟩ := (regions 4 (by decide)).exists_buffer
  change lastFlags.length = 1 at lastFlagLength
  obtain ⟨lastFlag, rfl⟩ := List.length_eq_one_iff.mp lastFlagLength
  have sourceEq := iterated.readOnly_tape 5 rfl
  have afterFrame : after = frame (buffer (word input)) factor
      (finish factor input.reverse (List.replicate factor.length false), lastShifted, lastResult, lastFlag) := by
    funext name
    fin_cases name
    · exact productEq
    · exact factorEq
    · exact lastShiftedEq
    · exact lastResultEq
    · exact lastFlagEq
    · exact sourceEq
  have cleaned := cleanup_runs (buffer (word input)) input.length factor
    (finish factor input.reverse (List.replicate factor.length false), lastShifted, lastResult, lastFlag)
    (by simpa [widths] using lastShiftedLength) (by simpa [widths] using lastResultLength)
  rw [← afterFrame] at cleaned
  have tail := iterated.sequence cleanup cleanupEntry
    (by intro symbols; simp [loop, loopExit, StandardBitFold.machine, StandardBitFold.exit]) cleaned
  have complete := cleared.sequence _ (Sum.inl loopEntry)
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) tail
  convert complete using 1 <;> first | rfl | ring


/-- The factor/result capacity and multiplier width are independent sizes. -/
noncomputable def domains : Sum Bool (Fin 6) → EncodedDomain Bool
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals (decide (name = 5))

def argumentReadOnly : Sum Bool (Fin 6) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 6 ↪ Sum Bool (Fin 6) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Bool ↪ Sum Bool (Fin 6) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def outputTapes : Unit ↪ Sum Bool (Fin 6) := oneTape (.inr 0)

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Bool (Fin 6))) State :=
  MultiTape.wire dataTapes machine

/-- The two immutable operands produce their exact product on a separate tape,
provided its fixed capacity suffices. Private scratch has no return contract. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment input =>
      (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val *
        (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val < 2 ^ assignment false)
    (fun assignment input output =>
      (output () : Fin (2 ^ assignment false)).val =
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val *
          (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire,
    machine, exit, MultiTape.sequence, cleanup, cleanupExit, StandardTapeCommands.setBoolean,
    StandardTapeCommands.booleanMachine]),
    MvPolynomial.X true * (6 * MvPolynomial.X false + 14) + 6 * MvPolynomial.X false + 14, ?_⟩
  intro assignment input initial valid represented sizes
  let factor := List.ofFn (fun index : Fin (assignment false) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  let multiplier := List.ofFn (fun index : Fin (assignment true) =>
    (BitVec.ofFin (input ⟨.inr 5, rfl⟩)).getLsbD index.val)
  have factorLength : factor.length = assignment false := List.length_ofFn
  have multiplierLength : multiplier.length = assignment true := List.length_ofFn
  have factorValue : value factor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment false)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  have multiplierValue : value multiplier = (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 5, rfl⟩))
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 4) rfl
  norm_num [domains, StandardBinaryScan.domains, EncodedDomain.booleans,
    EncodedDomain.fixed, EncodedDomain.ofCodec] at flagLength
  obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  have factorEq : initial (.inr 1) = buffer (word factor) :=
    (represented.1 (.inr 1) rfl).trans (encoded_binaryNaturals_value false assignment _)
  have multiplierEq : initial (.inr 5) = buffer (word multiplier) :=
    (represented.1 (.inr 5) rfl).trans (encoded_binaryNaturals_value true assignment _)
  simp [domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at oldLength shiftedLength resultLength
  have oldFits : old.length = factor.length := oldLength.trans factorLength.symm
  have shiftedFits : oldShifted.length = factor.length := shiftedLength.trans factorLength.symm
  have resultFits : oldResult.length = factor.length := resultLength.trans factorLength.symm
  let product := finish factor multiplier.reverse (List.replicate factor.length false)
  have productLength : product.length = assignment false :=
    (finish_length factor multiplier.reverse (List.replicate factor.length false) List.length_replicate).trans factorLength
  have correct : value product = value factor * value multiplier :=
    result_value multiplier factor
      (by rw [factorValue, multiplierValue, factorLength]; exact valid)
  have trace := (runs multiplier factor old oldShifted oldResult oldFits shiftedFits resultFits oldFlag).wire
    dataTapes (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains (.inr name)).width assignment = _
      fin_cases name <;> norm_num [domains, widths, factorLength, multiplierLength,
        EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.binaryNaturals])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes (initialFrame multiplier factor old oldShifted oldResult oldFlag) initial = initial := by
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
      · exact factorEq.symm
      · exact shiftedEq.symm
      · exact resultEq.symm
      · exact flagEq.symm
      · exact multiplierEq.symm
  have positions : install dataTapes (fun _ : Fin 6 => (0 : ℤ))
      (fun _ : Sum Bool (Fin 6) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let productValue : Fin (2 ^ assignment false) := ⟨value product,
    by simpa only [productLength] using Binary.value_lt_pow_length product⟩
  let output : Outputs domains outputTapes assignment := fun _ => productValue
  refine ⟨multiplier.length * (6 * factor.length + 14) + 6 * factor.length + 14, output,
    install dataTapes (frame (buffer (word multiplier)) factor
      (product, word (List.replicate factor.length false), word (List.replicate factor.length false), data false)) initial,
    ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X, factorLength, multiplierLength]
    exact le_rfl
  · change value product = _
    simpa only [factorValue, multiplierValue] using correct
  · intro name
    cases name
    change install dataTapes _ initial (dataTapes 0) = _
    rw [install_at]
    exact (encoded_binaryNaturals false assignment product productLength).symm

end Polytime2.StandardBinaryMultiplication
