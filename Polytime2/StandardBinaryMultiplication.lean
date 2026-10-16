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

import Polytime2.StandardBinaryMultiplyStep
import Polytime2.StandardBitFold
import Polytime2.StandardTapeCommands

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

def Fits (digits : ℕ) (work : Workspace) : Prop :=
  work.1.length = digits ∧ work.2.1.length = digits ∧ work.2.2.1.length = digits

def advance (bit : Bool) (factor : List Bool) (work : Workspace) : Workspace :=
  let result := StandardBinaryMultiplyStep.added bit work.1 factor
  (result.1, word (StandardBinaryMultiplyStep.shifted work.1), word result.1, data result.2)

theorem advance_fits (bit : Bool) (factor : List Bool) (work : Workspace)
    (fits : Fits factor.length work) : Fits factor.length (advance bit factor work) := by
  have length := StandardBinaryMultiplyStep.added_length bit work.1 factor fits.1.symm
  refine ⟨length.trans fits.1, ?_, ?_⟩
  · simp [advance, word, fits.1]
  · simpa [advance, word] using length.trans fits.1

def stepWiring : Fin 5 ↪ Fin 6 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 6 => name.val) equal)⟩

def copyWiring : Bool ↪ Fin 6 :=
  ⟨(fun name => if name then 0 else 3), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem stepWiring_apply (name : Fin 5) : stepWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem copyWiring_apply (name : Bool) : copyWiring name = (if name then 0 else 3) := rfl

noncomputable def stepMachine (bit : Bool) : Machine Alphabet StandardBinaryMultiplyStep.State :=
  MultiTape.wire stepWiring (StandardBinaryMultiplyStep.machine bit)

abbrev ChoiceState := Sum StandardBinaryMultiplyStep.State StandardBinaryMultiplyStep.State

noncomputable def choice : Machine Alphabet ChoiceState
  | .inl state, symbols => (stepMachine true state symbols).map (fun command => (.inl command.1, command.2))
  | .inr state, symbols => (stepMachine false state symbols).map (fun command => (.inr command.1, command.2))

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  MultiTape.wire copyWiring StandardTerminatedCopy.machine

abbrev BodyState := Sum (Sum ChoiceState Unit) (Fin 3)

noncomputable def body : Machine Alphabet BodyState :=
  MultiTape.sequence (MultiTape.withExit choice) copyMachine 0

def bodyEntry (bit : Bool) : BodyState :=
  .inl (.inl (if bit then .inl StandardBinaryMultiplyStep.entry else .inr StandardBinaryMultiplyStep.entry))

def bodyExit : BodyState := .inr 2

private theorem step_positions (offset : ℤ) :
    install stepWiring (fun _ : Fin 5 => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  all_goals first
    | (change install stepWiring _ _ (stepWiring 0) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 1) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 2) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 3) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 4) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 6 => name.val) equal;
        have bounded := localName.isLt; simp only [stepWiring_apply] at values; omega)

private theorem step_install (source : Turing.Tape Symbol) (factor current : List Bool)
    (shifted result : List Symbol) (flag : Symbol) (old : Workspace) :
    install stepWiring (StandardBinaryMultiplyStep.frame current factor shifted result flag)
      (frame source factor old) = frame source factor (current, shifted, result, flag) := by
  funext name
  fin_cases name
  all_goals first
    | (change install stepWiring _ _ (stepWiring 0) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 1) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 2) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 3) = _; rw [install_at]; rfl)
    | (change install stepWiring _ _ (stepWiring 4) = _; rw [install_at]; rfl)
    | (rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩
        have values := congrArg (fun name : Fin 6 => name.val) equal
        have bounded := localName.isLt
        simp only [stepWiring_apply] at values
        omega)]; rfl)

private theorem copy_positions (offset : ℤ) :
    install copyWiring (fun _ : Bool => (0 : ℤ)) (position offset) = position offset := by
  funext name
  fin_cases name
  · change install copyWiring _ _ (copyWiring true) = _
    rw [install_at]; rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal
  · change install copyWiring _ _ (copyWiring false) = _
    rw [install_at]; rfl
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal

private theorem copy_install (source : Turing.Tape Symbol) (factor current result : List Bool)
    (shifted : List Symbol) (flag : Symbol) (newCurrent : List Bool) :
    install copyWiring (Copy.frame [0] (word result ++ [0]) [0] (word newCurrent ++ [0]))
      (frame source factor (current, shifted, word result, flag)) =
      frame source factor (newCurrent, shifted, word result, flag) := by
  funext name
  fin_cases name
  · change install copyWiring _ _ (copyWiring true) = _
    rw [install_at]
    exact buffer_padding _
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal
  · change install copyWiring _ _ (copyWiring false) = _
    rw [install_at]
    exact buffer_padding _
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [copyWiring_apply] at equal

/-- One restoring body call changes only private accumulator and scratch tapes.
The multiplier cursor remains wherever the enclosing traversal placed it. -/
theorem body_runs (bit : Bool) (factor : List Bool) (work : Workspace)
    (fits : Fits factor.length work) (source : Turing.Tape Symbol) (sourceWidth : ℕ) (offset : ℤ) :
    Runs (widths sourceWidth factor.length) readOnly body (6 * factor.length + 10)
      (bodyEntry bit) (position offset) (frame source factor work)
      bodyExit (position offset) (frame source factor (advance bit factor work)) := by
  have stepTrace := (StandardBinaryMultiplyStep.runs bit work.1 factor fits.1.symm
    work.2.1 work.2.2.1 (fits.2.1.trans fits.1.symm) (fits.2.2.trans fits.1.symm) work.2.2.2).wire
    stepWiring (widths sourceWidth factor.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardBinaryMultiplyStep.widths, fits.1])
    (by intro name premise; fin_cases name <;>
      simp_all [readOnly, StandardBinaryMultiplyStep.readOnly])
    (frame source factor work) (position offset)
  rw [step_positions, step_install, step_install] at stepTrace
  have originalWork : (work.1, work.2.1, work.2.2.1, work.2.2.2) = work := rfl
  rw [originalWork] at stepTrace
  have selected : Runs (widths sourceWidth factor.length) readOnly choice (4 * work.1.length + 6)
      (if bit then .inl StandardBinaryMultiplyStep.entry else .inr StandardBinaryMultiplyStep.entry)
      (position offset) (frame source factor work)
      (if bit then .inl StandardBinaryMultiplyStep.exit else .inr StandardBinaryMultiplyStep.exit)
      (position offset) (frame source factor (work.1,
        word (StandardBinaryMultiplyStep.shifted work.1),
        word (StandardBinaryMultiplyStep.added bit work.1 factor).1,
        data (StandardBinaryMultiplyStep.added bit work.1 factor).2)) := by
    cases bit
    · exact stepTrace.rename Sum.inr (by intro state symbols next actions transition; simp [choice, stepMachine, transition])
    · exact stepTrace.rename Sum.inl (by intro state symbols next actions transition; simp [choice, stepMachine, transition])
  have common := selected.withExit (by
    intro symbols
    cases bit <;> simp [choice, stepMachine, MultiTape.wire, StandardBinaryMultiplyStep.machine,
      StandardBinaryMultiplyStep.exit, MultiTape.withExit])
  let next := (StandardBinaryMultiplyStep.added bit work.1 factor).1
  have nextLength : next.length = factor.length :=
    (StandardBinaryMultiplyStep.added_length bit work.1 factor fits.1.symm).trans fits.1
  have copied := (StandardTerminatedCopy.runs next (word work.1)
    (by simp [word, nextLength, fits.1])).wire
    copyWiring (widths sourceWidth factor.length) readOnly
    (by intro name; cases name <;> simp [widths, nextLength])
    (by intro name premise; cases name <;> simp [readOnly] at premise)
    (frame source factor (work.1, word (StandardBinaryMultiplyStep.shifted work.1), word next,
      data (StandardBinaryMultiplyStep.added bit work.1 factor).2)) (position offset)
  rw [copy_positions, copy_install, copy_install] at copied
  have complete := common.sequence copyMachine 0 (by intro symbols; rfl) copied
  simp only [fits.1, nextLength] at complete
  convert complete using 1 <;> first | rfl | omega

abbrev LoopState := StandardBitFold.State BodyState

noncomputable def loop : Machine Alphabet LoopState := StandardBitFold.machine 5 body bodyEntry

def loopEntry : LoopState := StandardBitFold.entry
def loopExit : LoopState := StandardBitFold.exit

def finish (factor : List Bool) (bits : List Bool) (work : Workspace) : Workspace :=
  StandardBitFold.fold (fun bit work => advance bit factor work) bits work

theorem finish_fits (factor bits : List Bool) (work : Workspace)
    (fits : Fits factor.length work) : Fits factor.length (finish factor bits work) := by
  induction bits generalizing work with
  | nil => exact fits
  | cons bit bits hypothesis => exact hypothesis _ (advance_fits bit factor work fits)

/-- The accumulator computes the product prefix modulo its fixed capacity. -/
theorem finish_value (factor bits : List Bool) (work : Workspace)
    (fits : Fits factor.length work) :
    value (finish factor bits work).1 =
      (2 ^ bits.length * value work.1 + value factor * value bits.reverse) % 2 ^ factor.length := by
  induction bits generalizing work with
  | nil =>
    have bounded : value work.1 < 2 ^ factor.length := by
      simpa only [fits.1] using Binary.value_lt_pow_length work.1
    simp [finish, StandardBitFold.fold, value, Nat.mod_eq_of_lt bounded]
  | cons bit bits hypothesis =>
    have nextFits := advance_fits bit factor work fits
    have rest := hypothesis (advance bit factor work) nextFits
    have step := StandardBinaryMultiplyStep.added_mod bit work.1 factor fits.1.symm
    rw [fits.1] at step
    have reverseValue : value (bit :: bits).reverse =
        value bits.reverse + 2 ^ bits.length * bit.toNat := by
      have previous := Binary.prefixValue_reverse bits.reverse bit.toNat
      have whole := Binary.prefixValue_reverse (bit :: bits).reverse 0
      simp only [List.reverse_reverse, List.length_reverse, Nat.mul_zero, Nat.add_zero] at previous whole
      rw [← whole]
      change Binary.prefixValue bits (bit.toNat + 2 * 0) = _
      simpa using previous
    change value (finish factor bits (advance bit factor work)).1 = _
    rw [rest]
    change (2 ^ bits.length * value (StandardBinaryMultiplyStep.added bit work.1 factor).1 +
      value factor * value bits.reverse) % 2 ^ factor.length = _
    rw [step, reverseValue, List.length_cons, pow_succ]
    calc
      _ = (2 ^ bits.length * (2 * value work.1 + (if bit then value factor else 0)) +
          value factor * value bits.reverse) % 2 ^ factor.length := by
        simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
      _ = _ := by congr 1; cases bit <;> simp <;> ring

/-- With zero initial accumulator and sufficient capacity, the loop is exact. -/
theorem result_value (input factor : List Bool) (shifted result : List Symbol) (flag : Symbol)
    (shiftedLength : shifted.length = factor.length) (resultLength : result.length = factor.length)
    (capacity : value factor * value input < 2 ^ factor.length) :
    value (finish factor input.reverse (List.replicate factor.length false, shifted, result, flag)).1 =
      value factor * value input := by
  simpa [Nat.mod_eq_of_lt capacity] using finish_value factor input.reverse
    (List.replicate factor.length false, shifted, result, flag)
    ⟨List.length_replicate, shiftedLength, resultLength⟩

/-- The runtime-width multiplication loop uses one fixed finite controller.
Every source head and every body head is restored at its boundary. -/
theorem loop_runs (input factor : List Bool) (work : Workspace) (fits : Fits factor.length work) :
    Runs (widths input.length factor.length) readOnly loop
      (input.length * (6 * factor.length + 14) + 3) loopEntry (fun _ => 0)
      (frame (buffer (word input)) factor work) loopExit (fun _ => 0)
      (frame (buffer (word input)) factor (finish factor input.reverse work)) := by
  exact StandardBitFold.runs 5 body bodyEntry (storage factor) (widths input.length factor.length)
    readOnly (fun bit work => advance bit factor work) (Fits factor.length) bodyExit
    (6 * factor.length + 10)
    (by intro symbols; simp [body, bodyExit, MultiTape.sequence, copyMachine,
      MultiTape.wire, StandardTerminatedCopy.machine])
    (fun bit work valid => advance_fits bit factor work valid)
    (fun bit work valid source offset => body_runs bit factor work valid source input.length offset)
    input work fits


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
    (factor : List Bool) (work : Workspace) (fits : Fits factor.length work) :
    Runs (widths sourceWidth factor.length) readOnly cleanup (4 * factor.length + 7)
      cleanupEntry (fun _ => 0) (frame source factor work)
      cleanupExit (fun _ => 0) (frame source factor (work.1,
        word (List.replicate factor.length false), word (List.replicate factor.length false), data false)) := by
  let first : Workspace := (work.1, word (List.replicate factor.length false), work.2.2.1, work.2.2.2)
  let second : Workspace := (work.1, first.2.1, word (List.replicate factor.length false), work.2.2.2)
  have clearFirst := StandardTapeCommands.clear_runs (1 : Fin 6) 2 (by decide)
    (widths sourceWidth factor.length) readOnly rfl factor work.2.1 rfl rfl fits.2.1
    (frame source factor work) rfl rfl
  have firstEq : Function.update (frame source factor work) 2
      (buffer (word (List.replicate factor.length false))) = frame source factor first := by
    funext name
    fin_cases name <;> simp [frame, StandardBitFold.frame, storage, first]
  rw [firstEq] at clearFirst
  have clearSecond := StandardTapeCommands.clear_runs (1 : Fin 6) 3 (by decide)
    (widths sourceWidth factor.length) readOnly rfl factor work.2.2.1 rfl rfl fits.2.2
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

/-- Complete multiplication initializes its own result, restores every head,
from arbitrary writable contents. The concrete trace also records scratch. -/
theorem runs (input factor : List Bool) (old shifted result : List Symbol)
    (oldLength : old.length = factor.length) (shiftedLength : shifted.length = factor.length)
    (resultLength : result.length = factor.length) (flag : Symbol) :
    let work : Workspace := (List.replicate factor.length false, shifted, result, flag)
    let product := (finish factor input.reverse work).1
    Runs (widths input.length factor.length) readOnly machine
      (input.length * (6 * factor.length + 14) + 6 * factor.length + 14)
      entry (fun _ => 0) (initialFrame input factor old shifted result flag)
      exit (fun _ => 0) (frame (buffer (word input)) factor
        (product, word (List.replicate factor.length false), word (List.replicate factor.length false), data false)) := by
  dsimp only
  let work : Workspace := (List.replicate factor.length false, shifted, result, flag)
  have fits : Fits factor.length work := ⟨List.length_replicate, shiftedLength, resultLength⟩
  have cleared := StandardTapeCommands.clear_runs (1 : Fin 6) 0 (by decide)
    (widths input.length factor.length) readOnly rfl factor old rfl rfl oldLength
    (initialFrame input factor old shifted result flag) rfl (Function.update_self _ _ _)
  have initialized : Function.update (initialFrame input factor old shifted result flag) 0
      (buffer (word (List.replicate factor.length false))) = frame (buffer (word input)) factor work := by
    funext name
    fin_cases name <;> simp [initialFrame, frame, StandardBitFold.frame, storage, work]
  rw [initialized] at cleared
  have iterated := loop_runs input factor work fits
  have cleaned := cleanup_runs (buffer (word input)) input.length factor (finish factor input.reverse work)
    (finish_fits factor input.reverse work fits)
  have tail := iterated.sequence cleanup cleanupEntry
    (by intro symbols; simp [loop, loopExit, StandardBitFold.machine, StandardBitFold.exit]) cleaned
  have complete := cleared.sequence _ (Sum.inl loopEntry)
    (by intro symbols; simp [StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) tail
  convert complete using 1 <;> first | rfl | ring


/-- The factor/result capacity and multiplier width are independent sizes. -/
def domains : Sum Bool (Fin 6) → EncodedDomain Bool
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
  change flags.length = 1 at flagLength
  obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  have factorEq : initial (.inr 1) = buffer (word factor) := represented.1 (.inr 1) rfl
  have multiplierEq : initial (.inr 5) = buffer (word multiplier) := represented.1 (.inr 5) rfl
  have oldFits : old.length = factor.length := oldLength.trans factorLength.symm
  have shiftedFits : oldShifted.length = factor.length := shiftedLength.trans factorLength.symm
  have resultFits : oldResult.length = factor.length := resultLength.trans factorLength.symm
  let work : Workspace := (List.replicate factor.length false, oldShifted, oldResult, oldFlag)
  let product := (finish factor multiplier.reverse work).1
  have productLength : product.length = assignment false :=
    (finish_fits factor multiplier.reverse work ⟨List.length_replicate, shiftedFits, resultFits⟩).1.trans factorLength
  have correct : value product = value factor * value multiplier :=
    result_value multiplier factor oldShifted oldResult oldFlag shiftedFits resultFits
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
