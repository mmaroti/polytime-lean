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

import Polytime2.StandardGcdStep
import Polytime2.StandardBinaryGuard
import Polytime2.StandardTapeCommands

/-! # Euclidean iteration in private fixed-width storage

The loop computes separate new operands before copying them into its private
working slots. Its guard and every subroutine restore their argument heads.
-/

namespace Polytime2.StandardGcdMachine

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 9)
/-- Five raw word regions (remainder, shift, difference, next, new left), and borrow. -/
abbrev Scratch := (Fin 5 → List Symbol) × Symbol

def Fits (digits : ℕ) (scratch : Scratch) : Prop := ∀ name, (scratch.1 name).length = digits

def frame (left right : List Bool) (scratch : Scratch) (flag : Symbol) : Tapes Alphabet :=
  fun name => match name.val with
    | 0 => buffer (scratch.1 0)
    | 1 => buffer (word right)
    | 2 => buffer (scratch.1 1)
    | 3 => buffer (scratch.1 2)
    | 4 => buffer [scratch.2]
    | 5 => buffer (scratch.1 3)
    | 6 => buffer (word left)
    | 7 => buffer (scratch.1 4)
    | _ => buffer [flag]

def widths (digits : ℕ) (name : Fin 9) : ℕ := if name = 4 ∨ name = 8 then 1 else digits

def work (digits : ℕ) (scratch : Scratch) : StandardGcdStep.Workspace :=
  (List.replicate digits false, scratch.1 1, scratch.1 2, scratch.1 3, scratch.2)

def finished (left right : List Bool) (scratch : Scratch) : StandardGcdStep.Workspace :=
  StandardBinaryRemainder.finish right left.reverse (work right.length scratch)

def nextRight (left right : List Bool) (scratch : Scratch) : List Bool := (finished left right scratch).1

def nextScratch (left right : List Bool) (scratch : Scratch) : Scratch :=
  let final := finished left right scratch
  ((fun name => match name.val with
    | 0 => word final.1 | 1 => final.2.1 | 2 => final.2.2.1
    | 3 => final.2.2.2.1 | _ => word right), final.2.2.2.2)

private theorem finished_fits (left right : List Bool) (scratch : Scratch)
    (fits : Fits right.length scratch) : StandardBinaryRemainder.Fits right.length (finished left right scratch) :=
  StandardBinaryRemainder.finish_fits left.reverse right (work right.length scratch)
    ⟨List.length_replicate, fits 1, fits 2, fits 3⟩

private theorem next_right_length (left right : List Bool) (scratch : Scratch)
    (fits : Fits right.length scratch) : (nextRight left right scratch).length = right.length :=
  (finished_fits left right scratch fits).1

private theorem next_scratch_fits (left right : List Bool) (scratch : Scratch)
    (fits : Fits right.length scratch) : Fits right.length (nextScratch left right scratch) := by
  have finalFits := finished_fits left right scratch fits
  intro name
  fin_cases name <;> simp only [nextScratch]
  · simpa only [word, List.length_map] using finalFits.1
  · exact finalFits.2.1
  · exact finalFits.2.2.1
  · exact finalFits.2.2.2
  · simp [word]

def stepWiring : Fin 8 ↪ Fin 9 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 9 => name.val) equal)⟩

@[simp] theorem stepWiring_apply (name : Fin 8) : stepWiring name = ⟨name.val, by omega⟩ := rfl

noncomputable def stepMachine : Machine Alphabet StandardGcdStep.State :=
  MultiTape.wire stepWiring StandardGcdStep.machine

noncomputable def firstCopy : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 7 6 (by decide)
noncomputable def secondCopy : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 0 1 (by decide)

abbrev BodyState := Sum StandardGcdStep.State (Sum (Fin 3) (Fin 3))

noncomputable def body : Machine Alphabet BodyState :=
  MultiTape.sequence stepMachine (MultiTape.sequence firstCopy secondCopy 0) (.inl 0)

def bodyEntry : BodyState := .inl StandardGcdStep.entry
def bodyExit : BodyState := .inr (.inr 2)

/-- The copies update private slots after the immutable-input Euclidean call
has returned. All regions stay fixed and every participating head is restored. -/
theorem body_runs (left right : List Bool) (sameLength : left.length = right.length)
    (scratch : Scratch) (fits : Fits right.length scratch) (flag : Symbol) :
    Runs (widths right.length) (fun _ => false) body (8 * right.length ^ 2 + 25 * right.length + 15)
      bodyEntry (fun _ => 0) (frame left right scratch flag)
      bodyExit (fun _ => 0) (frame right (nextRight left right scratch) (nextScratch left right scratch) flag) := by
  have first := (StandardGcdStep.runs left right sameLength
    (scratch.1 0) (scratch.1 1) (scratch.1 2) (scratch.1 3) (scratch.1 4)
    (fits 0) (fits 1) (fits 2) (fits 3) (fits 4) scratch.2).wire_of_eq
    stepWiring (widths right.length) (fun _ => false)
    (by intro name; fin_cases name <;> simp [widths, stepWiring_apply, StandardGcdStep.widths])
    (by intro name premise; cases premise)
    (frame left right scratch flag) (frame left right (nextScratch left right scratch) flag)
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by
      intro name outside
      by_cases located : name.val < 8
      · exact False.elim (outside ⟨⟨name.val, located⟩, Fin.ext rfl⟩)
      · have last : name = 8 := Fin.ext (by omega)
        subst name
        rfl)
  let next := nextRight left right scratch
  let changed := nextScratch left right scratch
  have nextLength : next.length = right.length := next_right_length left right scratch fits
  have copyLeft := StandardTapeCommands.copy_runs (7 : Fin 9) 6 (by decide)
    (widths right.length) (fun _ => false) rfl right (word left) rfl rfl
    (by simp [word, sameLength]) (frame left right changed flag) rfl rfl
  have newLeft : Function.update (frame left right changed flag) 6 (buffer (word right)) =
      frame right right changed flag := by
    funext name
    fin_cases name <;> simp [frame]
  rw [newLeft] at copyLeft
  have copyRight := StandardTapeCommands.copy_runs (0 : Fin 9) 1 (by decide)
    (widths right.length) (fun _ => false) rfl next (word right)
    (by simpa [widths] using nextLength.symm) (by simpa [widths] using nextLength.symm)
    (by simp [word, nextLength]) (frame right right changed flag) rfl rfl
  have newRight : Function.update (frame right right changed flag) 1 (buffer (word next)) =
      frame right next changed flag := by
    funext name
    fin_cases name <;> simp [frame]
  rw [newRight] at copyRight
  have copied := copyLeft.sequence secondCopy 0
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) copyRight
  have complete := first.sequence (MultiTape.sequence firstCopy secondCopy 0) (.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardGcdStep.machine, StandardGcdStep.exit,
      MultiTape.sequence, StandardGcdStep.copyMachine, StandardTerminatedCopy.machine]) copied
  simp only [nextLength] at complete
  convert complete using 1 <;> first | rfl | ring

noncomputable def guard : Machine Alphabet StandardBinaryGuard.State :=
  MultiTape.wire (twoTapes 1 8 (by decide)) StandardBinaryGuard.machine

/-- The guard writes just its Boolean result and preserves all private words. -/
theorem guard_runs (left right : List Bool) (scratch : Scratch) (flag : Symbol) :
    Runs (widths right.length) (fun _ => false) guard (2 * right.length + 2)
      (false, 0) (fun _ => 0) (frame left right scratch flag)
      (false, 2) (fun _ => 0) (frame left right scratch (data (right.any id))) := by
  apply (StandardBinaryGuard.runs right flag).wire_of_eq (twoTapes 1 8 (by decide))
    (widths right.length) (fun _ => false)
  · intro name
    cases name <;> simp [widths, StandardBinaryGuard.widths]
  · intro name premise
    cases premise
  · intro name
    cases name
    · exact (buffer_padding (word right)).symm
    · exact (buffer_padding [flag]).symm
  · intro name
    cases name
    · exact (buffer_padding (word right)).symm
    · exact (buffer_padding [data (right.any id)]).symm
  · intro name outside
    have different : name ≠ 8 := by
      intro equal
      subst name
      exact outside ⟨true, rfl⟩
    fin_cases name <;> first | rfl | exact False.elim (different rfl)

def result (symbols : Symbols Alphabet) : Bool := symbols 8 == 2

noncomputable def loop : Machine Alphabet (Sum StandardBinaryGuard.State BodyState) :=
  MultiTape.whileMachine guard body (false, 0) bodyEntry result

abbrev IterationState := Sum (Sum StandardBinaryGuard.State BodyState) Unit
noncomputable def iteration : Machine Alphabet IterationState := MultiTape.withExit loop

def iterationEntry : IterationState := .inl (.inl (false, 0))
def iterationExit : IterationState := .inr ()

private theorem raw_loop_runs (left right : List Bool) (sameLength : left.length = right.length)
    (scratch : Scratch) (fits : Fits right.length scratch) (flag : Symbol)
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    ∃ ticks finalLeft finalRight finalScratch,
      ticks ≤ (Gcd.measure (value left, value right) + 1) * (8 * right.length ^ 2 + 27 * right.length + 19) ∧
      finalLeft.length = right.length ∧ finalRight.length = right.length ∧ Fits right.length finalScratch ∧
      Runs (widths right.length) (fun _ => false) loop ticks (.inl (false, 0)) (fun _ => 0)
        (frame left right scratch flag) (.inl (false, 2)) (fun _ => 0)
        (frame finalLeft finalRight finalScratch (data false)) ∧
      value finalRight = 0 ∧ value finalLeft = Nat.gcd (value left) (value right) := by
  have guarded := (guard_runs left right scratch flag).rename Sum.inl (target := loop)
    (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
  cases tested : right.any id with
  | false =>
    rw [tested] at guarded
    have zero : value right = 0 := by
      have notPositive : ¬ 0 < value right := by
        intro positive
        have active := (Binary.any_iff_positive right).mpr positive
        simp [tested] at active
      omega
    refine ⟨2 * right.length + 2, left, right, scratch, ?_, sameLength, rfl, fits, guarded,
      zero, ?_⟩
    · have dominates : 2 * right.length + 2 ≤ 8 * right.length ^ 2 + 27 * right.length + 19 := by omega
      have scaled := Nat.mul_le_mul_right (8 * right.length ^ 2 + 27 * right.length + 19)
        (show 1 ≤ Gcd.measure (value left, value right) + 1 by omega)
      simp only [one_mul] at scaled
      exact dominates.trans scaled
    · simp [zero]
  | true =>
    rw [tested] at guarded
    have positive : 0 < value right := (Binary.any_iff_positive right).mp tested
    let next := nextRight left right scratch
    let changed := nextScratch left right scratch
    have nextLength : next.length = right.length := next_right_length left right scratch fits
    have changedFits : Fits right.length changed := next_scratch_fits left right scratch fits
    have stepValue : (value right, value next) = Gcd.advance (value left, value right) :=
      StandardGcdStep.result_value left right (scratch.1 1) (scratch.1 2) (scratch.1 3) scratch.2
        (fits 1) (fits 2) (fits 3) positive capacity
    have nextValue : value next = value left % value right := congrArg Prod.snd stepValue
    have nextCapacity : 2 * value next ≤ 2 ^ next.length := by
      have smaller := Nat.mod_lt (value left) positive
      rw [nextLength, nextValue]
      omega
    have progress : Gcd.measure (value right, value next) < Gcd.measure (value left, value right) := by
      rw [stepValue]
      exact Gcd.decreases (value left, value right) (by simp [Gcd.condition, Nat.ne_of_gt positive])
    obtain ⟨restTicks, finalLeft, finalRight, finalScratch, restCost,
      finalLeftLength, finalRightLength, finalFits, restTrace, finalZero, finalCorrect⟩ :=
      raw_loop_runs right next nextLength.symm changed
        (by simpa only [nextLength] using changedFits) (data true) nextCapacity
    simp only [nextLength] at restCost finalLeftLength finalRightLength finalFits restTrace
    have advanced := (body_runs left right sameLength scratch fits (data true)).rename Sum.inr (target := loop)
      (by intro state symbols next actions transition; simp [loop, MultiTape.whileMachine, transition])
    have toBody : Runs (widths right.length) (fun _ => false) loop 1
        (.inl (false, 2)) (fun _ => 0) (frame left right scratch (data true))
        (.inr bodyEntry) (fun _ => 0) (frame left right scratch (data true)) := by
      apply Runs.next (nextState := Sum.inr bodyEntry)
        (actions := stationary (MultiTape.read (frame left right scratch (data true))))
        (by simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
          result, MultiTape.read, frame, data, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂]) (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop) (Sum.inr bodyEntry) (fun _ => 0) (frame left right scratch (data true)))
    have toGuard : Runs (widths right.length) (fun _ => false) loop 1
        (.inr bodyExit) (fun _ => 0) (frame right next changed (data true))
        (.inl (false, 0)) (fun _ => 0) (frame right next changed (data true)) := by
      apply Runs.next (nextState := Sum.inl (false, 0))
        (actions := stationary (MultiTape.read (frame right next changed (data true))))
        (by simp [loop, MultiTape.whileMachine, body, bodyExit, MultiTape.sequence,
          secondCopy, StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine])
        (by intro name premise; rfl)
      simpa only [stationary, displacement, add_zero, act_stationary] using
        (Runs.zero (machine := loop) (Sum.inl (false, 0)) (fun _ => 0) (frame right next changed (data true)))
    have complete := guarded.trans (toBody.trans (advanced.trans (toGuard.trans restTrace)))
    refine ⟨2 * right.length + 2 + (1 + (8 * right.length ^ 2 + 25 * right.length + 15 + (1 + restTicks))),
      finalLeft, finalRight, finalScratch, ?_, finalLeftLength, finalRightLength, finalFits,
      complete, finalZero, ?_⟩
    · have dominated := Nat.mul_le_mul_right (8 * right.length ^ 2 + 27 * right.length + 19)
        (show Gcd.measure (value right, value next) + 1 ≤ Gcd.measure (value left, value right) by omega)
      calc
        _ ≤ (8 * right.length ^ 2 + 27 * right.length + 19) +
            Gcd.measure (value left, value right) * (8 * right.length ^ 2 + 27 * right.length + 19) := by omega
        _ = _ := by ring
    · have conserved : Gcd.answer (value right, value next) = Gcd.answer (value left, value right) := by
        rw [stepValue]
        exact Gcd.conserves (value left, value right)
      exact finalCorrect.trans conserved
termination_by Gcd.measure (value left, value right)
decreasing_by exact progress

/-- The complete Euclidean loop is cubic in binary capacity. Its working slots
are private; the enclosing public routine supplies immutable inputs and performs
final scratch clearing, including when the initial second operand is zero. -/
theorem iteration_runs (left right : List Bool) (sameLength : left.length = right.length)
    (scratch : Scratch) (fits : Fits right.length scratch) (flag : Symbol)
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    ∃ ticks finalLeft finalRight finalScratch,
      ticks ≤ (2 * right.length + 2) * (8 * right.length ^ 2 + 27 * right.length + 19) + 1 ∧
      finalLeft.length = right.length ∧ finalRight.length = right.length ∧ Fits right.length finalScratch ∧
      Runs (widths right.length) (fun _ => false) iteration ticks iterationEntry (fun _ => 0)
        (frame left right scratch flag) iterationExit (fun _ => 0)
        (frame finalLeft finalRight finalScratch (data false)) ∧
      value finalRight = 0 ∧ value finalLeft = Nat.gcd (value left) (value right) := by
  obtain ⟨ticks, finalLeft, finalRight, finalScratch, cost, leftLength, rightLength, finalFits,
    trace, stopped, correct⟩ := raw_loop_runs left right sameLength scratch fits flag capacity
  have measureBound : Gcd.measure (value left, value right) ≤ 2 * right.length + 1 :=
    Gcd.measure_bound right.length (value left, value right)
      ⟨by simpa only [sameLength] using Binary.value_lt_pow_length left, Binary.value_lt_pow_length right⟩
  have halted : loop (.inl (false, 2)) (MultiTape.read (frame finalLeft finalRight finalScratch (data false))) = none := by
    simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
      result, MultiTape.read, frame, data, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂]
  refine ⟨ticks + 1, finalLeft, finalRight, finalScratch, ?_, leftLength, rightLength,
    finalFits, trace.withExit_at halted, stopped, correct⟩
  exact Nat.add_le_add_right (cost.trans (Nat.mul_le_mul_right _ (by omega))) 1

def zeroScratch (digits : ℕ) : Scratch :=
  ((fun _ => word (List.replicate digits false)), data false)

def clearTarget (name : Fin 5) : Fin 9 := match name.val with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 5 | _ => 7

def clearWord (digits : ℕ) (scratch : Scratch) (name : Fin 5) : Scratch :=
  (Function.update scratch.1 name (word (List.replicate digits false)), scratch.2)

private theorem clear_word_fits (digits : ℕ) (scratch : Scratch) (fits : Fits digits scratch)
    (name : Fin 5) : Fits digits (clearWord digits scratch name) := by
  intro index
  by_cases same : index = name
  · subst index
    simp [clearWord, word]
  · simpa [clearWord, same] using fits index

noncomputable def clearCommand (name : Fin 5) : Machine Alphabet (StandardBinaryScan.State Unit) :=
  StandardTapeCommands.clear 6 (clearTarget name) (by fin_cases name <;> decide)

private theorem clear_word_runs (left right : List Bool) (digits : ℕ) (leftLength : left.length = digits)
    (scratch : Scratch) (fits : Fits digits scratch) (flag : Symbol) (name : Fin 5) :
    Runs (widths digits) (fun _ => false) (clearCommand name) (2 * digits + 2)
      (.inl ()) (fun _ => 0) (frame left right scratch flag)
      (.inr ((), true)) (fun _ => 0) (frame left right (clearWord digits scratch name) flag) := by
  have trace := StandardTapeCommands.clear_runs (6 : Fin 9) (clearTarget name)
    (by fin_cases name <;> decide) (widths digits) (fun _ => false) rfl left (scratch.1 name)
    (by simpa [widths] using leftLength.symm)
    (by fin_cases name <;> simpa [widths, clearTarget] using leftLength.symm)
    ((fits name).trans leftLength.symm) (frame left right scratch flag) rfl
    (by fin_cases name <;> rfl)
  have updated : Function.update (frame left right scratch flag) (clearTarget name)
      (buffer (word (List.replicate left.length false))) =
      frame left right (clearWord digits scratch name) flag := by
    funext index
    fin_cases name <;> fin_cases index <;> simp [frame, clearWord, clearTarget, leftLength] <;> rfl
  rw [updated, leftLength] at trace
  exact trace

abbrev ClearState := StandardBinaryScan.State Unit
abbrev CleanupState := Sum ClearState (Sum ClearState (Sum ClearState (Sum ClearState (Sum ClearState Bool))))

/-- Clear all five word scratch regions, then overwrite the borrow bit. -/
noncomputable def cleanup : Machine Alphabet CleanupState :=
  MultiTape.sequence (clearCommand 0)
    (MultiTape.sequence (clearCommand 1)
      (MultiTape.sequence (clearCommand 2)
        (MultiTape.sequence (clearCommand 3)
          (MultiTape.sequence (clearCommand 4) (StandardTapeCommands.setBoolean 4 false) false)
          (.inl (.inl ()))) (.inl (.inl ()))) (.inl (.inl ()))) (.inl (.inl ()))

def cleanupEntry : CleanupState := .inl (.inl ())
def cleanupExit : CleanupState := .inr (.inr (.inr (.inr (.inr true))))

/-- Cleanup derives every word extent from the canonical final first operand.
It works even if no Euclidean iteration initialized the private scratch. -/
theorem cleanup_runs (left right : List Bool) (digits : ℕ) (leftLength : left.length = digits)
    (scratch : Scratch) (fits : Fits digits scratch) (flag : Symbol) :
    Runs (widths digits) (fun _ => false) cleanup (10 * digits + 16)
      cleanupEntry (fun _ => 0) (frame left right scratch flag)
      cleanupExit (fun _ => 0) (frame left right (zeroScratch digits) flag) := by
  let first := clearWord digits scratch 0
  let second := clearWord digits first 1
  let third := clearWord digits second 2
  let fourth := clearWord digits third 3
  let fifth := clearWord digits fourth 4
  have firstFits := clear_word_fits digits scratch fits 0
  have secondFits := clear_word_fits digits first firstFits 1
  have thirdFits := clear_word_fits digits second secondFits 2
  have fourthFits := clear_word_fits digits third thirdFits 3
  have clearFirst := clear_word_runs left right digits leftLength scratch fits flag 0
  have clearSecond := clear_word_runs left right digits leftLength first firstFits flag 1
  have clearThird := clear_word_runs left right digits leftLength second secondFits flag 2
  have clearFourth := clear_word_runs left right digits leftLength third thirdFits flag 3
  have clearFifth := clear_word_runs left right digits leftLength fourth fourthFits flag 4
  have clearFlag := StandardTapeCommands.setBoolean_runs (4 : Fin 9) false
    (widths digits) (fun _ => false) rfl rfl (frame left right fifth flag) fifth.2 rfl
  have cleanWords : fifth.1 = fun _ => word (List.replicate digits false) := by
    funext name
    fin_cases name <;> simp [fifth, fourth, third, second, first, clearWord]
  have cleanFrame : Function.update (frame left right fifth flag) 4 (buffer [data false]) =
      frame left right (zeroScratch digits) flag := by
    funext name
    fin_cases name <;> simp [frame, zeroScratch, cleanWords]
  rw [cleanFrame] at clearFlag
  have last := clearFifth.sequence (StandardTapeCommands.setBoolean 4 false) false
    (by intro symbols; simp [clearCommand, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) clearFlag
  have afterFourth := clearFourth.sequence _ (Sum.inl (Sum.inl ()))
    (by intro symbols; simp [clearCommand, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) last
  have afterThird := clearThird.sequence _ (Sum.inl (Sum.inl ()))
    (by intro symbols; simp [clearCommand, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) afterFourth
  have afterSecond := clearSecond.sequence _ (Sum.inl (Sum.inl ()))
    (by intro symbols; simp [clearCommand, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) afterThird
  have complete := clearFirst.sequence _ (Sum.inl (Sum.inl ()))
    (by intro symbols; simp [clearCommand, StandardTapeCommands.clear, MultiTape.wire, StandardBinaryScan.machine]) afterSecond
  convert complete using 1 <;> first | rfl | ring

abbrev State := Sum IterationState CleanupState
noncomputable def machine : Machine Alphabet State := MultiTape.sequence iteration cleanup cleanupEntry

def entry : State := .inl iterationEntry
def exit : State := .inr cleanupExit

/-- The private GCD computation returns fully initialized canonical scratch,
including on zero operands and zero-bit words. Public inputs are supplied by
the enclosing routine on separate immutable tapes. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (scratch : Scratch) (fits : Fits right.length scratch) (flag : Symbol)
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    ∃ ticks finalLeft finalRight,
      ticks ≤ 16 * right.length ^ 3 + 70 * right.length ^ 2 + 102 * right.length + 56 ∧
      finalLeft.length = right.length ∧ finalRight.length = right.length ∧
      Runs (widths right.length) (fun _ => false) machine ticks entry (fun _ => 0)
        (frame left right scratch flag) exit (fun _ => 0)
        (frame finalLeft finalRight (zeroScratch right.length) (data false)) ∧
      value finalRight = 0 ∧ value finalLeft = Nat.gcd (value left) (value right) := by
  obtain ⟨ticks, finalLeft, finalRight, finalScratch, cost, leftLength, rightLength, finalFits,
    trace, stopped, correct⟩ := iteration_runs left right sameLength scratch fits flag capacity
  have cleaned := cleanup_runs finalLeft finalRight right.length leftLength finalScratch finalFits (data false)
  have complete := trace.sequence cleanup cleanupEntry
    (by intro symbols; simp [iteration, iterationExit, MultiTape.withExit]) cleaned
  refine ⟨ticks + (10 * right.length + 16) + 1, finalLeft, finalRight, ?_,
    leftLength, rightLength, complete, stopped, correct⟩
  nlinarith [cost]

end Polytime2.StandardGcdMachine
