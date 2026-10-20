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

import Polytime2.Machine.CallingConventionWhile
import Polytime2.Arithmetic.GcdStep
import Polytime2.Arithmetic.BinaryGuard
import Polytime2.Primitives.TapeCommands

/-! # Euclidean iteration in private fixed-width storage

The loop computes separate new operands before copying them into its private
working slots. Its guard and every subroutine restore their argument heads.
-/

namespace Polytime2.StandardGcdMachine

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 9)
def widths (digits : ℕ) (name : Fin 9) : ℕ := if name = 4 ∨ name = 8 then 1 else digits

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

/-- Live operands and bounded private regions are the complete loop interface. -/
private def Represents (digits : ℕ) (operands : List Bool × List Bool) (tapes : Tapes Alphabet) : Prop :=
  operands.1.length = digits ∧ operands.2.length = digits ∧
    tapes 6 = buffer (word operands.1) ∧ tapes 1 = buffer (word operands.2) ∧
    ∀ name, Region (widths digits name) 0 (tapes name)

private def next (operands : List Bool × List Bool) : List Bool × List Bool :=
  (operands.2, (StandardBinaryDivision.finish operands.2 operands.1.reverse
    (List.replicate operands.2.length false, List.replicate operands.2.length false)).2)

private theorem body_runs (digits : ℕ) (operands : List Bool × List Bool) (initial : Tapes Alphabet)
    (represented : Represents digits operands initial) :
    ∃ final, Runs (widths digits) (fun _ => false) body (12 * digits ^ 2 + 35 * digits + 18)
      bodyEntry (fun _ => 0) initial bodyExit (fun _ => 0) final ∧ Represents digits (next operands) final := by
  rcases represented with ⟨leftLength, rightLength, leftEq, rightEq, regions⟩
  have nextLength : (next operands).2.length = digits :=
    (StandardBinaryDivision.finish_lengths _ _ _ List.length_replicate List.length_replicate).2.trans rightLength
  obtain ⟨localFinal, localTrace, remainderEq, divisorEq⟩ := StandardGcdStep.runs operands.1 operands.2
    (leftLength.trans rightLength.symm) (fun name => initial (stepWiring name)) leftEq rightEq
    (by
      intro name
      have region := regions (stepWiring name)
      fin_cases name <;> simpa [widths, StandardGcdStep.widths, rightLength] using region)
  obtain ⟨after, first, located, outside, immutable⟩ := localTrace.wire_restoring stepWiring
    (widths digits) (fun _ => false)
    (by intro name; fin_cases name <;> simp [widths, StandardGcdStep.widths, rightLength])
    (by intro name premise; cases premise) initial (fun _ => rfl)
  have copyLeft := StandardTapeCommands.copy_runs (7 : Fin 9) 6 (by decide)
    (widths digits) (fun _ => false) rfl operands.2 (word operands.1)
    rightLength.symm rightLength.symm (by simp [word, leftLength, rightLength]) after
    ((located 7).trans divisorEq) ((located 6).trans (localTrace.readOnly_tape 6 rfl |>.trans leftEq))
  let changed := Function.update after 6 (buffer (word operands.2))
  have copyRight := StandardTapeCommands.copy_runs (0 : Fin 9) 1 (by decide)
    (widths digits) (fun _ => false) rfl (next operands).2 (word operands.2)
    nextLength.symm nextLength.symm (by simp [word, nextLength, rightLength]) changed
    (by exact (located 0).trans remainderEq)
    (by exact (located 1).trans ((localTrace.readOnly_tape 1 rfl).trans rightEq))
  have copied := copyLeft.sequence secondCopy 0
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) copyRight
  have complete := first.sequence (MultiTape.sequence firstCopy secondCopy 0) (.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardGcdStep.machine, StandardGcdStep.exit,
      MultiTape.sequence, StandardGcdStep.copyMachine, StandardTapeCommands.copy, StandardTerminatedCopy.machine]) copied
  refine ⟨Function.update changed 1 (buffer (word (next operands).2)), ?_, rightLength, nextLength, ?_,
    Function.update_self _ _ _, ?_⟩
  · convert complete using 1 <;> first | rfl | (simp [rightLength, nextLength]; ring)
  · simp [changed, next]
  · intro name
    exact complete.region name (regions name)

noncomputable def guard : Machine Alphabet StandardBinaryGuard.State :=
  MultiTape.wire (twoTapes 1 8 (by decide)) StandardBinaryGuard.machine

private theorem guard_runs (digits : ℕ) (operands : List Bool × List Bool) (initial : Tapes Alphabet)
    (represented : Represents digits operands initial) :
    ∃ final, Runs (widths digits) (fun _ => false) guard (2 * digits + 2)
      (false, 0) (fun _ => 0) initial (false, 2) (fun _ => 0) final ∧
      Represents digits operands final ∧ final 8 = buffer [data (operands.2.any id)] := by
  rcases represented with ⟨leftLength, rightLength, leftEq, rightEq, regions⟩
  obtain ⟨flags, flagLength, flagEq⟩ := (regions 8).exists_buffer
  change flags.length = 1 at flagLength
  obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  obtain ⟨final, trace, located, outside, immutable⟩ := (StandardBinaryGuard.runs operands.2 flag).wire_restoring
    (twoTapes 1 8 (by decide)) (widths digits) (fun _ => false)
    (by intro name; cases name <;> simp [widths, StandardBinaryGuard.widths, rightLength])
    (by intro name premise; cases premise) initial
    (by
      intro name
      cases name
      · exact rightEq.trans (buffer_padding _).symm
      · exact flagEq.trans (buffer_padding _).symm)
  refine ⟨final, ?_, ⟨leftLength, rightLength, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [rightLength, guard] using trace
  · exact (outside 6 (by rintro ⟨name, equal⟩; cases name <;> contradiction)).trans leftEq
  · exact (immutable false rfl).trans rightEq
  · intro name
    exact trace.region name (regions name)
  · exact (located true).trans (buffer_padding [data (operands.2.any id)])

def result (symbols : Symbols Alphabet) : Bool := symbols 8 == 2
noncomputable def loop : Machine Alphabet (Sum StandardBinaryGuard.State BodyState) :=
  MultiTape.whileMachine guard body (false, 0) bodyEntry result
abbrev State := Sum (Sum StandardBinaryGuard.State BodyState) Unit
noncomputable def machine : Machine Alphabet State := MultiTape.withExit loop
def entry : State := .inl (.inl (false, 0))
def exit : State := .inr ()

/-- Euclidean iteration tracks only its operands and mathematical invariant. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (initial : Tapes Alphabet) (leftEq : initial 6 = buffer (word left))
    (rightEq : initial 1 = buffer (word right))
    (regions : ∀ name, Region (widths right.length name) 0 (initial name))
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    ∃ ticks finalLeft finalRight final,
      ticks ≤ 32 * right.length ^ 3 + 160 * right.length ^ 2 + 240 * right.length + 128 ∧
      finalLeft.length = right.length ∧ finalRight.length = right.length ∧
      Runs (widths right.length) (fun _ => false) machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final 6 = buffer (word finalLeft) ∧ final 1 = buffer (word finalRight) ∧
      value finalRight = 0 ∧ value finalLeft = Nat.gcd (value left) (value right) := by
  let numbers (operands : List Bool × List Bool) := (value operands.1, value operands.2)
  let representation (operands : List Bool × List Bool) (tapes : Tapes Alphabet) :=
    Represents right.length operands tapes ∧
      2 * value operands.2 ≤ 2 ^ right.length ∧ Gcd.answer (numbers operands) = Nat.gcd (value left) (value right)
  let guardedRepresentation operands tapes := representation operands tapes ∧
    tapes 8 = buffer [data (operands.2.any id)]
  have stepValue (operands : List Bool × List Bool) (tapes : Tapes Alphabet)
      (represented : representation operands tapes) (active : Gcd.condition (numbers operands) = true) :
      numbers (next operands) = Gcd.advance (numbers operands) := by
    have positive : 0 < value operands.2 := by simpa [Gcd.condition, numbers, Nat.pos_iff_ne_zero] using active
    have remainderValue := (StandardBinaryDivision.result_value operands.1 operands.2 positive
      (by simpa only [represented.1.2.1] using represented.2.1)
      (by simpa only [represented.1.1, represented.1.2.1] using Binary.value_lt_pow_length operands.1)).2
    exact Prod.ext rfl remainderValue
  obtain ⟨ticks, final, terminal, cost, trace, guarded, stopped⟩ := Runs.whileValues
    (widths right.length) (fun _ => false) guard body (false, 0) (false, 2) bodyEntry bodyExit result
    representation guardedRepresentation
    (fun operands => Gcd.condition (numbers operands)) (fun operands => Gcd.measure (numbers operands)) (2 * right.length + 2) (12 * right.length ^ 2 + 35 * right.length + 18)
    (by intro symbols; simp [guard, MultiTape.wire, StandardBinaryGuard.machine])
    (by intro symbols; simp [body, bodyExit, MultiTape.sequence, secondCopy,
      StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine])
    (by
      intro operands tapes represented
      obtain ⟨final, trace, correct, flag⟩ := guard_runs right.length operands tapes represented.1
      exact ⟨_, final, le_rfl, trace, ⟨⟨correct, represented.2⟩, flag⟩⟩)
    (by
      intro operands tapes represented active
      obtain ⟨final, trace, correct⟩ := body_runs right.length operands tapes represented.1.1
      have changed := stepValue operands tapes represented.1 active
      refine ⟨next operands, _, final, le_rfl, trace, ⟨correct, ?_, ?_⟩, ?_⟩
      · have smaller := Nat.mod_lt (value operands.1) (show 0 < value operands.2 by
          simpa [Gcd.condition, numbers, Nat.pos_iff_ne_zero] using active)
        have nextValue := congrArg Prod.snd changed
        change value (next operands).2 = value operands.1 % value operands.2 at nextValue
        rw [nextValue]
        have fits := represented.1.2.1
        omega
      · exact (congrArg Gcd.answer changed).trans ((Gcd.conserves _).trans represented.1.2.2)
      · rw [changed]
        exact Gcd.decreases _ active)
    (by
      intro operands tapes represented
      unfold result MultiTape.read
      rw [represented.2]
      have tested : operands.2.any id = Gcd.condition (numbers operands) := by
        apply Bool.eq_iff_iff.mpr
        simpa [Gcd.condition, numbers, Nat.pos_iff_ne_zero] using Binary.any_iff_positive operands.2
      cases testedValue : operands.2.any id <;> simpa [testedValue, buffer, data, Turing.Tape.mk₁, Turing.Tape.mk₂] using tested)
    (left, right) initial ⟨⟨sameLength, rfl, leftEq, rightEq, regions⟩, capacity, rfl⟩
  rcases guarded.1 with ⟨represented, finalCapacity, answer⟩
  rcases represented with ⟨leftLength, rightLength, finalLeftEq, finalRightEq, finalRegions⟩
  have zero : value terminal.2 = 0 := by simpa [Gcd.condition, numbers] using stopped
  have correct : value terminal.1 = Nat.gcd (value left) (value right) :=
    (Gcd.terminal _ stopped).symm.trans answer
  have measureBound := Gcd.measure_bound right.length (numbers (left, right))
    ⟨by simpa [numbers, sameLength] using Binary.value_lt_pow_length left,
      Binary.value_lt_pow_length right⟩
  have flagFalse : terminal.2.any id = false := by
    apply Bool.eq_false_iff.mpr
    intro tested
    have positive := (Binary.any_iff_positive terminal.2).mp tested
    omega
  have halted : loop (.inl (false, 2)) (MultiTape.read final) = none := by
    simp [loop, MultiTape.whileMachine, guard, MultiTape.wire, StandardBinaryGuard.machine,
      result, MultiTape.read, guarded.2, flagFalse, data, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂]
  refine ⟨ticks + 1, terminal.1, terminal.2, final, ?_, leftLength, rightLength,
    trace.withExit_at halted, finalLeftEq, finalRightEq, zero, correct⟩
  nlinarith [cost]

end Polytime2.StandardGcdMachine
