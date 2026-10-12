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

import Polytime2.Wiring
import Polytime2.Gcd
import Polytime2.BinaryRemainder
import Polytime2.BinaryGuard
import Polytime2.TerminatedCopy
import Polytime2.BinaryOutput

/-! # Gcd on a shared multi-tape workspace

The operands and a reusable remainder occupy equally padded binary tapes.
A separate flag tape supplies the loop guard. The Euclidean body clears scratch,
computes one remainder, then copies the two new operands into place.
-/

namespace Polytime2.GcdMachine

open MultiTape
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 4 => Symbol
abbrev GuardState := Bool × Fin 3
abbrev BodyState := Sum (BinaryScan.State Unit) (Sum BinaryRemainder.State (Sum (Fin 3) (Fin 3)))
abbrev State := Sum (Sum GuardState BodyState) Unit

def frame (left right scratch : List Bool) (flag : Bool) : Tapes Alphabet := fun name =>
  if name = 0 then Binary.tape [3] (word left ++ [0]) ()
  else if name = 1 then Binary.tape [3] (word right ++ [0]) ()
  else if name = 2 then Binary.tape [3] (word scratch ++ [0]) ()
  else Binary.tape [3] [data flag] ()

def remainderWiring : Fin 3 ↪ Fin 4 where
  toFun name := ⟨name.val, by omega⟩
  inj' := by intro first second equal; exact Fin.ext (congrArg (fun name : Fin 4 => name.val) equal)

def guardWiring : Bool ↪ Fin 4 := twoTapes 1 3 (by decide)
def copyWiring (second : Bool) : Bool ↪ Fin 4 :=
  twoTapes (if second then 2 else 1) (if second then 1 else 0) (by cases second <;> decide)

noncomputable def guard : Machine Alphabet GuardState := wire guardWiring BinaryGuard.machine
noncomputable def clear : Machine Alphabet (BinaryScan.State Unit) :=
  wire (oneTape 2) (BinaryScan.machine BinaryScan.clear)
noncomputable def remainder : Machine Alphabet BinaryRemainder.State :=
  wire remainderWiring BinaryRemainder.machine
noncomputable def copy (second : Bool) : Machine Alphabet (Fin 3) :=
  wire (copyWiring second) TerminatedCopy.machine

noncomputable def body : Machine Alphabet BodyState :=
  MultiTape.sequence clear (MultiTape.sequence remainder
    (MultiTape.sequence (copy false) (copy true) 0) (.inl 0)) (.inl BinaryRemainder.entry)

def bodyEntry : BodyState := .inl (.inl ())
def bodyExit : BodyState := .inr (.inr (.inr 2))

private theorem clear_steps (left right scratch : List Bool) (flag : Bool) :
    Steps clear (2 * scratch.length + 3) (.inl (), frame left right scratch flag)
      (.inr ((), true), frame left right (List.replicate scratch.length false) flag) := by
  have trace := BinaryScan.steps BinaryScan.clear () scratch [] []
  simp only [BinaryScan.clear_run] at trace
  apply wire_steps_of_eq (oneTape 2) _ trace
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name
    · rfl
    · rfl
    · exact False.elim (outside ⟨(), rfl⟩)
    · rfl

private theorem remainder_steps (left right scratch : List Bool) (flag : Bool)
    (sameLength : right.length = scratch.length) (bounded : value scratch < value right)
    (capacity : 2 * value right ≤ 2 ^ scratch.length) :
    ∃ ticks, ticks ≤ left.length * (6 * scratch.length + 16) + 3 ∧ Steps remainder ticks
      (BinaryRemainder.entry, frame left right scratch flag)
      (BinaryRemainder.exit, frame left right (BinaryRemainder.finish right left.reverse scratch) flag) := by
  obtain ⟨ticks, cost, trace⟩ := BinaryRemainder.steps left right scratch sameLength bounded capacity
  refine ⟨ticks, cost, ?_⟩
  apply wire_steps_of_eq remainderWiring _ trace
  · intro name; fin_cases name <;> rfl
  · intro name; fin_cases name <;> rfl
  · intro name outside
    fin_cases name
    · exact False.elim (outside ⟨0, rfl⟩)
    · exact False.elim (outside ⟨1, rfl⟩)
    · exact False.elim (outside ⟨2, rfl⟩)
    · rfl

private theorem copy_steps (second : Bool) (left right scratch : List Bool) (flag : Bool)
    (rightLength : right.length = left.length) (scratchLength : scratch.length = left.length) :
    Steps (copy second) (2 * left.length + 3) (0, frame left right scratch flag)
      (2, if second then frame left scratch scratch flag else frame right right scratch flag) := by
  cases second
  · have trace := TerminatedCopy.steps right (word left) (by simp [word, rightLength]) [] [] [] []
    rw [rightLength] at trace
    apply wire_steps_of_eq (copyWiring false) _ trace
    · intro name; cases name <;> rfl
    · intro name; cases name <;> rfl
    · intro name outside
      fin_cases name
      · exact False.elim (outside ⟨true, rfl⟩)
      · exact False.elim (outside ⟨false, rfl⟩)
      · rfl
      · rfl
  · have trace := TerminatedCopy.steps scratch (word right) (by simp [word, rightLength, scratchLength]) [] [] [] []
    rw [scratchLength] at trace
    apply wire_steps_of_eq (copyWiring true) _ trace
    · intro name; cases name <;> rfl
    · intro name; cases name <;> rfl
    · intro name outside
      fin_cases name
      · rfl
      · exact False.elim (outside ⟨true, rfl⟩)
      · exact False.elim (outside ⟨false, rfl⟩)
      · rfl

/-- One Euclidean step, preserving widths and the caller's flag. -/
theorem body_steps (left right scratch : List Bool) (flag : Bool)
    (rightLength : right.length = left.length) (scratchLength : scratch.length = left.length)
    (positive : 0 < value right) (capacity : 2 * value right ≤ 2 ^ left.length) :
    ∃ ticks output, ticks ≤ left.length * (6 * left.length + 22) + 15 ∧
      output.length = left.length ∧ value output = value left % value right ∧ Steps body ticks
        (bodyEntry, frame left right scratch flag) (bodyExit, frame right output output flag) := by
  let zeros := List.replicate left.length false
  have zeroLength : zeros.length = left.length := by simp [zeros]
  have cleared := clear_steps left right scratch flag
  rw [scratchLength] at cleared
  obtain ⟨remTicks, remCost, remTrace⟩ := remainder_steps left right zeros flag
    (by omega) (by simpa [zeros] using positive) (by simpa only [zeroLength] using capacity)
  let output := BinaryRemainder.finish right left.reverse zeros
  have outputLength : output.length = left.length :=
    (BinaryRemainder.finish_length left.reverse zeros right (by omega)).trans zeroLength
  have outputValue : value output = value left % value right := by
    have correct := BinaryRemainder.finish_value left.reverse zeros right (by omega)
      (by simpa [zeros] using positive) (by simpa only [zeroLength] using capacity)
    simpa [zeros] using correct
  have firstCopy := copy_steps false left right output flag rightLength outputLength
  have secondCopy := copy_steps true right right output flag rfl (by omega)
  rw [rightLength] at secondCopy
  have copied := sequence_steps (copy false) (copy true) 0 firstCopy
    (by intro symbols; simp [copy, wire, TerminatedCopy.machine]) secondCopy
  have afterRemainder := sequence_steps remainder (sequence (copy false) (copy true) 0) (.inl 0)
    remTrace (by intro symbols; simp [remainder, wire, BinaryRemainder.machine, BinaryRemainder.exit]) copied
  have complete := sequence_steps clear (sequence remainder (sequence (copy false) (copy true) 0) (.inl 0))
    (.inl BinaryRemainder.entry) cleared (by intro symbols; simp [clear, wire, BinaryScan.machine]) afterRemainder
  refine ⟨_, output, ?_, outputLength, outputValue, complete⟩
  rw [zeroLength] at remCost
  nlinarith

private theorem guard_steps (left right scratch : List Bool) (flag : Bool) :
    Steps guard (2 * right.length + 3) ((false, 0), frame left right scratch flag)
      ((false, 2), frame left right scratch (right.any id)) := by
  apply wire_steps_of_eq guardWiring _ (BinaryGuard.steps right [] [] [3] [] (data flag))
  · intro name; cases name <;> rfl
  · intro name; cases name <;> rfl
  · intro name outside
    fin_cases name
    · rfl
    · exact False.elim (outside ⟨false, rfl⟩)
    · rfl
    · exact False.elim (outside ⟨true, rfl⟩)

/-- Scratch and the previous guard flag are existential, not logical inputs. -/
def representation (sizes : Unit → ℕ) (operands : Gcd.Value) (tapes : Tapes Alphabet) : Prop :=
  ∃ left right scratch flag, left.length = sizes () + 1 ∧ right.length = sizes () + 1 ∧
    scratch.length = sizes () + 1 ∧ value left = operands.1 ∧ value right = operands.2 ∧
    tapes = frame left right scratch flag

def guardedRepresentation (sizes : Unit → ℕ) (operands : Gcd.Value) (tapes : Tapes Alphabet) : Prop :=
  ∃ left right scratch, left.length = sizes () + 1 ∧ right.length = sizes () + 1 ∧
    scratch.length = sizes () + 1 ∧ value left = operands.1 ∧ value right = operands.2 ∧
    tapes = frame left right scratch (Gcd.condition operands)

theorem guard_contract : Computes guard (false, 0) (false, 2) representation guardedRepresentation
    (fun sizes operands => operands.1 < 2 ^ sizes () ∧ operands.2 < 2 ^ sizes ()) (fun _ operands => operands) := by
  refine ⟨by intro symbols; rfl, 2 * MvPolynomial.X () + 5, ?_⟩
  intro sizes operands initial _ represented
  obtain ⟨left, right, scratch, flag, leftLength, rightLength, scratchLength, leftValue, rightValue, rfl⟩ := represented
  have flagCorrect : right.any id = Gcd.condition operands := by
    apply Bool.eq_iff_iff.mpr
    rw [BinaryGuard.any_iff_positive]
    simp only [Gcd.condition, decide_eq_true_eq, rightValue, Nat.pos_iff_ne_zero]
  refine ⟨2 * right.length + 3, _, ?_, guard_steps left right scratch flag,
    left, right, scratch, leftLength, rightLength, scratchLength, leftValue, rightValue, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · rw [flagCorrect]

theorem body_contract : Computes body bodyEntry bodyExit guardedRepresentation representation
    (fun sizes operands => (operands.1 < 2 ^ sizes () ∧ operands.2 < 2 ^ sizes ()) ∧ Gcd.condition operands = true)
    (fun _ operands => Gcd.advance operands) := by
  refine ⟨by intro symbols; rfl, 8 * (MvPolynomial.X () + 3) ^ 2, ?_⟩
  intro sizes operands initial valid represented
  obtain ⟨left, right, scratch, leftLength, rightLength, scratchLength, leftValue, rightValue, rfl⟩ := represented
  have positive : 0 < value right := by
    rw [rightValue]
    simpa [Gcd.condition, Nat.pos_iff_ne_zero] using valid.2
  have capacity : 2 * value right ≤ 2 ^ left.length := by
    rw [leftLength, pow_succ]
    nlinarith [valid.1.2]
  obtain ⟨ticks, output, cost, outputLength, outputValue, trace⟩ :=
    body_steps left right scratch (Gcd.condition operands) (by omega) (by omega) positive capacity
  refine ⟨ticks, _, ?_, trace, right, output, output, Gcd.condition operands,
    rightLength, outputLength.trans leftLength, outputLength.trans leftLength, rightValue, ?_, rfl⟩
  · simp only [map_mul, map_pow, map_add, map_ofNat, MvPolynomial.eval_X]
    rw [leftLength] at cost
    nlinarith
  · simpa only [Gcd.advance, leftValue, rightValue] using outputValue

def result (symbols : Symbols Alphabet) : Bool := symbols 3 == 2

private theorem result_correct (sizes : Unit → ℕ) (operands : Gcd.Value) (tapes : Tapes Alphabet)
    (represented : guardedRepresentation sizes operands tapes) : result (read tapes) = Gcd.condition operands := by
  obtain ⟨left, right, scratch, _, _, _, _, _, rfl⟩ := represented
  cases Gcd.condition operands <;> simp [result, MultiTape.read, frame, Binary.tape, data]

noncomputable def machine : Machine Alphabet State := withExit (whileMachine guard body (false, 0) bodyEntry result)
def entry : State := .inl (.inl (false, 0))
def exit : State := .inr ()

/-- A complete finite multi-tape gcd machine with a polynomial runtime bound.
Only the external parsing and physical output extraction belong to its wrapper. -/
theorem contract : Computes machine entry exit representation
    (BinaryOutput.representation 0 (MvPolynomial.X () + 1))
    (fun sizes operands => operands.1 < 2 ^ sizes () ∧ operands.2 < 2 ^ sizes ())
    (fun _ operands => Nat.gcd operands.1 operands.2) := by
  have certificate := Gcd.contract result representation guardedRepresentation
    guard_contract body_contract result_correct
  apply Computes.adapt certificate (fun _ _ good => good) (fun _ _ _ encoded => encoded)
  intro sizes output tapes represented
  obtain ⟨terminal, encoded, _, correct⟩ := represented
  obtain ⟨left, right, scratch, leftLength, _, _, leftValue, _, rfl⟩ := encoded
  refine ⟨left, leftValue.trans correct, ?_, rfl⟩
  simp only [map_add, MvPolynomial.eval_X, map_one]
  omega

end Polytime2.GcdMachine
