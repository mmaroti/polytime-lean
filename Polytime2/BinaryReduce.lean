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
import Polytime2.BinaryInPlace
import Polytime2.BinaryAddition
import Polytime2.BinarySubtraction

/-! # One restoring binary remainder step

When the first operand is less than twice the positive divisor, subtract once
and add back on underflow. Both scans retain the final carry/borrow in finite
controller memory. No repeated subtraction by numeric magnitude is used.
-/

namespace Polytime2.BinaryReduce

open MultiTape
open Binary (Symbol word value)
open Copy (frame)

abbrev Alphabet := BinaryInPlace.Alphabet
abbrev ArithmeticState := BinaryInPlace.State
abbrev State := Sum (Sum ArithmeticState ArithmeticState) Unit

abbrev subtraction := BinaryInPlace.machine BinarySubtraction.digit BinarySubtraction.borrow
abbrev addition := BinaryInPlace.machine BinaryAddition.digit BinaryAddition.carry

def reduced (left right : List Bool) : List Bool :=
  let difference := BinarySubtraction.ripple false left right
  if difference.2 then (BinaryAddition.ripple false difference.1 right).1 else difference.1

@[simp] theorem reduced_length (left right : List Bool) (sameLength : right.length = left.length) :
    (reduced left right).length = left.length := by
  have differenceLength : (BinarySubtraction.ripple false left right).1.length = left.length :=
    BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength
  unfold reduced
  dsimp only
  split
  · rw [BinaryRipple.ripple_length BinaryAddition.digit BinaryAddition.carry false _ right (by omega)]
    exact differenceLength
  · exact differenceLength

/-- Restoring a borrowed subtraction recovers the original low digits. -/
private theorem restored_value (left right : List Bool) (sameLength : right.length = left.length)
    (borrowed : (BinarySubtraction.ripple false left right).2 = true) :
    value (BinaryAddition.ripple false (BinarySubtraction.ripple false left right).1 right).1 = value left := by
  have differenceLength : (BinarySubtraction.ripple false left right).1.length = left.length :=
    BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength
  have difference := BinarySubtraction.ripple_equation false left right sameLength
  have restored := BinaryAddition.ripple_value false (BinarySubtraction.ripple false left right).1 right (by omega)
  have lowBound := Binary.value_lt_pow_length (BinaryAddition.ripple false (BinarySubtraction.ripple false left right).1 right).1
  rw [BinaryRipple.ripple_length BinaryAddition.digit BinaryAddition.carry false _ right (by omega),
    differenceLength] at lowBound
  have originalBound := Binary.value_lt_pow_length left
  simp only [borrowed, Bool.toNat_true, Bool.toNat_false, Nat.add_zero, Nat.mul_one] at difference
  simp only [differenceLength, Bool.toNat_false, Nat.add_zero] at restored
  cases finalCarry : (BinaryAddition.ripple false (BinarySubtraction.ripple false left right).1 right).2 <;>
    simp only [finalCarry, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at restored <;> omega

/-- Under the restoring-division invariant the result is the exact remainder. -/
theorem reduced_value (left right : List Bool) (sameLength : right.length = left.length)
    (small : value left < 2 * value right) : value (reduced left right) = value left % value right := by
  by_cases borrowed : (BinarySubtraction.ripple false left right).2 = true
  · simp only [reduced, borrowed, ↓reduceIte]
    rw [restored_value left right sameLength borrowed,
      Nat.mod_eq_of_lt ((BinarySubtraction.underflow_iff left right sameLength).mp borrowed)]
  · have nonnegative : value right ≤ value left := by
      have notLess := mt (BinarySubtraction.underflow_iff left right sameLength).mpr borrowed
      omega
    have noBorrow : (BinarySubtraction.ripple false left right).2 = false := Bool.eq_false_iff.mpr borrowed
    simp only [reduced, noBorrow, Bool.false_eq_true, ↓reduceIte]
    rw [BinarySubtraction.difference_of_no_borrow left right sameLength nonnegative]
    rw [Nat.mod_eq_sub_mod nonnegative, Nat.mod_eq_of_lt (show value left - value right < value right by omega)]

/-- A halting subtraction branches on its retained borrow; addition restores
only the borrowed case. -/
def raw : Machine Alphabet (Sum ArithmeticState ArithmeticState)
  | .inl state, symbols => match subtraction state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => if state = .inr (true, true) then some (.inr (.inl false), stationary symbols) else none
  | .inr state, symbols => (addition state symbols).map fun command => (.inr command.1, command.2)

def machine : Machine Alphabet State := withExit raw

def entry : State := .inl (.inl (.inl false))
def exit : State := .inr ()

/-- At most two linear scans, preserving the divisor, neighbors, and heads. -/
theorem steps (left right : List Bool) (sameLength : right.length = left.length)
    (leftFirst leftSecond tailFirst tailSecond : List Symbol) :
    ∃ ticks, ticks ≤ 4 * left.length + 8 ∧ Steps machine ticks
      (entry, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond))
      (exit, frame (3 :: leftFirst) (word (reduced left right) ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond)) := by
  have differenceLength : (BinarySubtraction.ripple false left right).1.length = left.length :=
    BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength
  have subTrace := BinaryInPlace.steps BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength leftFirst leftSecond tailFirst tailSecond
  have subLift := subTrace.rename Sum.inl (target := raw)
    (by intro state symbols next actions transition; simp [raw, subtraction, transition])
  cases borrowed : (BinarySubtraction.ripple false left right).2 with
  | false =>
    rw [borrowed] at subLift
    have halted : step raw
        (.inl (.inr (false, true)), frame (3 :: leftFirst)
          (word (BinarySubtraction.ripple false left right).1 ++ 0 :: tailFirst)
          (3 :: leftSecond) (word right ++ 0 :: tailSecond)) = none := by
      simp [step, raw, subtraction, BinaryInPlace.machine]
    refine ⟨2 * left.length + 3 + 1, by omega, ?_⟩
    simpa only [machine, entry, exit, reduced, borrowed, Bool.false_eq_true, ↓reduceIte] using
      withExit_steps raw subLift halted
  | true =>
    rw [borrowed] at subLift
    have addTrace := BinaryInPlace.steps BinaryAddition.digit BinaryAddition.carry
      false (BinarySubtraction.ripple false left right).1 right (by omega)
      leftFirst leftSecond tailFirst tailSecond
    have addLift := addTrace.rename Sum.inr (target := raw)
      (by intro state symbols next actions transition; simp [raw, addition, transition])
    have handover : step raw
        (.inl (.inr (true, true)), frame (3 :: leftFirst)
          (word (BinarySubtraction.ripple false left right).1 ++ 0 :: tailFirst)
          (3 :: leftSecond) (word right ++ 0 :: tailSecond)) =
        some (.inr (.inl false), frame (3 :: leftFirst)
          (word (BinarySubtraction.ripple false left right).1 ++ 0 :: tailFirst)
          (3 :: leftSecond) (word right ++ 0 :: tailSecond)) := by
      simp [step, raw, subtraction, BinaryInPlace.machine]
    have halted : step raw
        (.inr (.inr ((BinaryAddition.ripple false (BinarySubtraction.ripple false left right).1 right).2, true)),
          frame (3 :: leftFirst)
            (word (BinaryAddition.ripple false (BinarySubtraction.ripple false left right).1 right).1 ++ 0 :: tailFirst)
            (3 :: leftSecond) (word right ++ 0 :: tailSecond)) = none := by
      simp [step, raw, addition, BinaryInPlace.machine]
    have complete := withExit_steps raw (subLift.trans (.next handover addLift)) halted
    refine ⟨2 * left.length + 3 + (2 * (BinarySubtraction.ripple false left right).1.length + 3 + 1) + 1, ?_, ?_⟩
    · simp only [differenceLength]
      omega
    · simpa only [machine, entry, exit, reduced, borrowed, ↓reduceIte] using complete

end Polytime2.BinaryReduce
