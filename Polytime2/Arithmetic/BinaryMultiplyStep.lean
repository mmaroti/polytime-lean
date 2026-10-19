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

import Polytime2.Arithmetic.BinaryArithmetic
import Polytime2.Arithmetic.BinaryScan
import Polytime2.Arithmetic.BinaryAddition

/-! # One fixed-width multiplication step

Horner multiplication doubles the accumulator and optionally adds the factor.
Both operands are immutable; the shifted word, result, and carry have separate
fixed regions. The Boolean choice selects one of two fixed finite controllers.
-/

namespace Polytime2.StandardBinaryMultiplyStep

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 5)
abbrev State := Sum (Sum (StandardBinaryScan.State Bool) StandardBinaryArithmetic.State) Unit

def frame (current factor : List Bool) (shifted result : List Symbol) (flag : Symbol) :
    Tapes Alphabet := fun name =>
  if name = 0 then buffer (word current)
  else if name = 1 then buffer (word factor)
  else if name = 2 then buffer shifted
  else if name = 3 then buffer result
  else buffer [flag]

def widths (digits : ℕ) (name : Fin 5) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 5) : Bool := decide (name.val < 2)

def digit (enabled left right previous : Bool) : Bool :=
  BinaryAddition.digit left (enabled && right) previous

def carry (enabled left right previous : Bool) : Bool :=
  BinaryAddition.carry left (enabled && right) previous

def shifted (current : List Bool) : List Bool := (BinaryScan.run BinaryScan.shift false current).2

def added (enabled : Bool) (current factor : List Bool) : List Bool × Bool :=
  BinaryRipple.ripple (digit enabled) (carry enabled) false (shifted current) factor

@[simp] theorem shifted_length (current : List Bool) :
    (shifted current).length = current.length := BinaryScan.run_length _ _ _

@[simp] theorem added_length (enabled : Bool) (current factor : List Bool)
    (sameLength : factor.length = current.length) :
    (added enabled current factor).1.length = current.length := by
  exact (BinaryRipple.ripple_length _ _ _ _ _ (sameLength.trans (shifted_length current).symm)).trans
    (shifted_length current)

private theorem selected_ripple (enabled previous : Bool) (left right : List Bool) :
    BinaryRipple.ripple (digit enabled) (carry enabled) previous left right =
      BinaryAddition.ripple previous left (right.map (fun bit => enabled && bit)) := by
  induction left generalizing previous right with
  | nil => rfl
  | cons bit bits hypothesis =>
    cases right with
    | nil => rfl
    | cons other rest => simp [BinaryRipple.ripple, BinaryAddition.ripple, digit, carry, hypothesis]

/-- The capacity hypothesis rules out both shift and addition overflow. -/
theorem added_value (enabled : Bool) (current factor : List Bool)
    (sameLength : factor.length = current.length)
    (capacity : 2 * value current + (if enabled then value factor else 0) < 2 ^ current.length) :
    value (added enabled current factor).1 =
      2 * value current + (if enabled then value factor else 0) ∧
      (added enabled current factor).2 = false := by
  have shiftCapacity : false.toNat + 2 * value current < 2 ^ current.length := by
    simp only [Bool.toNat_false]
    omega
  have shiftValue := (BinaryScan.shift_value false current shiftCapacity).1
  simp only [Bool.toNat_false, zero_add] at shiftValue
  have selectedValue : value (factor.map (fun bit => enabled && bit)) =
      if enabled then value factor else 0 := by
    cases enabled <;> simp
  have equation := BinaryAddition.ripple_value false (shifted current)
    (factor.map (fun bit => enabled && bit)) (by simp [sameLength])
  rw [← selected_ripple, selectedValue, shifted_length] at equation
  change value (added enabled current factor).1 +
    2 ^ current.length * (added enabled current factor).2.toNat = _ at equation
  change value (shifted current) = 2 * value current at shiftValue
  rw [shiftValue] at equation
  simp only [Bool.toNat_false, Nat.add_zero] at equation
  cases flag : (added enabled current factor).2 with
  | false => simpa [flag] using equation
  | true => simp only [flag, Bool.toNat_true, Nat.mul_one] at equation; omega

/-- Fixed-width arithmetic always computes the corresponding modular value. -/
theorem added_mod (enabled : Bool) (current factor : List Bool)
    (sameLength : factor.length = current.length) :
    value (added enabled current factor).1 =
      (2 * value current + (if enabled then value factor else 0)) % 2 ^ current.length := by
  have shiftBound : value (shifted current) < 2 ^ current.length := by
    simpa only [shifted_length] using Binary.value_lt_pow_length (shifted current)
  have shiftEquation := congrArg (fun number => number % 2 ^ current.length)
    (BinaryScan.shift_equation false current)
  change (value (shifted current) + 2 ^ current.length *
    (BinaryScan.run BinaryScan.shift false current).1.toNat) % 2 ^ current.length = _ at shiftEquation
  have shiftMod : value (shifted current) = (2 * value current) % 2 ^ current.length := by
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt shiftBound] using shiftEquation
  have selectedValue : value (factor.map (fun bit => enabled && bit)) =
      if enabled then value factor else 0 := by cases enabled <;> simp
  have equation := BinaryAddition.ripple_value false (shifted current)
    (factor.map (fun bit => enabled && bit)) (by simp [sameLength])
  rw [← selected_ripple, selectedValue, shifted_length] at equation
  change value (added enabled current factor).1 +
    2 ^ current.length * (added enabled current factor).2.toNat = _ at equation
  have resultBound : value (added enabled current factor).1 < 2 ^ current.length := by
    simpa only [added_length enabled current factor sameLength] using
      Binary.value_lt_pow_length (added enabled current factor).1
  have reduced := congrArg (fun number => number % 2 ^ current.length) equation
  simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt resultBound, shiftMod] using reduced

def shiftWiring : Bool ↪ Fin 5 :=
  ⟨(fun name => if name then 2 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

def additionWiring : Fin 4 ↪ Fin 5 :=
  ⟨(fun name => match name.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 4), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem shiftWiring_apply (name : Bool) : shiftWiring name = (if name then 2 else 0) := rfl
@[simp] theorem additionWiring_apply (name : Fin 4) :
    additionWiring name = (match name.val with | 0 => 2 | 1 => 1 | 2 => 3 | _ => 4) := rfl

noncomputable def shiftMachine : Machine Alphabet (StandardBinaryScan.State Bool) :=
  MultiTape.wire shiftWiring (StandardBinaryScan.machine BinaryScan.shift)

noncomputable def additionMachine (enabled : Bool) : Machine Alphabet StandardBinaryArithmetic.State :=
  MultiTape.wire additionWiring (StandardBinaryArithmetic.machine (digit enabled) (carry enabled))

noncomputable def machine (enabled : Bool) : Machine Alphabet State :=
  MultiTape.withExit (MultiTape.sequence shiftMachine (additionMachine enabled) (.inl false))

def entry : State := .inl (.inl (.inl false))
def exit : State := .inr ()

/-- All three writable tapes are fully written from arbitrary old contents;
both operands and the surrounding blanks are preserved at every step. -/
theorem runs (enabled : Bool) (current factor : List Bool)
    (sameLength : factor.length = current.length) (oldShifted oldResult : List Symbol)
    (shiftedLength : oldShifted.length = current.length)
    (resultLength : oldResult.length = current.length) (oldFlag : Symbol) :
    Runs (widths current.length) readOnly (machine enabled) (4 * current.length + 6)
      entry (fun _ => 0) (frame current factor oldShifted oldResult oldFlag)
      exit (fun _ => 0) (frame current factor (word (shifted current))
        (word (added enabled current factor).1) (data (added enabled current factor).2)) := by
  have shiftTrace := (StandardBinaryScan.runs BinaryScan.shift false current oldShifted shiftedLength).wire_of_eq
    shiftWiring (widths current.length) readOnly
    (by intro name; cases name <;> rfl)
    (by intro name premise; cases name <;> simp_all [readOnly, shiftWiring_apply])
    (frame current factor oldShifted oldResult oldFlag)
    (frame current factor (word (shifted current)) oldResult oldFlag)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by intro name; cases name <;> exact (buffer_padding _).symm)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨false, rfl⟩)
      · rfl
      · exact False.elim (outside ⟨true, rfl⟩)
      · rfl
      · rfl)
  have additionTrace := (StandardBinaryArithmetic.runs (digit enabled) (carry enabled)
    false (shifted current) factor (by simpa using sameLength) oldResult
    (by simpa using resultLength) oldFlag).wire_of_eq
    additionWiring (widths current.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardBinaryArithmetic.width, shifted_length])
    (by intro name premise; fin_cases name <;>
      simp_all [readOnly, StandardBinaryArithmetic.readOnly])
    (frame current factor (word (shifted current)) oldResult oldFlag)
    (frame current factor (word (shifted current)) (word (added enabled current factor).1)
      (data (added enabled current factor).2))
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by
      intro name outside
      fin_cases name
      · rfl
      · exact False.elim (outside ⟨1, rfl⟩)
      · exact False.elim (outside ⟨0, rfl⟩)
      · exact False.elim (outside ⟨2, rfl⟩)
      · exact False.elim (outside ⟨3, rfl⟩))
  have complete := (shiftTrace.sequence (additionMachine enabled) (.inl false)
    (by intro symbols; simp [MultiTape.wire, StandardBinaryScan.machine]) additionTrace).withExit
    (by intro symbols; simp [MultiTape.sequence, additionMachine, MultiTape.wire,
      StandardBinaryArithmetic.machine])
  simp only [shifted_length] at complete
  convert complete using 1 <;> first | rfl | omega

end Polytime2.StandardBinaryMultiplyStep
