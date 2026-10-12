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

import Polytime2.Complexity
import Polytime2.Contracts
import Polytime2.BinaryRipple

/-! # Runtime-width binary subtraction

A finite borrow bit drives the shared ripple scanner. The output consists of
capacity-many difference digits followed by the final borrow. Together these
are the exact signed difference in two's complement, with no overflow.
-/

namespace Polytime2.BinarySubtraction

open MultiTape
open Binary (Symbol word value)

abbrev Alphabet := BinaryRipple.Alphabet
abbrev State := BinaryRipple.State

def digit (left right previous : Bool) : Bool := (left != right) != previous

def borrow (left right previous : Bool) : Bool :=
  (!left && (right || previous)) || (right && previous)

abbrev ripple := BinaryRipple.ripple digit borrow
abbrev subtract := BinaryRipple.output digit borrow
abbrev frame := BinaryRipple.frame
abbrev machine := BinaryRipple.machine digit borrow

private theorem digit_equation (left right previous : Bool) :
    (digit left right previous).toNat + right.toNat + previous.toNat =
      left.toNat + 2 * (borrow left right previous).toNat := by
  cases left <;> cases right <;> cases previous <;> decide

theorem ripple_equation (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    value (ripple previous left right).1 + value right + previous.toNat =
      value left + 2 ^ left.length * (ripple previous left right).2.toNat := by
  induction left generalizing previous right with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    subst right
    simp [ripple, BinaryRipple.ripple, value]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have tail := hypothesis (borrow bit other previous) rest (by simpa using sameLength)
      have head := digit_equation bit other previous
      simp only [ripple, BinaryRipple.ripple, value, List.length_cons, pow_succ]
      nlinarith

/-- The low digits and final borrow represent the exact signed difference. -/
theorem subtract_value (left right : List Bool) (sameLength : right.length = left.length) :
    (value (ripple false left right).1 : ℤ) -
        (2 : ℤ) ^ left.length * ((ripple false left right).2.toNat : ℤ) =
      (value left : ℤ) - value right := by
  have natural := ripple_equation false left right sameLength
  simp only [Bool.toNat_false, Nat.add_zero] at natural
  have signed : (value (ripple false left right).1 : ℤ) + value right =
      (value left : ℤ) + (2 : ℤ) ^ left.length * ((ripple false left right).2.toNat : ℤ) := by
    exact_mod_cast natural
  omega

/-- The final borrow is also an unsigned comparison result. -/
theorem underflow_iff (left right : List Bool) (sameLength : right.length = left.length) :
    (ripple false left right).2 = true ↔ value left < value right := by
  have equation := ripple_equation false left right sameLength
  have bound := Binary.value_lt_pow_length (ripple false left right).1
  rw [BinaryRipple.ripple_length digit borrow false left right sameLength] at bound
  cases finalBorrow : (ripple false left right).2 <;> simp [finalBorrow] at equation ⊢ <;> omega

/-- Without underflow the low digits are ordinary natural subtraction. -/
theorem difference_of_no_borrow (left right : List Bool) (sameLength : right.length = left.length)
    (nonnegative : value right ≤ value left) :
    value (ripple false left right).1 = value left - value right := by
  have noBorrow : (ripple false left right).2 = false := by
    have notTrue : (ripple false left right).2 ≠ true := by
      intro underflow
      have less := (underflow_iff left right sameLength).mp underflow
      omega
    exact Bool.eq_false_iff.mpr notTrue
  have equation := ripple_equation false left right sameLength
  simp only [noBorrow, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at equation
  omega

@[simp] theorem subtract_length (left right : List Bool) (sameLength : right.length = left.length) :
    (subtract left right).length = left.length + 1 := by
  simp [subtract, BinaryRipple.output, BinaryRipple.ripple_length digit borrow false left right sameLength]

/-- Linear cost, preserved operands and neighbors, and restored heads. -/
theorem steps (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps machine (2 * left.length + 3)
      (.inl false, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond)
        (3 :: leftOutput) (old ++ 0 :: tailOutput))
      (.inr 1, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond)
        (3 :: leftOutput) (word (subtract left right) ++ tailOutput)) :=
  BinaryRipple.steps digit borrow left right sameLength old oldLength
    leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput

/-- Mathematical signed subtraction on equally padded unsigned operands.
Scratch contents are existential; the final borrow is an explicit output bit. -/
theorem contract :
    Computes machine (.inl false) (.inr 1)
      (fun _sizes : Unit → ℕ => fun (operands : List Bool × List Bool) tapes => ∃ old,
        old.length = operands.1.length ∧ tapes =
          frame [3] (word operands.1 ++ [0]) [3] (word operands.2 ++ [0]) [3] (old ++ [0, 0]))
      (fun sizes => fun (result : ℤ) tapes => ∃ left right bits finalBorrow,
        (value bits : ℤ) - (2 : ℤ) ^ bits.length * (finalBorrow.toNat : ℤ) = result ∧
        bits.length ≤ sizes () ∧ tapes =
          frame [3] (word left ++ [0]) [3] (word right ++ [0]) [3] (word (bits ++ [finalBorrow]) ++ [0]))
      (fun sizes operands => operands.2.length = operands.1.length ∧ operands.1.length ≤ sizes ())
      (fun _ operands => (value operands.1 : ℤ) - value operands.2) := by
  refine ⟨by intro symbols; rfl, 2 * MvPolynomial.X () + 3, ?_⟩
  intro sizes operands initial valid represented
  obtain ⟨old, oldLength, rfl⟩ := represented
  refine ⟨_, _, ?_, steps operands.1 operands.2 valid.1 old oldLength [] [] [] [] [] [0],
    operands.1, operands.2, (ripple false operands.1 operands.2).1,
    (ripple false operands.1 operands.2).2, ?_, ?_, rfl⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · rw [BinaryRipple.ripple_length digit borrow false operands.1 operands.2 valid.1]
    exact subtract_value operands.1 operands.2 valid.1
  · simpa only [BinaryRipple.ripple_length digit borrow false operands.1 operands.2 valid.1] using valid.2

end Polytime2.BinarySubtraction
