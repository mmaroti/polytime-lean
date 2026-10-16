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

import Polytime2.BinaryRipple

import Polytime2.StandardBinaryRipple
import Polytime2.StandardBinaryArithmetic

/-! # Runtime-width binary subtraction

A finite borrow bit drives the shared ripple scanner. The output consists of
capacity-many difference digits followed by the final borrow. Together these
are the exact signed difference in two's complement, with no overflow.
-/

namespace Polytime2.BinarySubtraction

open MultiTape
open Binary (Symbol word value)

abbrev RippleAlphabet := BinaryRipple.Alphabet
abbrev RippleState := BinaryRipple.State

def digit (left right previous : Bool) : Bool := (left != right) != previous

def borrow (left right previous : Bool) : Bool :=
  (!left && (right || previous)) || (right && previous)

abbrev ripple := BinaryRipple.ripple digit borrow
abbrev subtract := BinaryRipple.output digit borrow
abbrev rippleFrame := BinaryRipple.frame

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

/-- The immutable-input implementation needs neither boundary markers nor
prepared output contents. -/
abbrev rippleMachine := StandardBinaryRipple.machine digit borrow

/-- The standard implementation writes every result bit and restores every
head, while preserving both operands and every cell outside their regions. -/
theorem runs (left right : List Bool)
    (sameLength : right.length = left.length) (old : List Symbol)
    (oldLength : old.length = left.length) (oldCarry : Symbol) :
    CallingConvention.Runs (StandardBinaryRipple.width left.length)
      StandardBinaryRipple.readOnly rippleMachine (2 * left.length + 2)
      (.inl false) (fun _ => 0)
      (rippleFrame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [oldCarry]))
      (.inr 1) (fun _ => 0)
      (rippleFrame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (word (subtract left right))) := by
  exact StandardBinaryRipple.runs digit borrow false left right sameLength old oldLength oldCarry

/-- Standard four-tape interface: immutable operands, low difference, and borrow. -/
noncomputable abbrev domains := StandardBinaryArithmetic.domains
abbrev argumentReadOnly := StandardBinaryArithmetic.argumentReadOnly
abbrev sizeTapes := StandardBinaryArithmetic.sizeTapes

noncomputable def algorithm :
    Machine (CallingConvention.Alphabet (Sum Unit (Fin 4))) (Sum StandardBinaryArithmetic.State Unit) :=
  StandardBinaryArithmetic.algorithm digit borrow

def entry := StandardBinaryArithmetic.entry false
def exit := StandardBinaryArithmetic.exit

/-- The standard interface returns the low difference and final borrow. -/
theorem contract :
    CallingConvention.Realizes domains argumentReadOnly sizeTapes StandardBinaryArithmetic.outputTapes algorithm entry exit
      (fun _ _ => True)
      (fun assignment input output =>
        (output false : Fin (2 ^ assignment ())).val =
            value (ripple false
              (List.ofFn (fun index : Fin (assignment ()) =>
                (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
              (List.ofFn (fun index : Fin (assignment ()) =>
                (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).1 ∧
          output true =
            (ripple false
              (List.ofFn (fun index : Fin (assignment ()) =>
                (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val))
              (List.ofFn (fun index : Fin (assignment ()) =>
                (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val))).2) := by
  exact StandardBinaryArithmetic.contract digit borrow false

/-- Loop guards can use the borrow output directly as unsigned comparison;
the low difference remains a valid fixed-width scratch result. -/
theorem comparison_contract :
    CallingConvention.Realizes domains argumentReadOnly sizeTapes StandardBinaryArithmetic.outputTapes algorithm entry exit
      (fun _ _ => True)
      (fun assignment input output => output true =
        decide ((input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val <
          (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val)) := by
  obtain ⟨sizeReadOnly, outputsWritable, halts, bound, execute⟩ := contract
  refine ⟨sizeReadOnly, outputsWritable, halts, bound, ?_⟩
  intro assignment input initial valid represented headers
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute assignment input initial valid represented headers
  refine ⟨ticks, output, final, cost, trace, ?_, canonical⟩
  apply Eq.trans correct.2
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  let left := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  have leftValue : value left = (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 0, rfl⟩))
  have rightValue : value right = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  have compared := underflow_iff left right (by simp [left, right])
  rw [leftValue, rightValue] at compared
  exact compared

end Polytime2.BinarySubtraction
