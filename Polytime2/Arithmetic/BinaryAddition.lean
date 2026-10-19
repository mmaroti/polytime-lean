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

import Polytime2.Encoding.Binary
import Polytime2.Arithmetic.RippleMath

import Polytime2.Arithmetic.BinaryRipple
import Polytime2.Arithmetic.BinaryArithmetic

/-! # Runtime-width binary addition

Two equally padded little-endian operands are preserved on tapes 0 and 1.
Tape 2 receives the sum, including the final carry digit. All heads return to
to the first data cell. The carry is finite controller memory; the
common operand capacity is runtime data, never a controller parameter.
-/

namespace Polytime2.BinaryAddition

open MultiTape
open Binary (Symbol data word value)

abbrev RippleAlphabet := fun _ : Fin 3 => Symbol
abbrev RippleState := Sum Bool (Fin 2)

def digit (left right carry : Bool) : Bool := (left != right) != carry

def carry (left right previous : Bool) : Bool :=
  (left && right) || (previous && (left || right))

abbrev ripple := BinaryRipple.ripple digit carry

def add (left right : List Bool) : List Bool :=
  (ripple false left right).1 ++ [(ripple false left right).2]

private theorem digit_equation (left right previous : Bool) :
    (digit left right previous).toNat + 2 * (carry left right previous).toNat =
      left.toNat + right.toNat + previous.toNat := by
  cases left <;> cases right <;> cases previous <;> decide

private theorem ripple_length (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    (ripple previous left right).1.length = left.length := by
  induction left generalizing previous right with
  | nil => simp [ripple, BinaryRipple.ripple]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest => simp [ripple, BinaryRipple.ripple, hypothesis _ rest (by simpa using sameLength)]

theorem ripple_value (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    value (ripple previous left right).1 +
        2 ^ left.length * (ripple previous left right).2.toNat =
      value left + value right + previous.toNat := by
  induction left generalizing previous right with
  | nil => have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
           subst right; simp [ripple, BinaryRipple.ripple, value]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have tail := hypothesis (carry bit other previous) rest (by simpa using sameLength)
      have head := digit_equation bit other previous
      simp only [ripple, BinaryRipple.ripple, value, List.length_cons, pow_succ]
      nlinarith

private theorem value_append (left right : List Bool) :
    value (left ++ right) = value left + 2 ^ left.length * value right := by
  induction left with
  | nil => simp [value]
  | cons bit bits hypothesis =>
    simp only [List.cons_append, value, List.length_cons, pow_succ, hypothesis]
    ring

@[simp] theorem add_length (left right : List Bool) (sameLength : right.length = left.length) :
    (add left right).length = left.length + 1 := by
  simp [add, ripple_length false left right sameLength]

/-- The extra carry digit makes this exact addition, with no truncation. -/
theorem add_value (left right : List Bool) (sameLength : right.length = left.length) :
    value (add left right) = value left + value right := by
  simpa [add, value_append, value, ripple_length false left right sameLength] using
    ripple_value false left right sameLength

def lowSum (left right : List Bool) : List Bool := (ripple false left right).1

theorem lowSum_length (left right : List Bool) (sameLength : right.length = left.length) :
    (lowSum left right).length = left.length := BinaryRipple.ripple_length _ _ _ _ _ sameLength

theorem lowSum_value (left right : List Bool) (sameLength : right.length = left.length)
    (capacity : value left + value right < 2 ^ left.length) :
    value (lowSum left right) = value left + value right ∧
      (ripple false left right).2 = false := by
  have equation := ripple_value false left right sameLength
  cases flag : (ripple false left right).2 with
  | false => simpa [lowSum, flag] using equation
  | true => simp only [flag, Bool.toNat_true, Nat.mul_one, Bool.toNat_false, Nat.add_zero] at equation; omega

def rippleFrame (leftFirst rightFirst leftSecond rightSecond leftOutput rightOutput : List Symbol) :
    Tapes RippleAlphabet := fun name =>
  if name = 0 then Turing.Tape.mk' (Turing.ListBlank.mk leftFirst) (Turing.ListBlank.mk rightFirst)
  else if name = 1 then Turing.Tape.mk' (Turing.ListBlank.mk leftSecond) (Turing.ListBlank.mk rightSecond)
  else Turing.Tape.mk' (Turing.ListBlank.mk leftOutput) (Turing.ListBlank.mk rightOutput)

/-- The immutable-input implementation needs neither boundary markers nor
prepared output contents. -/
abbrev rippleMachine := StandardBinaryRipple.machine digit carry

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
      (rippleFrame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (word (add left right))) := by
  exact StandardBinaryRipple.runs digit carry false left right sameLength old oldLength oldCarry

/-- Standard four-tape interface: immutable operands, low result, and carry. -/
noncomputable abbrev domains := StandardBinaryArithmetic.domains
abbrev argumentReadOnly := StandardBinaryArithmetic.argumentReadOnly (Parameter := Unit)
abbrev sizeTapes := StandardBinaryArithmetic.sizeTapes (Parameter := Unit)

noncomputable def algorithm :
    Machine (CallingConvention.Alphabet (Sum Unit (Fin 4))) (Sum StandardBinaryArithmetic.State Unit) :=
  StandardBinaryArithmetic.algorithm digit carry

def entry := StandardBinaryArithmetic.entry false
def exit := StandardBinaryArithmetic.exit

/-- The standard interface returns the ripple result and final carry. -/
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
  exact StandardBinaryArithmetic.contract digit carry false

end Polytime2.BinaryAddition
