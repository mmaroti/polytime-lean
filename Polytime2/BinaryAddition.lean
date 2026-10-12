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

import Polytime2.Contracts
import Polytime2.Binary
import Polytime2.BinaryRipple

/-! # Runtime-width binary addition

Two equally padded little-endian operands are preserved on tapes 0 and 1.
Tape 2 receives the sum, including the final carry digit. All heads return to
just after their left boundaries. The carry is finite controller memory; the
common operand capacity is runtime data, never a controller parameter.
-/

namespace Polytime2.BinaryAddition

open MultiTape
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 3 => Symbol
abbrev State := Sum Bool (Fin 2)

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

def frame (leftFirst rightFirst leftSecond rightSecond leftOutput rightOutput : List Symbol) :
    Tapes Alphabet := fun name =>
  if name = 0 then Turing.Tape.mk' (Turing.ListBlank.mk leftFirst) (Turing.ListBlank.mk rightFirst)
  else if name = 1 then Turing.Tape.mk' (Turing.ListBlank.mk leftSecond) (Turing.ListBlank.mk rightSecond)
  else Turing.Tape.mk' (Turing.ListBlank.mk leftOutput) (Turing.ListBlank.mk rightOutput)

def machine : Machine Alphabet State
  | .inl previous, symbols =>
    if symbols 0 = 0 then
      some (.inr 0, fun name => (if name = 2 then data previous else symbols name, none))
    else
      let left := symbols 0 == 2
      let right := symbols 1 == 2
      some (.inl (carry left right previous),
        fun name => (if name = 2 then data (digit left right previous) else symbols name, some .right))
  | .inr position, symbols =>
    if position = 0 then
      if symbols 0 = 3 then some (.inr 1, fun name => (symbols name, some .right))
      else some (.inr 0, fun name => (symbols name, some .left))
    else none

/-- Linear tape time, preserved operands and neighbors, and restored heads. -/
theorem steps (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps machine (2 * left.length + 3)
      (.inl false, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond)
        (3 :: leftOutput) (old ++ 0 :: tailOutput))
      (.inr 1, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond)
        (3 :: leftOutput) (word (add left right) ++ tailOutput)) := by
  exact BinaryRipple.steps digit carry left right sameLength old oldLength
    leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput

/-- Runtime digit capacity and numeric addition, with irrelevant output scratch
hidden by the input representation. The machine is the same for every capacity. -/
theorem contract :
    Computes machine (.inl false) (.inr 1)
      (fun _sizes : Unit → ℕ => fun (operands : List Bool × List Bool) tapes => ∃ old,
        old.length = operands.1.length ∧ tapes =
          frame [3] (word operands.1 ++ [0]) [3] (word operands.2 ++ [0]) [3] (old ++ [0, 0]))
      (fun sizes => fun result tapes => ∃ left right resultBits,
        value resultBits = result ∧ resultBits.length ≤ sizes () + 1 ∧ tapes =
          frame [3] (word left ++ [0]) [3] (word right ++ [0]) [3] (word resultBits ++ [0]))
      (fun sizes operands => operands.2.length = operands.1.length ∧ operands.1.length ≤ sizes ())
      (fun _ operands => value operands.1 + value operands.2) := by
  refine ⟨by intro symbols; rfl, 2 * MvPolynomial.X () + 3, ?_⟩
  intro sizes operands initial valid represented
  obtain ⟨old, oldLength, rfl⟩ := represented
  refine ⟨_, _, ?_, steps operands.1 operands.2 valid.1 old oldLength [] [] [] [] [] [0],
    operands.1, operands.2, add operands.1 operands.2,
    add_value operands.1 operands.2 valid.1, ?_, rfl⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · rw [add_length operands.1 operands.2 valid.1]
    omega

end Polytime2.BinaryAddition
