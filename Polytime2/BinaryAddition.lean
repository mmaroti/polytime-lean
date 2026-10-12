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

def ripple : Bool → List Bool → List Bool → List Bool × Bool
  | previous, left :: ls, right :: rs =>
    let rest := ripple (carry left right previous) ls rs
    (digit left right previous :: rest.1, rest.2)
  | previous, _, _ => ([], previous)

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
  | nil => simp [ripple]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest => simp [ripple, hypothesis _ rest (by simpa using sameLength)]

private theorem ripple_value (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    value (ripple previous left right).1 +
        2 ^ left.length * (ripple previous left right).2.toNat =
      value left + value right + previous.toNat := by
  induction left generalizing previous right with
  | nil => have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
           subst right; simp [ripple, value]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have tail := hypothesis (carry bit other previous) rest (by simpa using sameLength)
      have head := digit_equation bit other previous
      simp only [ripple, value, List.length_cons, pow_succ]
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

private theorem forward (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) (old : List Symbol)
    (oldLength : old.length = left.length)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps machine left.length
      (.inl previous, frame leftFirst (word left ++ tailFirst)
        leftSecond (word right ++ tailSecond) leftOutput (old ++ tailOutput))
      (.inl (ripple previous left right).2,
        frame ((word left).reverse ++ leftFirst) tailFirst
          ((word right).reverse ++ leftSecond) tailSecond
          ((word (ripple previous left right).1).reverse ++ leftOutput) tailOutput) := by
  induction left generalizing previous right old leftFirst leftSecond leftOutput with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    have oldEmpty : old = [] := List.eq_nil_of_length_eq_zero oldLength
    subst right; subst old
    simpa [ripple, word] using Steps.zero (machine := machine)
      (.inl previous, frame leftFirst tailFirst leftSecond tailSecond leftOutput tailOutput)
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      cases old with
      | nil => simp at oldLength
      | cons previousOutput old =>
        have first : step machine
            (.inl previous, frame leftFirst (word (bit :: bits) ++ tailFirst)
              leftSecond (word (other :: rest) ++ tailSecond) leftOutput ((previousOutput :: old) ++ tailOutput)) =
            some (.inl (carry bit other previous),
              frame (data bit :: leftFirst) (word bits ++ tailFirst)
                (data other :: leftSecond) (word rest ++ tailSecond)
                (data (digit bit other previous) :: leftOutput) (old ++ tailOutput)) := by
          have nonblank : data bit ≠ 0 := by cases bit <;> decide
          have leftDigit : (data bit == 2) = bit := by cases bit <;> decide
          have rightDigit : (data other == 2) = other := by cases other <;> decide
          have oneNotZero : (1 : Fin 3) ≠ 0 := by decide
          simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
            Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank,
            ↓reduceIte, oneNotZero, leftDigit, rightDigit, Option.map_some]
          congr 2
          funext name
          fin_cases name <;>
            simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        have restTrace := hypothesis (carry bit other previous) rest (by simpa using sameLength)
          old (by simpa using oldLength) (data bit :: leftFirst) (data other :: leftSecond)
          (data (digit bit other previous) :: leftOutput)
        simpa [ripple, word, List.reverse_cons, List.append_assoc] using Steps.next first restTrace

private theorem return_heads (left right output : List Bool)
    (rightLength : right.length = left.length) (outputLength : output.length = left.length)
    (currentFirst currentSecond currentOutput : Symbol) (notBoundary : currentFirst ≠ 3)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps machine (left.length + 2)
      (.inr 0, frame (word left ++ 3 :: leftFirst) (currentFirst :: tailFirst)
        (word right ++ 3 :: leftSecond) (currentSecond :: tailSecond)
        (word output ++ 3 :: leftOutput) (currentOutput :: tailOutput))
      (.inr 1, frame (3 :: leftFirst) ((word left).reverse ++ currentFirst :: tailFirst)
        (3 :: leftSecond) ((word right).reverse ++ currentSecond :: tailSecond)
        (3 :: leftOutput) ((word output).reverse ++ currentOutput :: tailOutput)) := by
  induction left generalizing right output currentFirst currentSecond currentOutput
      tailFirst tailSecond tailOutput with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_of_length_eq_zero rightLength
    have outputEmpty : output = [] := List.eq_nil_of_length_eq_zero outputLength
    subst right; subst output
    have first : step machine
        (.inr 0, frame (3 :: leftFirst) (currentFirst :: tailFirst)
          (3 :: leftSecond) (currentSecond :: tailSecond) (3 :: leftOutput) (currentOutput :: tailOutput)) =
        some (.inr 0, frame leftFirst (3 :: currentFirst :: tailFirst)
          leftSecond (3 :: currentSecond :: tailSecond) leftOutput (3 :: currentOutput :: tailOutput)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      fin_cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        (.inr 0, frame leftFirst (3 :: currentFirst :: tailFirst)
          leftSecond (3 :: currentSecond :: tailSecond) leftOutput (3 :: currentOutput :: tailOutput)) =
        some (.inr 1, frame (3 :: leftFirst) (currentFirst :: tailFirst)
          (3 :: leftSecond) (currentSecond :: tailSecond) (3 :: leftOutput) (currentOutput :: tailOutput)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      fin_cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at rightLength
    | cons other rest =>
      cases output with
      | nil => simp at outputLength
      | cons result results =>
        have first : step machine
            (.inr 0, frame (word (bit :: bits) ++ 3 :: leftFirst) (currentFirst :: tailFirst)
              (word (other :: rest) ++ 3 :: leftSecond) (currentSecond :: tailSecond)
              (word (result :: results) ++ 3 :: leftOutput) (currentOutput :: tailOutput)) =
            some (.inr 0, frame (word bits ++ 3 :: leftFirst) (data bit :: currentFirst :: tailFirst)
              (word rest ++ 3 :: leftSecond) (data other :: currentSecond :: tailSecond)
              (word results ++ 3 :: leftOutput) (data result :: currentOutput :: tailOutput)) := by
          simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
            Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary,
            ↓reduceIte, Option.map_some]
          congr 2
          funext name
          fin_cases name <;>
            simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
        have dataNotBoundary : data bit ≠ 3 := by cases bit <;> decide
        have restTrace := hypothesis rest results (by simpa using rightLength)
          (by simpa using outputLength) (data bit) (data other) (data result) dataNotBoundary
          (currentFirst :: tailFirst) (currentSecond :: tailSecond) (currentOutput :: tailOutput)
        simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first restTrace

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
  have scanned := forward false left right sameLength old oldLength
    (3 :: leftFirst) (3 :: leftSecond) (3 :: leftOutput)
    (0 :: tailFirst) (0 :: tailSecond) (0 :: tailOutput)
  have finish : step machine
      (.inl (ripple false left right).2,
        frame ((word left).reverse ++ 3 :: leftFirst) (0 :: tailFirst)
          ((word right).reverse ++ 3 :: leftSecond) (0 :: tailSecond)
          ((word (ripple false left right).1).reverse ++ 3 :: leftOutput) (0 :: tailOutput)) =
      some (.inr 0, frame ((word left).reverse ++ 3 :: leftFirst) (0 :: tailFirst)
        ((word right).reverse ++ 3 :: leftSecond) (0 :: tailSecond)
        ((word (ripple false left right).1).reverse ++ 3 :: leftOutput)
        (data (ripple false left right).2 :: tailOutput)) := by
    simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    fin_cases name <;> simp [act, frame, Turing.Tape.write_mk']
  have restored := return_heads left.reverse right.reverse (ripple false left right).1.reverse
    (by simpa using sameLength) (by simp [ripple_length false left right sameLength])
    0 0 (data (ripple false left right).2) (by decide)
    leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse] at scanned restored finish ⊢
  convert scanned.trans (Steps.next finish restored) using 1 <;> first
    | omega
    | simp [add, List.map_append, List.append_assoc]

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
