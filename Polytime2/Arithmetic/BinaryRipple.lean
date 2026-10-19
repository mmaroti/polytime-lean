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

import Polytime2.Primitives.ScanReturn
import Polytime2.Machine.CallingConvention
import Polytime2.Arithmetic.RippleMath

/-! # Marker-free carry and borrow scans

Both operands are immutable, fixed-width binary words. The separate output
has one additional bit, which is overwritten with the final carry or borrow.
The source's surrounding blanks determine traversal and head restoration.
-/

namespace Polytime2.StandardBinaryRipple

open MultiTape
open Binary (Symbol data word)

abbrev Alphabet := BinaryRipple.Alphabet
abbrev State := BinaryRipple.State
abbrev ripple := BinaryRipple.ripple
abbrev output := BinaryRipple.output
abbrev frame := BinaryRipple.frame

variable (digit carry : Bool → Bool → Bool → Bool)

def machine : Machine Alphabet State
  | .inl previous, symbols =>
    if symbols 0 = 0 then
      some (.inr 0, fun name =>
        (if name = 2 then data previous else symbols name, some .left))
    else
      let left := symbols 0 == 2
      let right := symbols 1 == 2
      some (.inl (carry left right previous),
        fun name => (if name = 2 then data (digit left right previous)
          else symbols name, some .right))
  | .inr position, symbols =>
    if position = 0 then
      if symbols 0 = 0 then some (.inr 1, fun name => (symbols name, some .right))
      else some (.inr 0, fun name => (symbols name, some .left))
    else none

private theorem forward (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) (old : List Symbol)
    (oldLength : old.length = left.length)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps (machine digit carry) left.length
      (.inl previous, frame leftFirst (word left ++ tailFirst)
        leftSecond (word right ++ tailSecond) leftOutput (old ++ tailOutput))
      (.inl (ripple digit carry previous left right).2,
        frame ((word left).reverse ++ leftFirst) tailFirst
          ((word right).reverse ++ leftSecond) tailSecond
          ((word (ripple digit carry previous left right).1).reverse ++ leftOutput) tailOutput) := by
  induction left generalizing previous right old leftFirst leftSecond leftOutput with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    have oldEmpty : old = [] := List.eq_nil_of_length_eq_zero oldLength
    subst right; subst old
    simpa [ripple, BinaryRipple.ripple, word] using Steps.zero (machine := (machine digit carry))
      (.inl previous, frame leftFirst tailFirst leftSecond tailSecond leftOutput tailOutput)
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      cases old with
      | nil => simp at oldLength
      | cons previousOutput old =>
        have first : step (machine digit carry)
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
          simp only [step, machine, MultiTape.read, frame, BinaryRipple.frame, word, List.map_cons, List.cons_append,
            Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank,
            ↓reduceIte, oneNotZero, leftDigit, rightDigit, Option.map_some]
          congr 2
          funext name
          fin_cases name <;>
            simp [act, BinaryRipple.frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
        have restTrace := hypothesis (carry bit other previous) rest (by simpa using sameLength)
          old (by simpa using oldLength) (data bit :: leftFirst) (data other :: leftSecond)
          (data (digit bit other previous) :: leftOutput)
        simpa [ripple, BinaryRipple.ripple, word, List.reverse_cons, List.append_assoc] using Steps.next first restTrace

/-- Exact linear cost for an arbitrary old output, including its carry cell. -/
theorem steps (previous : Bool) (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length) (oldCarry : Symbol)
    (leftFirst leftSecond leftOutput tailFirst tailSecond tailOutput : List Symbol) :
    Steps (machine digit carry) (2 * left.length + 2)
      (.inl previous, frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
        (0 :: leftSecond) (word right ++ 0 :: tailSecond)
        (0 :: leftOutput) (old ++ oldCarry :: tailOutput))
      (.inr 1, frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
        (0 :: leftSecond) (word right ++ 0 :: tailSecond)
        (0 :: leftOutput) (word ((ripple digit carry previous left right).1 ++
          [(ripple digit carry previous left right).2]) ++ tailOutput)) := by
  let low := (ripple digit carry previous left right).1
  let finalCarry := (ripple digit carry previous left right).2
  let atEnd := frame ((word left).reverse ++ 0 :: leftFirst) (0 :: tailFirst)
    ((word right).reverse ++ 0 :: leftSecond) (0 :: tailSecond)
    ((word low).reverse ++ 0 :: leftOutput) (oldCarry :: tailOutput)
  let prepared := frame ((word left).reverse ++ 0 :: leftFirst) (0 :: tailFirst)
    ((word right).reverse ++ 0 :: leftSecond) (0 :: tailSecond)
    ((word low).reverse ++ 0 :: leftOutput) (data finalCarry :: tailOutput)
  have lowLength : low.length = left.length :=
    BinaryRipple.ripple_length digit carry previous left right sameLength
  have scanned := forward digit carry previous left right sameLength old oldLength
    (0 :: leftFirst) (0 :: leftSecond) (0 :: leftOutput)
    (0 :: tailFirst) (0 :: tailSecond) (oldCarry :: tailOutput)
  have boundary : step (machine digit carry) (.inl finalCarry, atEnd) =
      some ((.inr 0), ScanReturn.move (fun _ : Fin 3 => true) .left prepared) := by
    simp only [step, machine, MultiTape.read, atEnd, frame, BinaryRipple.frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    fin_cases name <;> simp [act, prepared, frame, BinaryRipple.frame, ScanReturn.move, Turing.Tape.write_mk',
      Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have returned := ScanReturn.from_end (machine digit carry) (.inl finalCarry)
    (.inr 0) (.inr 1) 0 (fun _ : Fin 3 => true) rfl
    (by intro symbols nonblank; simp [machine, nonblank])
    (fun symbols name => (symbols name, some .right))
    (by intro symbols blank; simp [machine, blank]) left.reverse leftFirst tailFirst atEnd prepared boundary
    (by simp [prepared, frame, BinaryRipple.frame, word, List.map_reverse])
  have restored : Steps (machine digit carry) (left.length + 2) (.inl finalCarry, atEnd)
      ((.inr 1), frame (0 :: leftFirst) (word left ++ 0 :: tailFirst)
        (0 :: leftSecond) (word right ++ 0 :: tailSecond)
        (0 :: leftOutput) (word low ++ data finalCarry :: tailOutput)) := by
    simp only [List.length_reverse] at returned
    convert returned using 1
    congr 1
    funext name
    fin_cases name <;> simp only [act, MultiTape.read, Turing.Tape.write_self, ScanReturn.move_iterate,
      prepared, frame, BinaryRipple.frame]
    · simpa [word, List.map_reverse, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word left).reverse) leftFirst (0 :: tailFirst)).symm
    · simpa [word, List.map_reverse, sameLength, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word right).reverse) leftSecond (0 :: tailSecond)).symm
    · simpa [word, List.map_reverse, lowLength, Turing.Tape.write_self] using
        (ScanReturn.restore_tape ((word low).reverse) leftOutput (data finalCarry :: tailOutput)).symm
  simpa [low, finalCarry, word, List.map_append, Nat.mul_add, two_mul, Nat.add_assoc] using scanned.trans restored

open CallingConvention

/-- Only the separate result tape is writable. -/
def readOnly (name : Fin 3) : Bool := name != 2

/-- The carry cell is part of the output's reserved region. -/
def width (operandWidth : ℕ) (name : Fin 3) : ℕ :=
  if name = 2 then operandWidth + 1 else operandWidth

private def invariant (operandWidth : ℕ) (position : Fin 3 → ℤ) (state : State)
    (tapes : Tapes Alphabet) : Prop :=
  (∀ name, position name = position 0) ∧
    (∀ index : ℤ, (tapes 0).nth (index - position 0) = 0 ↔
      index < 0 ∨ (operandWidth : ℤ) ≤ index) ∧
    (match state with
     | .inl _ => 0 ≤ position 0 ∧ position 0 ≤ operandWidth
     | .inr phase => if phase = 0 then -1 ≤ position 0 ∧ position 0 < operandWidth
                    else position 0 = 0)

private theorem safe (operandWidth : ℕ) (position : Fin 3 → ℤ) (state : State)
    (tapes : Tapes Alphabet) (nextState : State) (actions : Actions Alphabet)
    (valid : invariant operandWidth position state tapes)
    (instruction : machine digit carry state (read tapes) = some (nextState, actions)) :
    Allowed (width operandWidth) readOnly position (read tapes) actions ∧
      invariant operandWidth (fun name => position name + displacement (actions name).2)
        nextState (act actions tapes) := by
  obtain ⟨synchronized, shape, bounds⟩ := valid
  have atHead := shape (position 0)
  simp only [sub_self, Turing.Tape.nth_zero] at atHead
  have preserveShape (source : (actions 0).1 = (tapes 0).head) :
      ∀ index : ℤ,
        (act actions tapes 0).nth
          (index - (position 0 + displacement (actions 0).2)) = 0 ↔
        index < 0 ∨ (operandWidth : ℤ) ≤ index := by
    intro index
    rw [action_nth]
    by_cases equal : index = position 0
    · subst index
      simpa [source] using atHead
    · simpa [equal] using shape index
  cases state with
  | inl previous =>
    by_cases blank : (tapes 0).head = 0
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      refine ⟨?_, ?_⟩
      · intro name premise
        by_cases output : name = 2
        · subst name
          have outside := atHead.mp blank
          simp only [readOnly, bne_self_eq_false, Bool.false_eq_true, false_or,
            width, ↓reduceIte] at premise
          rw [synchronized 2] at premise
          omega
        · simp [output, MultiTape.read]
      · refine ⟨?_, preserveShape (by simp), ?_⟩
        · intro name
          simpa [displacement] using synchronized name
        · simp only [displacement, ↓reduceIte]
          have outside := atHead.mp blank
          omega
    · simp only [machine, MultiTape.read, blank, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      have inside : ¬ (position 0 < 0 ∨ (operandWidth : ℤ) ≤ position 0) := by
        exact fun outside => blank (atHead.mpr outside)
      refine ⟨?_, ?_⟩
      · intro name premise
        by_cases output : name = 2
        · subst name
          simp only [readOnly, bne_self_eq_false, Bool.false_eq_true, false_or,
            width, ↓reduceIte] at premise
          rw [synchronized 2] at premise
          omega
        · simp [output, MultiTape.read]
      · refine ⟨?_, preserveShape (by simp), ?_⟩
        · intro name
          simpa [displacement] using synchronized name
        · simp only [displacement]
          omega
  | inr phase =>
    fin_cases phase
    · by_cases blank : (tapes 0).head = 0
      · simp only [machine, MultiTape.read, blank, ↓reduceIte] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        refine ⟨(by intro name premise; rfl), ?_⟩
        refine ⟨?_, preserveShape rfl, ?_⟩
        · intro name
          simpa [displacement] using synchronized name
        · have outside := atHead.mp blank
          norm_num [displacement] at bounds ⊢
          omega
      · simp only [machine, MultiTape.read, blank, ↓reduceIte] at instruction
        obtain ⟨rfl, rfl⟩ := instruction
        have inside : ¬ (position 0 < 0 ∨ (operandWidth : ℤ) ≤ position 0) := by
          exact fun outside => blank (atHead.mpr outside)
        refine ⟨(by intro name premise; rfl), ?_⟩
        refine ⟨?_, preserveShape rfl, ?_⟩
        · intro name
          simpa [displacement] using synchronized name
        · norm_num [displacement] at bounds ⊢
          omega
    · simp [machine] at instruction

/-- Both inputs and every surrounding blank are preserved at every step;
the complete output, including the carry bit, is overwritten. -/
theorem runs (previous : Bool) (left right : List Bool) (sameLength : right.length = left.length)
    (old : List Symbol) (oldLength : old.length = left.length) (oldCarry : Symbol) :
    Runs (width left.length) readOnly (machine digit carry) (2 * left.length + 2)
      (.inl previous) (fun _ => 0)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [oldCarry]))
      (.inr 1) (fun _ => 0)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
        (word ((ripple digit carry previous left right).1 ++
          [(ripple digit carry previous left right).2]))) := by
  have initial : invariant left.length (fun _ => 0) (.inl previous)
      (frame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [oldCarry])) := by
    refine ⟨(by intro name; rfl), ?_, ?_⟩
    · intro index
      simpa only [sub_zero, frame, BinaryRipple.frame, ↓reduceIte] using
        word_nth_blank_iff left index
    · simp
  obtain ⟨finalPosition, trace, finalValid⟩ := Runs.of_steps_invariant (invariant left.length)
    (safe digit carry left.length)
    (steps digit carry previous left right sameLength old oldLength oldCarry [] [] [] [] [] [])
    (fun _ => 0) initial
  have zero : finalPosition = fun _ => 0 := by
    obtain ⟨synchronized, shape, bounds⟩ := finalValid
    have atZero : finalPosition 0 = 0 := by simpa using bounds
    funext name
    exact (synchronized name).trans atZero
  simpa only [zero, List.append_nil] using trace

end Polytime2.StandardBinaryRipple
