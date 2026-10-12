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
import Polytime2.BinaryRipple
import Polytime2.Copy

/-! # In-place binary arithmetic with a retained carry or borrow

The first tape is updated and the second operand is preserved. Both heads and
neighboring regions are restored. The final carry or borrow remains in finite
controller memory, allowing a caller to branch without another tape scan.
-/

namespace Polytime2.BinaryInPlace

open MultiTape
open Binary (Symbol data word)
open Copy (frame)

abbrev Alphabet := fun _ : Bool => Symbol
abbrev State := Sum Bool (Bool × Bool)

variable (digit carry : Bool → Bool → Bool → Bool)

def machine : Machine Alphabet State
  | .inl previous, symbols =>
    if symbols false = 0 then some (.inr (previous, false), stationary symbols)
    else
      let left := symbols false == 2
      let right := symbols true == 2
      some (.inl (carry left right previous), fun name =>
        (if name then symbols true else data (digit left right previous), some .right))
  | .inr (previous, finished), symbols =>
    if finished then none
    else if symbols false = 3 then
      some (.inr (previous, true), fun name => (symbols name, some .right))
    else some (.inr (previous, false), fun name => (symbols name, some .left))

private theorem forward (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length)
    (leftFirst leftSecond tailFirst tailSecond : List Symbol) :
    Steps (machine digit carry) left.length
      (.inl previous, frame leftFirst (word left ++ tailFirst) leftSecond (word right ++ tailSecond))
      (.inl (BinaryRipple.ripple digit carry previous left right).2,
        frame ((word (BinaryRipple.ripple digit carry previous left right).1).reverse ++ leftFirst) tailFirst
          ((word right).reverse ++ leftSecond) tailSecond) := by
  induction left generalizing previous right leftFirst leftSecond with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    subst right
    simpa [BinaryRipple.ripple, word] using Steps.zero (machine := machine digit carry)
      (.inl previous, frame leftFirst tailFirst leftSecond tailSecond)
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have first : step (machine digit carry)
          (.inl previous, frame leftFirst (word (bit :: bits) ++ tailFirst)
            leftSecond (word (other :: rest) ++ tailSecond)) =
          some (.inl (carry bit other previous),
            frame (data (digit bit other previous) :: leftFirst) (word bits ++ tailFirst)
              (data other :: leftSecond) (word rest ++ tailSecond)) := by
        have nonblank : data bit ≠ 0 := by cases bit <;> decide
        have leftDigit : (data bit == 2) = bit := by cases bit <;> decide
        have rightDigit : (data other == 2) = other := by cases other <;> decide
        simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank, ↓reduceIte,
          leftDigit, rightDigit, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have restTrace := hypothesis (carry bit other previous) rest (by simpa using sameLength)
        (data (digit bit other previous) :: leftFirst) (data other :: leftSecond)
      simpa [BinaryRipple.ripple, word, List.reverse_cons, List.append_assoc] using Steps.next first restTrace

private theorem rewind (memory : Bool) (left right : List Bool)
    (sameLength : right.length = left.length)
    (currentFirst currentSecond : Symbol) (nonboundary : currentFirst ≠ 3)
    (leftFirst leftSecond tailFirst tailSecond : List Symbol) :
    Steps (machine digit carry) (left.length + 2)
      (.inr (memory, false), frame (word left ++ 3 :: leftFirst) (currentFirst :: tailFirst)
        (word right ++ 3 :: leftSecond) (currentSecond :: tailSecond))
      (.inr (memory, true), frame (3 :: leftFirst) ((word left).reverse ++ currentFirst :: tailFirst)
        (3 :: leftSecond) ((word right).reverse ++ currentSecond :: tailSecond)) := by
  induction left generalizing right currentFirst currentSecond tailFirst tailSecond with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    subst right
    have first : step (machine digit carry)
        (.inr (memory, false), frame (3 :: leftFirst) (currentFirst :: tailFirst)
          (3 :: leftSecond) (currentSecond :: tailSecond)) =
        some (.inr (memory, false), frame leftFirst (3 :: currentFirst :: tailFirst)
          leftSecond (3 :: currentSecond :: tailSecond)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, nonboundary, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine digit carry)
        (.inr (memory, false), frame leftFirst (3 :: currentFirst :: tailFirst)
          leftSecond (3 :: currentSecond :: tailSecond)) =
        some (.inr (memory, true), frame (3 :: leftFirst) (currentFirst :: tailFirst)
          (3 :: leftSecond) (currentSecond :: tailSecond)) := by
      simp only [step, machine, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Bool.false_eq_true, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have first : step (machine digit carry)
          (.inr (memory, false), frame (word (bit :: bits) ++ 3 :: leftFirst) (currentFirst :: tailFirst)
            (word (other :: rest) ++ 3 :: leftSecond) (currentSecond :: tailSecond)) =
          some (.inr (memory, false), frame (word bits ++ 3 :: leftFirst) (data bit :: currentFirst :: tailFirst)
            (word rest ++ 3 :: leftSecond) (data other :: currentSecond :: tailSecond)) := by
        simp only [step, machine, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonboundary,
          ↓reduceIte, Bool.false_eq_true, Option.map_some]
        congr 2
        funext name
        cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have dataNotBoundary : data bit ≠ 3 := by cases bit <;> decide
      have restTrace := hypothesis rest (by simpa using sameLength) (data bit) (data other) dataNotBoundary
        (currentFirst :: tailFirst) (currentSecond :: tailSecond)
      simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first restTrace

/-- Linear arithmetic, with the final carry/borrow retained at a halting exit. -/
theorem steps (previous : Bool) (left right : List Bool) (sameLength : right.length = left.length)
    (leftFirst leftSecond tailFirst tailSecond : List Symbol) :
    Steps (machine digit carry) (2 * left.length + 3)
      (.inl previous, frame (3 :: leftFirst) (word left ++ 0 :: tailFirst)
        (3 :: leftSecond) (word right ++ 0 :: tailSecond))
      (.inr ((BinaryRipple.ripple digit carry previous left right).2, true),
        frame (3 :: leftFirst) (word (BinaryRipple.ripple digit carry previous left right).1 ++ 0 :: tailFirst)
          (3 :: leftSecond) (word right ++ 0 :: tailSecond)) := by
  have scanned := forward digit carry previous left right sameLength (3 :: leftFirst) (3 :: leftSecond)
    (0 :: tailFirst) (0 :: tailSecond)
  have finish : step (machine digit carry)
      (.inl (BinaryRipple.ripple digit carry previous left right).2,
        frame ((word (BinaryRipple.ripple digit carry previous left right).1).reverse ++ 3 :: leftFirst) (0 :: tailFirst)
          ((word right).reverse ++ 3 :: leftSecond) (0 :: tailSecond)) =
      some (.inr ((BinaryRipple.ripple digit carry previous left right).2, false),
        frame ((word (BinaryRipple.ripple digit carry previous left right).1).reverse ++ 3 :: leftFirst) (0 :: tailFirst)
          ((word right).reverse ++ 3 :: leftSecond) (0 :: tailSecond)) := by
    simp [step, machine, MultiTape.read, frame]
  have restored := rewind digit carry (BinaryRipple.ripple digit carry previous left right).2
    (BinaryRipple.ripple digit carry previous left right).1.reverse right.reverse
    (by simp [BinaryRipple.ripple_length digit carry previous left right sameLength, sameLength])
    0 0 (by decide) leftFirst leftSecond tailFirst tailSecond
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse,
    BinaryRipple.ripple_length digit carry previous left right sameLength] at scanned finish restored ⊢
  convert scanned.trans (Steps.next finish restored) using 1
  omega

end Polytime2.BinaryInPlace
