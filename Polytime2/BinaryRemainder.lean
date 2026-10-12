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
import Polytime2.BinaryScan
import Polytime2.BinaryReduce
import Polytime2.Wiring

/-! # Binary long remainder

Digits are processed from high to low. Each iteration shifts one bit into a
fixed-width remainder and performs one restoring subtraction. The divisor
reserves a leading zero digit, preventing shift overflow.
-/

namespace Polytime2.BinaryRemainder

open MultiTape
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 3 => Symbol
abbrev State := Sum (Fin 4) (Sum (BinaryScan.State Bool) BinaryReduce.State)

def shifted (bit : Bool) (remainder : List Bool) : List Bool :=
  (BinaryScan.run BinaryScan.shift bit remainder).2

def finish (divisor : List Bool) : List Bool → List Bool → List Bool
  | [], remainder => remainder
  | bit :: bits, remainder => finish divisor bits (BinaryReduce.reduced (shifted bit remainder) divisor)

def prefixValue (bits : List Bool) (initial : ℕ) : ℕ :=
  bits.foldl (fun previous bit => bit.toNat + 2 * previous) initial

@[simp] theorem prefixValue_reverse (bits : List Bool) (initial : ℕ) :
    prefixValue bits.reverse initial = value bits + 2 ^ bits.length * initial := by
  induction bits with
  | nil => simp [prefixValue, value]
  | cons bit bits hypothesis =>
    simp only [prefixValue, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at hypothesis ⊢
    rw [hypothesis]
    simp only [value, List.length_cons, pow_succ]
    ring

private theorem prefixValue_mod (bits : List Bool) (initial divisor : ℕ) :
    prefixValue bits (initial % divisor) % divisor = prefixValue bits initial % divisor := by
  induction bits generalizing initial with
  | nil => simp [prefixValue]
  | cons bit bits hypothesis =>
    have next : (bit.toNat + 2 * (initial % divisor)) % divisor =
        (bit.toNat + 2 * initial) % divisor := by simp [Nat.add_mod, Nat.mul_mod]
    change prefixValue bits (bit.toNat + 2 * (initial % divisor)) % divisor =
      prefixValue bits (bit.toNat + 2 * initial) % divisor
    rw [← hypothesis (bit.toNat + 2 * (initial % divisor)), next, hypothesis]

private theorem shifted_fits (bit : Bool) (remainder divisor : List Bool)
    (bounded : value remainder < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ remainder.length) :
    bit.toNat + 2 * value remainder < 2 ^ remainder.length := by
  have bitBound : bit.toNat ≤ 1 := by cases bit <;> decide
  omega

@[simp] theorem finish_length (bits remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length) :
    (finish divisor bits remainder).length = remainder.length := by
  induction bits generalizing remainder with
  | nil => rfl
  | cons bit bits hypothesis =>
    have shiftedLength : (shifted bit remainder).length = remainder.length := BinaryScan.run_length _ _ _
    have nextLength := BinaryReduce.reduced_length (shifted bit remainder) divisor (by omega)
    rw [finish, hypothesis (BinaryReduce.reduced (shifted bit remainder) divisor) (by omega),
      nextLength, shiftedLength]

/-- The mathematical long-division loop computes the exact remainder. -/
theorem finish_value (bits remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length)
    (bounded : value remainder < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ remainder.length) :
    value (finish divisor bits remainder) = prefixValue bits (value remainder) % value divisor := by
  induction bits generalizing remainder with
  | nil => simpa [finish, prefixValue] using (Nat.mod_eq_of_lt bounded).symm
  | cons bit bits hypothesis =>
    have shiftedLength : (shifted bit remainder).length = remainder.length := BinaryScan.run_length _ _ _
    have shiftedValue : value (shifted bit remainder) = bit.toNat + 2 * value remainder :=
      (BinaryScan.shift_value bit remainder (shifted_fits bit remainder divisor bounded capacity)).1
    have bitBound : bit.toNat ≤ 1 := by cases bit <;> decide
    have small : value (shifted bit remainder) < 2 * value divisor := by omega
    have nextValue := BinaryReduce.reduced_value (shifted bit remainder) divisor (by omega) small
    have nextLength := BinaryReduce.reduced_length (shifted bit remainder) divisor (by omega)
    have positive : 0 < value divisor := by omega
    have nextBound : value (BinaryReduce.reduced (shifted bit remainder) divisor) < value divisor := by
      rw [nextValue]
      exact Nat.mod_lt _ positive
    rw [finish, hypothesis _ (by omega) nextBound (by simpa only [nextLength, shiftedLength] using capacity),
      nextValue, shiftedValue, prefixValue_mod]
    rfl

/-- Tape 0: dividend cursor; tape 1: divisor; tape 2: remainder. -/
def frame (sourceLeft sourceRight : List Symbol) (divisor remainder : List Bool) : Tapes Alphabet :=
  fun name => if name = 0 then Binary.tape sourceLeft sourceRight ()
    else if name = 1 then Binary.tape [3] (word divisor ++ [0]) ()
    else Binary.tape [3] (word remainder ++ [0]) ()

@[simp] private theorem word_reconstruct (bits : List Bool) :
    (bits.map data ++ [0]).headI :: (bits.map data ++ [0]).tail = bits.map data ++ [0] := by
  cases bits <;> rfl

def shiftWiring : Unit ↪ Fin 3 := oneTape 2

def reduceWiring : Bool ↪ Fin 3 where
  toFun name := if name then 1 else 2
  inj' := by intro first second equal; cases first <;> cases second <;> simp_all

noncomputable def shiftMachine : Machine Alphabet (BinaryScan.State Bool) :=
  wire shiftWiring (BinaryScan.machine BinaryScan.shift)

noncomputable def reduceMachine : Machine Alphabet BinaryReduce.State :=
  wire reduceWiring BinaryReduce.machine

/-- A runtime-width controller; the dividend cursor supplies the next high bit. -/
noncomputable def machine : Machine Alphabet State
  | .inl phase, symbols => match phase.val with
    | 0 => if symbols 0 = 0 then some (.inl 1, stationary symbols)
      else some (.inl 0, fun name => (symbols name, if name = 0 then some .right else none))
    | 1 => some (.inl 2, fun name => (symbols name, if name = 0 then some .left else none))
    | 2 => if symbols 0 = 3 then
        some (.inl 3, fun name => (symbols name, if name = 0 then some .right else none))
      else some (.inr (.inl (.inl (symbols 0 == 2))), stationary symbols)
    | _ => none
  | .inr (.inl state), symbols => match shiftMachine state symbols with
    | some (next, actions) => some (.inr (.inl next), actions)
    | none => some (.inr (.inr BinaryReduce.entry), stationary symbols)
  | .inr (.inr state), symbols => match reduceMachine state symbols with
    | some (next, actions) => some (.inr (.inr next), actions)
    | none => some (.inl 1, stationary symbols)

def entry : State := .inl 0
def exit : State := .inl 3

private theorem shift_steps (bit : Bool) (remainder divisor : List Bool)
    (sourceLeft sourceRight : List Symbol) :
    Steps shiftMachine (2 * remainder.length + 3)
      (.inl bit, frame sourceLeft sourceRight divisor remainder)
      (.inr ((BinaryScan.run BinaryScan.shift bit remainder).1, true),
        frame sourceLeft sourceRight divisor (shifted bit remainder)) := by
  apply wire_steps_of_eq shiftWiring _ (BinaryScan.steps BinaryScan.shift bit remainder [] [])
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name
    · rfl
    · rfl
    · exact False.elim (outside ⟨(), rfl⟩)

private theorem reduce_steps (remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length) (sourceLeft sourceRight : List Symbol) :
    ∃ ticks, ticks ≤ 4 * remainder.length + 8 ∧ Steps reduceMachine ticks
      (BinaryReduce.entry, frame sourceLeft sourceRight divisor remainder)
      (BinaryReduce.exit, frame sourceLeft sourceRight divisor (BinaryReduce.reduced remainder divisor)) := by
  obtain ⟨ticks, cost, trace⟩ := BinaryReduce.steps remainder divisor sameLength [] [] [] []
  refine ⟨ticks, cost, ?_⟩
  apply wire_steps_of_eq reduceWiring _ trace
  · intro name; cases name <;> rfl
  · intro name; cases name <;> rfl
  · intro name outside
    fin_cases name
    · rfl
    · exact False.elim (outside ⟨true, rfl⟩)
    · exact False.elim (outside ⟨false, rfl⟩)

private theorem forward_steps (bits : List Bool) (left right : List Symbol) (divisor remainder : List Bool) :
    Steps machine bits.length
      (.inl 0, frame left (word bits ++ right) divisor remainder)
      (.inl 0, frame ((word bits).reverse ++ left) right divisor remainder) := by
  induction bits generalizing left with
  | nil => simpa [word] using Steps.zero (machine := machine) (.inl 0, frame left right divisor remainder)
  | cons bit bits hypothesis =>
    have first : step machine (.inl 0, frame left (word (bit :: bits) ++ right) divisor remainder) =
        some (.inl 0, frame (data bit :: left) (word bits ++ right) divisor remainder) := by
      have nonblank : data bit ≠ 0 := by cases bit <;> decide
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Binary.tape, word,
        List.map_cons, List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
        List.headI_cons, nonblank, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      fin_cases name <;> simp [act, frame, Binary.tape, word, Turing.Tape.write_mk',
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word, List.reverse_cons, List.append_assoc] using
      Steps.next first (hypothesis (data bit :: left))

/-- Each loop iteration consumes one high-to-low dividend bit. Scratch-free
logical values determine the result; the physical cursor determines stopping. -/
private theorem loop_steps (bits processed remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length)
    (bounded : value remainder < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ remainder.length) :
    ∃ ticks, ticks ≤ bits.length * (6 * remainder.length + 15) + 2 ∧ Steps machine ticks
      (.inl 1, frame (word bits ++ [3]) (word processed ++ [0]) divisor remainder)
      (exit, frame [3] (word (bits.reverse ++ processed) ++ [0]) divisor (finish divisor bits remainder)) := by
  induction bits generalizing processed remainder with
  | nil =>
    have first : step machine
        (.inl 1, frame [3] (word processed ++ [0]) divisor remainder) =
        some (.inl 2, frame [] (3 :: word processed ++ [0]) divisor remainder) := by
      simp only [step, machine, Fin.val_one, Option.map_some]
      congr 2
      funext name
      fin_cases name <;> simp [act, MultiTape.read, frame, Binary.tape, word, Turing.Tape.write_mk',
        Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        (.inl 2, frame [] (3 :: word processed ++ [0]) divisor remainder) =
        some (exit, frame [3] (word processed ++ [0]) divisor remainder) := by
      simp only [step, machine, show (2 : Fin 4).val = 2 from rfl, MultiTape.read, frame, Binary.tape, List.cons_append, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      fin_cases name <;> simp [act, frame, Binary.tape, word, Turing.Tape.write_mk',
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    exact ⟨2, by simp, by simpa [word, finish] using Steps.next first (Steps.next second (.zero _))⟩
  | cons bit bits hypothesis =>
    have shiftedLength : (shifted bit remainder).length = remainder.length := BinaryScan.run_length _ _ _
    have nextLength := BinaryReduce.reduced_length (shifted bit remainder) divisor (by omega)
    have shiftedValue := (BinaryScan.shift_value bit remainder
      (shifted_fits bit remainder divisor bounded capacity)).1
    have bitBound : bit.toNat ≤ 1 := by cases bit <;> decide
    have small : value (shifted bit remainder) < 2 * value divisor := by
      change value (shifted bit remainder) = _ at shiftedValue
      omega
    have nextValue := BinaryReduce.reduced_value (shifted bit remainder) divisor (by omega) small
    have positive : 0 < value divisor := by omega
    have nextBound : value (BinaryReduce.reduced (shifted bit remainder) divisor) < value divisor := by
      rw [nextValue]; exact Nat.mod_lt _ positive
    have first : step machine
        (.inl 1, frame (word (bit :: bits) ++ [3]) (word processed ++ [0]) divisor remainder) =
        some (.inl 2, frame (word bits ++ [3]) (data bit :: word processed ++ [0]) divisor remainder) := by
      simp only [step, machine, Fin.val_one, Option.map_some]
      congr 2
      funext name
      fin_cases name <;> simp [act, MultiTape.read, frame, Binary.tape, word, Turing.Tape.write_mk',
        Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have launch : step machine
        (.inl 2, frame (word bits ++ [3]) (data bit :: word processed ++ [0]) divisor remainder) =
        some (.inr (.inl (.inl bit)),
          frame (word bits ++ [3]) (data bit :: word processed ++ [0]) divisor remainder) := by
      have notMarker : data bit ≠ 3 := by cases bit <;> decide
      have digit : (data bit == 2) = bit := by cases bit <;> decide
      simp [step, machine, MultiTape.read, frame, Binary.tape, notMarker, digit]
    have shiftedTrace := shift_steps bit remainder divisor (word bits ++ [3]) (data bit :: word processed ++ [0])
    have shiftedLift := shiftedTrace.rename (fun state => Sum.inr (Sum.inl state)) (target := machine)
      (by intro state symbols next actions transition; simp [machine, transition])
    have handover : step machine
        (.inr (.inl (.inr ((BinaryScan.run BinaryScan.shift bit remainder).1, true))),
          frame (word bits ++ [3]) (data bit :: word processed ++ [0]) divisor (shifted bit remainder)) =
        some (.inr (.inr BinaryReduce.entry),
          frame (word bits ++ [3]) (data bit :: word processed ++ [0]) divisor (shifted bit remainder)) := by
      simp [step, machine, shiftMachine, wire, BinaryScan.machine]
    obtain ⟨reduceTicks, reduceCost, reduceTrace⟩ := reduce_steps (shifted bit remainder) divisor (by omega)
      (word bits ++ [3]) (data bit :: word processed ++ [0])
    have reduceLift := reduceTrace.rename (fun state => Sum.inr (Sum.inr state)) (target := machine)
      (by intro state symbols next actions transition; simp [machine, transition])
    have restart : step machine
        (.inr (.inr BinaryReduce.exit), frame (word bits ++ [3]) (data bit :: word processed ++ [0])
          divisor (BinaryReduce.reduced (shifted bit remainder) divisor)) =
        some (.inl 1, frame (word bits ++ [3]) (data bit :: word processed ++ [0])
          divisor (BinaryReduce.reduced (shifted bit remainder) divisor)) := by
      simp [step, machine, reduceMachine, wire, BinaryReduce.machine, BinaryReduce.exit, withExit]
    obtain ⟨restTicks, restCost, restTrace⟩ := hypothesis (bit :: processed)
      (BinaryReduce.reduced (shifted bit remainder) divisor) (by omega) nextBound
      (by simpa only [nextLength, shiftedLength] using capacity)
    have trace := Steps.next first (Steps.next launch
      (shiftedLift.trans (Steps.next handover (reduceLift.trans (Steps.next restart restTrace)))))
    refine ⟨1 + (1 + (2 * remainder.length + 3 + (1 + (reduceTicks + (1 + restTicks))))), ?_, ?_⟩
    · rw [nextLength, shiftedLength] at restCost
      rw [shiftedLength] at reduceCost
      simp only [List.length_cons]
      nlinarith
    · simpa only [finish, word, List.reverse_cons, List.map_append, List.map_cons, List.append_assoc,
        List.singleton_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using trace

/-- Complete long remainder: fixed finite control, quadratic runtime, preserved
operands, restored heads, and a fixed-capacity remainder. -/
theorem steps (input divisor remainder : List Bool)
    (sameLength : divisor.length = remainder.length)
    (bounded : value remainder < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ remainder.length) :
    ∃ ticks, ticks ≤ input.length * (6 * remainder.length + 16) + 3 ∧ Steps machine ticks
      (entry, frame [3] (word input ++ [0]) divisor remainder)
      (exit, frame [3] (word input ++ [0]) divisor (finish divisor input.reverse remainder)) := by
  have scanned := forward_steps input [3] [0] divisor remainder
  have handover : step machine
      (.inl 0, frame ((word input).reverse ++ [3]) [0] divisor remainder) =
      some (.inl 1, frame ((word input).reverse ++ [3]) [0] divisor remainder) := by
    simp [step, machine, MultiTape.read, frame, Binary.tape]
  obtain ⟨loopTicks, loopCost, loopTrace⟩ := loop_steps input.reverse [] remainder divisor sameLength bounded capacity
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse, List.append_nil] at scanned handover loopTrace loopCost ⊢
  refine ⟨input.length + (loopTicks + 1), ?_, ?_⟩
  · nlinarith
  · exact scanned.trans (Steps.next handover loopTrace)

/-- Mathematical operands and an initialized zero remainder. Each word has
one extra capacity digit; no control state depends on that runtime capacity. -/
def inputRepresentation (sizes : Unit → ℕ) (operands : ℕ × ℕ) (tapes : Tapes Alphabet) : Prop :=
  ∃ input divisor remainder : List Bool,
    input.length = sizes () + 1 ∧ divisor.length = sizes () + 1 ∧ remainder.length = sizes () + 1 ∧
    value input = operands.1 ∧ value divisor = operands.2 ∧ value remainder = 0 ∧
    tapes = frame [3] (word input ++ [0]) divisor remainder

/-- Output retains both operands and returns their remainder at the same width. -/
def outputRepresentation (sizes : Unit → ℕ) (output : (ℕ × ℕ) × ℕ) (tapes : Tapes Alphabet) : Prop :=
  ∃ input divisor remainder : List Bool,
    input.length = sizes () + 1 ∧ divisor.length = sizes () + 1 ∧ remainder.length = sizes () + 1 ∧
    value input = output.1.1 ∧ value divisor = output.1.2 ∧ value remainder = output.2 ∧
    tapes = frame [3] (word input ++ [0]) divisor remainder

/-- Polynomial-time binary remainder with explicit mathematical preconditions.
Zero divisors are outside the hypothesis; the routine has no error output. -/
theorem contract : Computes machine entry exit inputRepresentation outputRepresentation
    (fun sizes operands => operands.1 < 2 ^ sizes () ∧ operands.2 < 2 ^ sizes () ∧ 0 < operands.2)
    (fun _ operands => (operands, operands.1 % operands.2)) := by
  refine ⟨by intro symbols; rfl, 8 * (MvPolynomial.X () + 2) ^ 2 + 10, ?_⟩
  intro sizes operands initial valid represented
  obtain ⟨input, divisor, remainder, inputLength, divisorLength, remainderLength,
    inputValue, divisorValue, remainderValue, rfl⟩ := represented
  have sameLength : divisor.length = remainder.length := by omega
  have bounded : value remainder < value divisor := by omega
  have capacity : 2 * value divisor ≤ 2 ^ remainder.length := by
    rw [remainderLength, pow_succ]
    nlinarith [valid.2.1]
  obtain ⟨ticks, cost, trace⟩ := steps input divisor remainder sameLength bounded capacity
  have resultLength := finish_length input.reverse remainder divisor sameLength
  have resultValue := finish_value input.reverse remainder divisor sameLength bounded capacity
  simp only [prefixValue_reverse, remainderValue, Nat.mul_zero, Nat.add_zero, inputValue, divisorValue] at resultValue
  refine ⟨ticks, _, ?_, trace, input, divisor, finish divisor input.reverse remainder,
    inputLength, divisorLength, resultLength.trans remainderLength, inputValue, divisorValue, resultValue, rfl⟩
  simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
  rw [inputLength, remainderLength] at cost
  nlinarith

end Polytime2.BinaryRemainder
