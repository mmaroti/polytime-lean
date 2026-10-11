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

import Polytime1.Examples.TupleLookup

/-! # Two indexed exchanges in one prepared frame

Two tuple regions share one tape. The old bit returned by the first exchange
becomes the replacement in the second. The updated first tuple and arbitrary
surrounding storage survive the second call. No external preparation or header
parsing is repeated between calls.
-/

namespace Polytime1.Examples.TupleComposition

open TupleMachine (Symbol data word)

/-- Left states run the original routine, tagged by which call is active.
The right state transfers the first result into the second argument slot. -/
abbrev State := Sum (Bool × TupleMachine.State) Bool

instance : Inhabited State := ⟨.inl (false, (false, 1))⟩

def machine : Turing.TM0.Machine Symbol State
  | .inl (second, (flag, phase)), symbol =>
      if !second && phase == 15 then
        if symbol = 7 then some (.inr flag, .move .right)
        else some (.inl (false, (flag, 15)), .move .right)
      else (TupleMachine.machine (flag, phase) symbol).map fun (next, action) =>
        (.inl (second, next), action)
  | .inr result, _ => some (.inl (true, (false, 1)), .write (data result))

def configuration (second flag : Bool) (phase : Fin 16) (left right : List Symbol) :=
  Tape.configuration (.inl (second, (flag, phase)) : State) left right

def embed (second : Bool) (source : Tape.Configuration Symbol TupleMachine.State) :
    Tape.Configuration Symbol State := ⟨.inl (second, source.q), source.Tape⟩

private theorem instruction (second : Bool) (state next : TupleMachine.State)
    (symbol : Symbol) (action : Turing.TM0.Stmt Symbol)
    (transition : TupleMachine.machine state symbol = some (next, action)) :
    machine (.inl (second, state)) symbol = some (.inl (second, next), action) := by
  obtain ⟨flag, phase⟩ := state
  have active : phase ≠ 15 := by
    intro equality
    subst phase
    simp [TupleMachine.machine] at transition
  simp [machine, active, transition]

private theorem simulate (second : Bool)
    (initial middle : Tape.Configuration Symbol TupleMachine.State)
    (transition : Turing.TM0.step TupleMachine.machine initial = some middle) :
    Turing.TM0.step machine (embed second initial) = some (embed second middle) := by
  obtain ⟨state, tape⟩ := initial
  cases equation : TupleMachine.machine state tape.1 with
  | none => simp [Turing.TM0.step, equation] at transition
  | some command =>
    obtain ⟨next, action⟩ := command
    have transferred := instruction second state next tape.1 action equation
    simp only [Turing.TM0.step, equation, Option.map_some, Option.some.injEq] at transition
    subst middle
    simp [Turing.TM0.step, embed, transferred]

/-- Run an existing routine in either call region, preserving its step count. -/
theorem lift {ticks : ℕ} {initial final : Tape.Configuration Symbol TupleMachine.State}
    (second : Bool) (trace : TupleMachine.Steps ticks initial final) :
    Tape.Steps machine ticks (embed second initial) (embed second final) :=
  trace.map (embed second) (simulate second)

/-- Transfer the returned bit across the first tuple to the second argument
slot. The first output and both surrounding contexts are preserved. -/
theorem handoff (result placeholder : Bool) (updated : List Bool)
    (left rest : List Symbol) :
    Tape.Steps machine (updated.length + 3)
      (configuration false result 15 left
        (data result :: (word updated ++ 7 :: data placeholder :: rest)))
      (configuration true false 1
        (7 :: (word updated).reverse ++ data result :: left)
        (data result :: rest)) := by
  have scan := Tape.scan_right (machine := machine)
    (state := (.inl (false, (result, 15)) : State))
    (data result :: word updated) left (7 :: data placeholder :: rest)
    (by
      intro symbol member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · cases result <;> rfl
      · obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
        cases bit <;> rfl)
  have advance := Tape.move_right (machine := machine)
    (state := (.inl (false, (result, 15)) : State)) (nextState := (.inr result : State))
    ((data result :: word updated).reverse ++ left) (data placeholder :: rest) 7 (by rfl)
  have install := Tape.write (machine := machine) (state := (.inr result : State))
    (nextState := (.inl (true, (false, 1)) : State))
    (7 :: ((data result :: word updated).reverse ++ left)) rest
    (data placeholder) (data result) (by rfl)
  simpa [configuration, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
    scan.trans (Tape.Steps.next advance (Tape.Steps.next install (.zero _)))

/-- Two adjacent operation regions on a prepared tape. The second replacement
slot is vacant (initialized to false); handoff installs the first result. -/
def frame (firstCounter firstTuple secondCounter secondTuple : List Bool)
    (replacement : Bool) (right : List Symbol) : List Symbol :=
  data replacement :: (word firstCounter ++ 4 :: (word firstTuple ++
    7 :: data false :: (word secondCounter ++ 4 :: (word secondTuple ++ right))))

/-- The consumed counters stay in their reserved slots; the completed first
output remains to the left of the second region, in reverse tape-stack order. -/
def retained (firstWidth secondWidth : ℕ) (firstOutput : List Bool)
    (firstResult : Bool) (left : List Symbol) : List Symbol :=
  List.replicate secondWidth (data true) ++ 3 ::
    (7 :: (word firstOutput).reverse ++ data firstResult ::
      (List.replicate firstWidth (data true) ++ 3 :: left))

/-- Compose two exchange contracts and the handoff contract. The second call
uses the first result, preserves its updated tuple, and touches neither external
context. The controller and alphabet are independent of both tuple lengths. -/
theorem compose (firstCounter firstTuple secondCounter secondTuple : List Bool)
    (replacement : Bool) (left right : List Symbol)
    (firstValid : Binary.value firstCounter < firstTuple.length)
    (secondValid : Binary.value secondCounter < secondTuple.length) :
    let firstResult := firstTuple.getD (Binary.value firstCounter) false
    let firstOutput := firstTuple.set (Binary.value firstCounter) replacement
    let secondResult := secondTuple.getD (Binary.value secondCounter) false
    ∃ ticks, ticks ≤ 96 *
      (firstCounter.length + firstTuple.length + secondCounter.length + secondTuple.length + 1) ^ 2 ∧
      Tape.Steps machine ticks
        (configuration false false 1 left
          (frame firstCounter firstTuple secondCounter secondTuple replacement right))
        (configuration true secondResult 15
          (retained firstCounter.length secondCounter.length firstOutput firstResult left)
          (data secondResult ::
            (word (secondTuple.set (Binary.value secondCounter) firstResult) ++ right))) := by
  dsimp only
  let firstResult := firstTuple.getD (Binary.value firstCounter) false
  let firstOutput := firstTuple.set (Binary.value firstCounter) replacement
  let following := word secondCounter ++ 4 :: (word secondTuple ++ right)
  obtain ⟨firstTicks, firstBound, firstTrace⟩ := TupleMachine.exchange
    firstCounter firstTuple replacement left (7 :: data false :: following) firstValid
  have first := lift false firstTrace
  have transfer := handoff firstResult false firstOutput
    (List.replicate firstCounter.length (data true) ++ 3 :: left) following
  let preserved := 7 :: (word firstOutput).reverse ++ data firstResult ::
    (List.replicate firstCounter.length (data true) ++ 3 :: left)
  obtain ⟨secondTicks, secondBound, secondTrace⟩ := TupleMachine.exchange
    secondCounter secondTuple firstResult preserved right secondValid
  have second := lift true secondTrace
  change Tape.Steps machine firstTicks _ _ at first
  change Tape.Steps machine secondTicks _ _ at second
  have trace := first.trans (transfer.trans second)
  refine ⟨firstTicks + (firstOutput.length + 3 + secondTicks), ?_, ?_⟩
  · have firstLength : firstOutput.length = firstTuple.length := List.length_set
    rw [firstLength]
    have firstCapacity : firstCounter.length + firstTuple.length + 1 ≤
        firstCounter.length + firstTuple.length + secondCounter.length + secondTuple.length + 1 := by omega
    have secondCapacity : secondCounter.length + secondTuple.length + 1 ≤
        firstCounter.length + firstTuple.length + secondCounter.length + secondTuple.length + 1 := by omega
    have firstSquare := Nat.pow_le_pow_left firstCapacity 2
    have secondSquare := Nat.pow_le_pow_left secondCapacity 2
    nlinarith [sq_nonneg (firstCounter.length + firstTuple.length + secondCounter.length + secondTuple.length)]
  · simpa [embed, configuration, TupleMachine.configuration, Tape.configuration,
      frame, retained, firstResult, firstOutput, following, preserved, List.append_assoc] using trace

/-- Padded binary indices give a bound polynomial in the two tuple lengths. -/
theorem realizes (firstTuple secondTuple : List Bool)
    (firstIndex : Fin firstTuple.length) (secondIndex : Fin secondTuple.length)
    (replacement : Bool) (left right : List Symbol) :
    ∃ ticks, ticks ≤ 384 * (firstTuple.length + secondTuple.length + 1) ^ 2 ∧
      Tape.Steps machine ticks
        (configuration false false 1 left
          (frame (Binary.digits firstTuple.length firstIndex.val) firstTuple
            (Binary.digits secondTuple.length secondIndex.val) secondTuple replacement right))
        (configuration true (secondTuple.getD secondIndex.val false) 15
          (retained firstTuple.length secondTuple.length
            (firstTuple.set firstIndex.val replacement) (firstTuple.getD firstIndex.val false) left)
          (data (secondTuple.getD secondIndex.val false) ::
            (word (secondTuple.set secondIndex.val (firstTuple.getD firstIndex.val false)) ++ right))) := by
  have firstValue : Binary.value (Binary.digits firstTuple.length firstIndex.val) = firstIndex.val := by
    simp [Nat.mod_eq_of_lt (firstIndex.isLt.trans Nat.lt_two_pow_self)]
  have secondValue : Binary.value (Binary.digits secondTuple.length secondIndex.val) = secondIndex.val := by
    simp [Nat.mod_eq_of_lt (secondIndex.isLt.trans Nat.lt_two_pow_self)]
  obtain ⟨ticks, bound, trace⟩ := compose
    (Binary.digits firstTuple.length firstIndex.val) firstTuple
    (Binary.digits secondTuple.length secondIndex.val) secondTuple replacement left right
    (by rw [firstValue]; exact firstIndex.isLt)
    (by rw [secondValue]; exact secondIndex.isLt)
  refine ⟨ticks, ?_, ?_⟩
  · simp only [Binary.digits_length] at bound
    calc
      ticks ≤ _ := bound
      _ ≤ 96 * (2 * (firstTuple.length + secondTuple.length + 1)) ^ 2 :=
        Nat.mul_le_mul_left 96 (Nat.pow_le_pow_left (by omega) 2)
      _ = _ := by ring
  · simpa [firstValue, secondValue] using trace

/-- Mathematical tuple contract: replace the first selected entry, then use its
old value to replace the second selected entry. Both old values are retained. -/
theorem realizes_tuples {firstLength secondLength : ℕ}
    (firstTuple : Fin firstLength → Bool) (secondTuple : Fin secondLength → Bool)
    (firstIndex : Fin firstLength) (secondIndex : Fin secondLength)
    (replacement : Bool) (left right : List Symbol) :
    ∃ ticks, ticks ≤ 384 * (firstLength + secondLength + 1) ^ 2 ∧
      Tape.Steps machine ticks
        (configuration false false 1 left
          (frame (Binary.digits firstLength firstIndex.val) (List.ofFn firstTuple)
            (Binary.digits secondLength secondIndex.val) (List.ofFn secondTuple) replacement right))
        (configuration true (BoolTuple.lookup secondTuple secondIndex) 15
          (retained firstLength secondLength
            (List.ofFn (BoolTuple.update firstTuple firstIndex replacement))
            (BoolTuple.lookup firstTuple firstIndex) left)
          (data (BoolTuple.lookup secondTuple secondIndex) ::
            (word (List.ofFn (BoolTuple.update secondTuple secondIndex
              (BoolTuple.lookup firstTuple firstIndex))) ++ right))) := by
  simpa [TupleLookup.lookup_list, ← TupleLookup.update_list, BoolTuple.lookup] using
    realizes (List.ofFn firstTuple) (List.ofFn secondTuple)
      (firstIndex.cast (List.length_ofFn (f := firstTuple)).symm)
      (secondIndex.cast (List.length_ofFn (f := secondTuple)).symm) replacement left right

@[simp] theorem halt (flag : Bool) (left right : List Symbol) :
    Turing.TM0.step machine (configuration true flag 15 left right) = none := by
  simp [Turing.TM0.step, configuration, Tape.configuration, machine, TupleMachine.machine]

/-- Execution reaches a genuine halt; the polynomial budget is an observer's
fuel and is not part of the controller or its stopping condition. -/
theorem run_realizes (firstTuple secondTuple : List Bool)
    (firstIndex : Fin firstTuple.length) (secondIndex : Fin secondTuple.length)
    (replacement : Bool) (left right : List Symbol) :
    Tape.run machine (384 * (firstTuple.length + secondTuple.length + 1) ^ 2)
      (configuration false false 1 left
        (frame (Binary.digits firstTuple.length firstIndex.val) firstTuple
          (Binary.digits secondTuple.length secondIndex.val) secondTuple replacement right)) =
      some (configuration true (secondTuple.getD secondIndex.val false) 15
        (retained firstTuple.length secondTuple.length (firstTuple.set firstIndex.val replacement)
          (firstTuple.getD firstIndex.val false) left)
        (data (secondTuple.getD secondIndex.val false) ::
          (word (secondTuple.set secondIndex.val (firstTuple.getD firstIndex.val false)) ++ right))) := by
  obtain ⟨ticks, bound, trace⟩ := realizes firstTuple secondTuple firstIndex secondIndex replacement left right
  exact Tape.run_of_steps trace (halt ..) bound

/-- Observe both retained old-bit/updated-tuple outputs for executable checks. -/
def execute (firstTuple secondTuple : List Bool)
    (firstIndex : Fin firstTuple.length) (secondIndex : Fin secondTuple.length)
    (replacement : Bool) : Option (List Bool × List Bool) :=
  (Tape.run machine (384 * (firstTuple.length + secondTuple.length + 1) ^ 2)
    (configuration false false 1 []
      (frame (Binary.digits firstTuple.length firstIndex.val) firstTuple
        (Binary.digits secondTuple.length secondIndex.val) secondTuple replacement [7]))).map fun final =>
    ((List.range (firstTuple.length + 1)).map fun position =>
      decide (final.Tape.left.nth (secondTuple.length + 2 + firstTuple.length - position) = data true),
     (List.range (secondTuple.length + 1)).map fun position =>
      decide (final.Tape.right₀.nth position = data true))

-- The first returned true becomes the second replacement, while the first tuple
-- keeps its new false; both original selected values remain in the outputs.
#guard execute [true] [false] 0 0 false = some ([true, false], [false, true])
-- Different lengths, first/last positions, and a transferred false bit.
#guard execute [true, false, true] [true, false] 1 0 true =
  some ([false, true, true, true], [true, false, false])
#guard execute [false, true] [false, false, false] 1 2 false =
  some ([true, false, false], [false, false, false, true])
-- Borrow propagation through three zero bits in both calls.
#guard execute [false, false, false, false, false, false, false, false, true]
    [false, false, false, false, false, false, false, false, false] 8 8 false =
  some ([true, false, false, false, false, false, false, false, false, false],
    [false, false, false, false, false, false, false, false, false, true])

end Polytime1.Examples.TupleComposition
