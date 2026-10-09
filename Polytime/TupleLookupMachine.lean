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

import Polytime.TupleMachine

/-! # Non-destructive indexed Boolean tuple lookup

Reuse the indexed exchange router; the final read restores the selected bit
instead of replacing it. The binary index remains consumed scratch storage.
-/

namespace Polytime.TupleLookupMachine

open TupleMachine

/-- The exchange controller with a non-destructive final read. -/
def machine : Turing.TM0.Machine Symbol State := fun state symbol =>
  if state.2 = 13 then
    if symbol = cursor false then some ((false, 14), .write (data false))
    else if symbol = cursor true then some ((true, 14), .write (data true))
    else some ((state.1, 13), .move .right)
  else TupleMachine.machine state symbol

theorem routing_predecessor (state next : State) (symbol : Symbol)
    (action : Turing.TM0.Stmt Symbol)
    (transition : TupleMachine.machine state symbol = some (next, action))
    (nextEarly : next.2.val ≤ 12) : state.2.val ≤ 12 := by
  obtain ⟨flag, phase⟩ := state
  by_contra late
  change ¬ phase.val ≤ 12 at late
  have alternatives : phase = 13 ∨ phase = 14 ∨ phase = 15 := by
    apply Or.imp (fun h => Fin.ext h) (Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h))
    omega
  rcases alternatives with equality | equality | equality
  all_goals subst phase
  all_goals by_cases first : symbol = (5 : Symbol)
  all_goals by_cases second : symbol = (6 : Symbol)
  all_goals by_cases delimiter : symbol = 4
  all_goals simp [TupleMachine.machine, first, second, delimiter, cursor] at transition
  all_goals
    obtain ⟨equality, _⟩ := transition
    have phaseEq := congrArg (fun state : State => state.2.val) equality
    norm_num at phaseEq
    omega

/-- Every routing trace ending in an early phase uses the common controller.
The read/return phases cannot return to the router. -/
private theorem routing_trace {ticks : ℕ} {initial final : Tape.Configuration Symbol State}
    (trace : Tape.Steps TupleMachine.machine ticks initial final)
    (finalEarly : final.q.2.val ≤ 12) :
    initial.q.2.val ≤ 12 ∧ Tape.Steps machine ticks initial final := by
  induction trace with
  | zero => exact ⟨finalEarly, .zero _⟩
  | @next count initial middle final transition rest hypothesis =>
    obtain ⟨middleEarly, transferred⟩ := hypothesis finalEarly
    cases commandEq : TupleMachine.machine initial.q initial.Tape.1 with
    | none => simp [Turing.TM0.step, commandEq] at transition
    | some command =>
      obtain ⟨next, action⟩ := command
      simp only [Turing.TM0.step, commandEq, Option.map_some, Option.some.injEq] at transition
      subst middle
      have initialEarly := routing_predecessor initial.q next initial.Tape.1 action
        commandEq middleEarly
      have different : initial.q.2 ≠ (13 : Fin 16) := by
        intro equality
        rw [equality] at initialEarly
        contradiction
      refine ⟨initialEarly, .next ?_ transferred⟩
      simp [Turing.TM0.step, machine, different, commandEq]

/-- Read the cursor bit, restore it, and return the selected bit at the output
slot. Every tuple bit and both surrounding regions are preserved. -/
theorem finish (width : ℕ) (past suffix : List Bool) (old flag : Bool)
    (left right : List Symbol) :
    Tape.Steps machine (2 * width + 2 * past.length + 4)
      (configuration flag 6 (3 :: left)
        (List.replicate width (data false) ++ 4 ::
          (word past ++ cursor old :: (word suffix ++ right))))
      (configuration old 15 (List.replicate width (data true) ++ 3 :: left)
        (data old :: (word (past ++ old :: suffix) ++ right))) := by
  have borrow := (routing_trace
    (borrow_zeros width flag (3 :: left)
      (4 :: (word past ++ cursor old :: (word suffix ++ right)))) (by change (6 : ℕ) ≤ 12; decide)).2
  have delimiter := Tape.move_right (machine := machine) (state := (flag, 6))
    (nextState := (flag, 13)) (List.replicate width (data true) ++ 3 :: left)
    (word past ++ cursor old :: (word suffix ++ right)) 4 (by rfl)
  have scan := Tape.scan_right (machine := machine) (state := (flag, 13)) (word past)
    (4 :: (List.replicate width (data true) ++ 3 :: left))
    (cursor old :: (word suffix ++ right)) (by
      intro symbol member
      obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
      subst symbol
      cases bit <;> rfl)
  have read := Tape.write (machine := machine) (state := (flag, 13))
    (nextState := (old, 14))
    ((word past).reverse ++ 4 :: (List.replicate width (data true) ++ 3 :: left))
    (word suffix ++ right) (cursor old) (data old) (by cases old <;> rfl)
  have back := Tape.scan_left (machine := machine) (state := (old, 14)) (word past).reverse
    (List.replicate width (data true) ++ 3 :: left) (word suffix ++ right) 4 (data old)
    (by
      intro symbol member
      have distinct : symbol ≠ (4 : Symbol) := by
        intro equality
        subst symbol
        simp only [List.mem_cons, List.mem_reverse] at member
        rcases member with equality | member
        · cases old <;> simp [data] at equality
        · obtain ⟨bit, _, equality⟩ := List.mem_map.mp member
          cases bit <;> simp [data] at equality
      simp [machine, TupleMachine.machine, distinct])
  have output := Tape.write (machine := machine) (state := (old, 14))
    (nextState := (old, 15)) (List.replicate width (data true) ++ 3 :: left)
    (word past ++ data old :: (word suffix ++ right)) 4 (data old) (by rfl)
  simp only [List.reverse_reverse] at back
  have trace := borrow.trans (Tape.Steps.next delimiter (scan.trans
    (Tape.Steps.next read (back.trans (Tape.Steps.next output (.zero _))))))
  simpa [configuration, word, List.append_assoc, Nat.add_assoc, Nat.two_mul,
    Nat.add_comm, Nat.add_left_comm] using trace

/-- A non-destructive lookup consumes a binary scratch index and returns the
selected bit. The frame's left and right contexts are arbitrary. -/
theorem lookup (counter bits : List Bool) (left right : List Symbol)
    (valid : Binary.value counter < bits.length) :
    ∃ ticks, ticks ≤ 32 * (counter.length + bits.length + 1) ^ 2 ∧
      Tape.Steps machine ticks
        (configuration false 1 left (data false :: word counter ++ 4 :: word bits ++ right))
        (configuration (bits.getD (Binary.value counter) false) 15
          (List.replicate counter.length (data true) ++ 3 :: left)
          (data (bits.getD (Binary.value counter) false) :: word bits ++ right)) := by
  cases bits with
  | nil => simp at valid
  | cons first rest =>
    have preparation := (routing_trace
      (prepare counter rest first false left right) (by change (6 : ℕ) ≤ 12; decide)).2
    obtain ⟨ticks, before, old, after, decomposition, lengthEq, bound, trace⟩ :=
      route counter [] (first :: rest) false left right valid
    have routed := (routing_trace trace (by change (6 : ℕ) ≤ 12; decide)).2
    have ending := finish counter.length before after old false left right
    simp only [List.nil_append] at routed
    have oldEq : (first :: rest).getD (Binary.value counter) false = old := by
      rw [decomposition, ← lengthEq]
      simp
    refine ⟨2 * counter.length + 7 + ticks + (2 * counter.length + 2 * before.length + 4), ?_, ?_⟩
    · have positionBound : Binary.value counter < (first :: rest).length := valid
      rw [lengthEq]
      simp only [List.length_nil, Nat.add_zero] at bound
      nlinarith
    · have result := preparation.trans (routed.trans ending)
      rw [oldEq]
      simpa [marked, word, ← decomposition, Nat.add_assoc] using result

@[simp] theorem halt (flag : Bool) (symbol : Symbol) : machine (flag, 15) symbol = none := rfl

/-- Lookup directly in a canonical bit vector, using a padded binary scratch
index. No decoding or re-encoding of the stored vector is performed. -/
theorem realizes_bits {width : ℕ} (bits : BitVec width) (index : Fin width)
    (left right : List Symbol) :
    ∃ ticks, ticks ≤ 128 * (width + 1) ^ 2 ∧
      Tape.Steps machine ticks
        (configuration false 1 left
          (data false :: word (Binary.digits width index.val) ++ 4 ::
            word (List.ofFn (BoolTuple.fromBits bits)) ++ right))
        (configuration (bits.getLsbD index.val) 15
          (List.replicate width (data true) ++ 3 :: left)
          (data (bits.getLsbD index.val) ::
            word (List.ofFn (BoolTuple.fromBits bits)) ++ right)) := by
  have indexFits : index.val < 2 ^ width := index.isLt.trans Nat.lt_two_pow_self
  have counterValue : Binary.value (Binary.digits width index.val) = index.val := by
    simp [Nat.mod_eq_of_lt indexFits]
  obtain ⟨ticks, bound, trace⟩ := lookup (Binary.digits width index.val)
    (List.ofFn (BoolTuple.fromBits bits)) left right (by simp [counterValue])
  refine ⟨ticks, ?_, ?_⟩
  · simp only [Binary.digits_length, List.length_ofFn] at bound
    calc
      ticks ≤ 32 * (width + width + 1) ^ 2 := bound
      _ ≤ 32 * (2 * (width + 1)) ^ 2 :=
        Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left (by omega) 2)
      _ = 128 * (width + 1) ^ 2 := by ring
  · have selected : (List.ofFn (BoolTuple.fromBits bits)).getD index.val false =
        bits.getLsbD index.val := by
      simp [List.getD_eq_getElem?_getD, index.isLt, BoolTuple.fromBits]
    simpa only [counterValue, Binary.digits_length, selected] using trace

end Polytime.TupleLookupMachine
