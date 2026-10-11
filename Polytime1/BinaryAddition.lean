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

import Polytime1.Realization
import Polytime1.TupleMachine

/-! # Binary addition in a runtime-width pair buffer

Each reserved entry contains one bit from each operand, least significant first.
The result reuses the first bit of each pair and clears the second; a leading
carry slot supplies the extra output bit. Width is runtime data, not controller
state. A delimiter ends traversal and a private marker restores the entry head.
-/

namespace Polytime1.BinaryAddition

open TupleMachine (Symbol data word)

abbrev Pair := Bool × Bool

def sumBit (first second carry : Bool) : Bool := xor (xor first second) carry

def carryBit (first second carry : Bool) : Bool :=
  (first && second) || (first && carry) || (second && carry)

def add : Bool → List Pair → List Bool × Bool
  | carry, [] => ([], carry)
  | carry, (first, second) :: rest =>
      let result := add (carryBit first second carry) rest
      (sumBit first second carry :: result.1, result.2)

@[simp] theorem add_length (carry : Bool) (pairs : List Pair) :
    (add carry pairs).1.length = pairs.length := by
  induction pairs generalizing carry with
  | nil => rfl
  | cons pair rest hypothesis => simp [add, hypothesis]

/-- No truncation: the final carry is the additional most significant bit. -/
theorem add_value (carry : Bool) (pairs : List Pair) :
    Binary.value (add carry pairs).1 + 2 ^ pairs.length * (add carry pairs).2.toNat =
      Binary.value (pairs.map Prod.fst) + Binary.value (pairs.map Prod.snd) + carry.toNat := by
  induction pairs generalizing carry with
  | nil => simp [add, Binary.value]
  | cons pair rest hypothesis =>
    obtain ⟨first, second⟩ := pair
    have result := hypothesis (carryBit first second carry)
    cases first <;> cases second <;> cases carry <;>
      simp [add, sumBit, carryBit, Binary.value, Nat.pow_succ] at * <;> nlinarith

/-- Canonical product encoding of the operand bits in each reserved entry. -/
def pairBits (pairs : List Pair) : List Bool := pairs.flatMap fun pair => [pair.1, pair.2]

@[simp] theorem pairBits_length (pairs : List Pair) : (pairBits pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest hypothesis => simp [pairBits]; omega

def outputBits (bits : List Bool) : List Bool := bits.flatMap fun bit => [bit, false]

@[simp] theorem outputBits_length (bits : List Bool) : (outputBits bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest hypothesis => simp [outputBits]; omega

inductive State
  | start | enter
  | first (carry : Bool)
  | second (carry first : Bool)
  | back (sum carry : Bool)
  | writeSum (sum carry : Bool)
  | nextSecond (carry : Bool)
  | nextFirst (carry : Bool)
  | rewind (carry : Bool)
  | halt
  deriving DecidableEq, Fintype, Inhabited

/-- All arithmetic state is three bits at most; operand width never enters it. -/
def machine : Turing.TM0.Machine Symbol State
  | .start, _ => some (.enter, .write 6)
  | .enter, _ => some (.first false, .move .right)
  | .first carry, symbol =>
      if symbol = 3 then some (.rewind carry, .write symbol)
      else some (.second carry (decide (symbol = data true)), .move .right)
  | .second carry first, symbol =>
      let second := decide (symbol = data true)
      some (.back (sumBit first second carry) (carryBit first second carry), .write (data false))
  | .back sum carry, _ => some (.writeSum sum carry, .move .left)
  | .writeSum sum carry, _ => some (.nextSecond carry, .write (data sum))
  | .nextSecond carry, _ => some (.nextFirst carry, .move .right)
  | .nextFirst carry, _ => some (.first carry, .move .right)
  | .rewind carry, symbol =>
      if symbol = 6 then some (.halt, .write (data carry))
      else some (.rewind carry, .move .left)
  | .halt, _ => none

/-- Six actual transitions consume a pair and emit its sum and cleared spare bit. -/
private theorem pair_run (first second carry : Bool) (left right : List Symbol) :
    Tape.Steps machine 6
      (Tape.configuration (.first carry) left (data first :: data second :: right))
      (Tape.configuration (.first (carryBit first second carry))
        (data false :: data (sumBit first second carry) :: left) right) := by
  have read := Tape.move_right (machine := machine) (state := .first carry)
    (nextState := .second carry first) left (data second :: right) (data first)
    (by cases first <;> rfl)
  have clear := Tape.write (machine := machine) (state := .second carry first)
    (nextState := .back (sumBit first second carry) (carryBit first second carry))
    (data first :: left) right (data second) (data false) (by cases second <;> rfl)
  have back := Tape.move_left_list (machine := machine)
    (state := .back (sumBit first second carry) (carryBit first second carry))
    (nextState := .writeSum (sumBit first second carry) (carryBit first second carry))
    left (data false :: right) (data first) (by intros; rfl)
  have write := Tape.write (machine := machine)
    (state := .writeSum (sumBit first second carry) (carryBit first second carry))
    (nextState := .nextSecond (carryBit first second carry)) left (data false :: right)
    (data first) (data (sumBit first second carry)) (by rfl)
  have next := Tape.move_right (machine := machine)
    (state := .nextSecond (carryBit first second carry)) (nextState := .nextFirst (carryBit first second carry))
    left (data false :: right) (data (sumBit first second carry)) (by rfl)
  have advance := Tape.move_right (machine := machine)
    (state := .nextFirst (carryBit first second carry)) (nextState := .first (carryBit first second carry))
    (data (sumBit first second carry) :: left) right (data false) (by rfl)
  exact .next read (.next clear (.next back (.next write (.next next (.next advance (.zero _))))))

private theorem scan (carry : Bool) (pairs : List Pair) (left right : List Symbol) :
    Tape.Steps machine (6 * pairs.length)
      (Tape.configuration (.first carry) left (word (pairBits pairs) ++ right))
      (Tape.configuration (.first (add carry pairs).2)
        ((word (outputBits (add carry pairs).1)).reverse ++ left) right) := by
  induction pairs generalizing carry left with
  | nil => simp [add, pairBits, outputBits, word]; exact .zero _
  | cons pair rest hypothesis =>
    obtain ⟨first, second⟩ := pair
    have trace := (pair_run first second carry left (word (pairBits rest) ++ right)).trans
      (hypothesis (carryBit first second carry) (data false :: data (sumBit first second carry) :: left))
    simpa [add, pairBits, outputBits, word, Nat.mul_add, List.append_assoc, List.reverse_append,
      Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using trace

/-- Rewind across a binary region, stopping at the private marker. Both caller
regions survive and the head returns to the carry slot. -/
private theorem rewind_run (carry : Bool) (past : List Symbol) (left right : List Symbol)
    (symbol : Symbol) (notMarker : symbol ≠ 6) (valid : ∀ item ∈ past, item ≠ 6) :
    Tape.Steps machine (past.length + 2)
      (Tape.configuration (.rewind carry) (past ++ 6 :: left) (symbol :: right))
      (Tape.configuration .halt left (data carry :: (past.reverse ++ symbol :: right))) := by
  induction past generalizing symbol right with
  | nil =>
    have move := Tape.move_left (machine := machine) (state := .rewind carry)
      (nextState := .rewind carry) left right 6 symbol (by simp [machine, notMarker])
    have write := Tape.write (machine := machine) (state := .rewind carry) (nextState := .halt)
      left (symbol :: right) 6 (data carry) (by simp [machine])
    exact .next move (.next write (.zero _))
  | cons previous past hypothesis =>
    have move := Tape.move_left (machine := machine) (state := .rewind carry)
      (nextState := .rewind carry) (past ++ 6 :: left) right previous symbol
      (by simp [machine, notMarker])
    have rest := hypothesis (symbol :: right) previous (valid previous (by simp))
      (by intro item member; exact valid item (by simp [member]))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Tape.Steps.next move rest

/-- The complete buffer operation has linear bit cost and preserves both sides
of its reserved frame. No numeric-magnitude counter or runtime fuel is used. -/
theorem realizes (pairs : List Pair) (left right : List Symbol) :
    Tape.Steps machine (8 * pairs.length + 5)
      (Tape.configuration .start left (data false :: (word (pairBits pairs) ++ 3 :: right)))
      (Tape.configuration .halt left
        (data (add false pairs).2 :: (word (outputBits (add false pairs).1) ++ 3 :: right))) := by
  have mark := Tape.write (machine := machine) (state := .start) (nextState := .enter)
    left (word (pairBits pairs) ++ 3 :: right) (data false) 6 (by rfl)
  have enter := Tape.move_right (machine := machine) (state := .enter) (nextState := .first false)
    left (word (pairBits pairs) ++ 3 :: right) 6 (by rfl)
  have scanned := scan false pairs (6 :: left) (3 :: right)
  have handover := Tape.write (machine := machine) (state := .first (add false pairs).2)
    (nextState := .rewind (add false pairs).2)
    ((word (outputBits (add false pairs).1)).reverse ++ 6 :: left) right 3 3 (by simp [machine])
  have returned := rewind_run (add false pairs).2
    ((word (outputBits (add false pairs).1)).reverse) left right 3 (by decide) (by
      intro symbol member
      simp only [List.mem_reverse, word, List.mem_map] at member
      obtain ⟨bit, _, rfl⟩ := member
      cases bit <;> decide)
  have trace := (Tape.Steps.next mark (Tape.Steps.next enter scanned)).trans (Tape.Steps.next handover returned)
  convert trace using 1 <;> simp [add_length]
  omega

abbrev context : SizeContext := ⟨Unit, inferInstance⟩

abbrev Input (sizes : SizeAssignment context) := Fin (sizes ()) → Pair
abbrev Output (sizes : SizeAssignment context) := (Fin (sizes ()) → Bool) × Bool

/-- Convert the complete list sum back to its fixed-size mathematical tuple. -/
def result (sizes : SizeAssignment context) (input : Input sizes) : Output sizes :=
  let sum := add false (List.ofFn input)
  ((fun index => sum.1[index.val]'(by rw [add_length, List.length_ofFn]; exact index.isLt)), sum.2)

@[simp] theorem result_bits (sizes : SizeAssignment context) (input : Input sizes) :
    List.ofFn (result sizes input).1 = (add false (List.ofFn input)).1 := by
  apply List.ext_getElem
  · simp [result]
  · intro index firstValid secondValid
    simp [result]

/-- Both caller regions are independent of the mathematical operands. -/
def inputRepresentation (sizes : SizeAssignment context) (caller : List Symbol × List Symbol)
    (input : Input sizes) (tape : Turing.Tape Symbol) : Prop :=
  tape = (Tape.configuration () caller.1
    (data false :: (word (pairBits (List.ofFn input)) ++ 3 :: caller.2))).Tape

def outputRepresentation (sizes : SizeAssignment context) (caller : List Symbol × List Symbol)
    (output : Output sizes) (tape : Turing.Tape Symbol) : Prop :=
  tape = (Tape.configuration () caller.1
    (data output.2 :: (word (outputBits (List.ofFn output.1)) ++ 3 :: caller.2))).Tape

noncomputable section AdditionContract

/-- Exact binary addition, polynomial in bit capacity, using the shared
realization interface and preserving neighboring reserved caller regions. -/
theorem contract : Realization.Realizes inputRepresentation outputRepresentation
    (fun _ _ => True) (fun sizes input output =>
      Binary.value (List.ofFn output.1) + 2 ^ sizes () * output.2.toNat =
        Binary.value ((List.ofFn input).map Prod.fst) + Binary.value ((List.ofFn input).map Prod.snd)) := by
  refine ⟨State, inferInstance, inferInstance, .start, .halt, machine,
    SizePolynomial.constant 8 * SizePolynomial.parameter () + SizePolynomial.constant 5,
    by intros; rfl, ?_⟩
  intro sizes caller input initial _ represented
  change initial = _ at represented
  subst initial
  refine ⟨result sizes input,
    (Tape.configuration () caller.1
      (data (result sizes input).2 :: (word (outputBits (List.ofFn (result sizes input).1)) ++ 3 :: caller.2))).Tape,
    8 * sizes () + 5, by simp, ?_, ?_, rfl⟩
  · rw [result_bits]
    simpa only [List.length_ofFn, result, Tape.configuration] using
      realizes (List.ofFn input) caller.1 caller.2
  · dsimp only
    rw [result_bits]
    have correct := add_value false (List.ofFn input)
    simpa only [result, List.length_ofFn, Bool.toNat_false, Nat.add_zero] using correct

end AdditionContract

section ExecutableChecks

def execute (pairs : List Pair) (left right : List Symbol) : Option (List Symbol × List Symbol) :=
  (Tape.run machine (8 * pairs.length + 5)
    (Tape.configuration .start left (data false :: (word (pairBits pairs) ++ 3 :: right)))).map fun final =>
      ((List.range left.length).map final.Tape.left.nth,
        (List.range (2 * pairs.length + 2 + right.length)).map final.Tape.right₀.nth)

-- Empty operands, overflow, and a carry propagating through every reserved bit.
#guard execute [] [7, 6] [4, 7] = some ([7, 6], [1, 3, 4, 7])
#guard execute [(true, true)] [7] [4, 6] = some ([7], [2, 1, 1, 3, 4, 6])
#guard execute [(true, true), (true, false), (true, false)] [6, 7] [4] =
  some ([6, 7], [2, 1, 1, 1, 1, 1, 1, 3, 4])
#guard execute [(false, true), (true, false)] [7] [] = some ([7], [1, 2, 1, 2, 1, 3])

end ExecutableChecks

end Polytime1.BinaryAddition
