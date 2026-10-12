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

import Polytime2.BinaryAddition
import Polytime2.TerminatedCopy
import Polytime2.Branch
import Polytime2.While

/-! # Binary multiplication by shifted additions

Each multiplier digit selects an addition, then the multiplicand is shifted
left by one bit. Width grows by one digit per iteration, independently of the
numeric magnitude of the multiplier. The constant-cost shift below avoids
relocating whole words. The complete loop has a fixed finite controller and
a polynomial transition bound in both runtime digit capacities.
-/

namespace Polytime2.BinaryMultiplication

open MultiTape
open Binary (Symbol data word value)

/-- Logical shift-and-add state, with capacities growing by one per digit. -/
def accumulate : List Bool → List Bool → List Bool → List Bool
  | _shifted, total, [] => total
  | shifted, total, bit :: bits =>
    accumulate (false :: shifted)
      (BinaryAddition.add total (if bit then shifted else List.replicate shifted.length false)) bits

private theorem zero_value (count : ℕ) : value (List.replicate count false) = 0 := by
  induction count with
  | zero => rfl
  | succ count hypothesis => simp [List.replicate_succ, value, hypothesis]

/-- The number of iterations is the multiplier's digit count, not its value. -/
theorem accumulate_length (shifted total bits : List Bool)
    (sameLength : shifted.length = total.length) :
    (accumulate shifted total bits).length = total.length + bits.length := by
  induction bits generalizing shifted total with
  | nil => simp [accumulate]
  | cons bit bits hypothesis =>
    have selectedLength : (if bit then shifted else List.replicate shifted.length false).length = total.length := by
      cases bit <;> simp [sameLength]
    have addedLength := BinaryAddition.add_length total _ selectedLength
    have nextLength : (false :: shifted).length =
        (BinaryAddition.add total (if bit then shifted else List.replicate shifted.length false)).length := by
      rw [addedLength, List.length_cons, sameLength]
    simp only [accumulate, hypothesis _ _ nextLength, addedLength, List.length_cons]
    omega

/-- Mathematical multiplication, also allowing an already accumulated sum. -/
theorem accumulate_value (shifted total bits : List Bool)
    (sameLength : shifted.length = total.length) :
    value (accumulate shifted total bits) = value total + value shifted * value bits := by
  induction bits generalizing shifted total with
  | nil => simp [accumulate, value]
  | cons bit bits hypothesis =>
    have selectedLength : (if bit then shifted else List.replicate shifted.length false).length = total.length := by
      cases bit <;> simp [sameLength]
    have addedLength := BinaryAddition.add_length total _ selectedLength
    have nextLength : (false :: shifted).length =
        (BinaryAddition.add total (if bit then shifted else List.replicate shifted.length false)).length := by
      rw [addedLength, List.length_cons, sameLength]
    rw [accumulate, hypothesis _ _ nextLength, BinaryAddition.add_value total _ selectedLength]
    cases bit <;> simp [value, zero_value] <;> ring

/-- Prepend a binary zero by moving the boundary one cell into blank storage. -/
def shiftMachine : Machine (fun _ : Unit => Symbol) (Fin 4) := fun state symbols =>
  match state.val with
  | 0 => some (1, fun _ => (symbols (), some .left))
  | 1 => some (2, fun _ => (1, some .left))
  | 2 => some (3, fun _ => (3, some .right))
  | _ => none

/-- Multiplication by two needs three transitions and no word-sized shift. -/
theorem shift_steps (bits : List Bool) (right : List Symbol) :
    Steps shiftMachine 3
      (0, Binary.tape [3] (word bits ++ right))
      (3, Binary.tape [3] (word (false :: bits) ++ right)) := by
  have first : step shiftMachine (0, Binary.tape [3] (word bits ++ right)) =
      some (1, Binary.tape [] (3 :: (word bits ++ right))) := by
    simp only [step, shiftMachine, Fin.val_zero, Option.map_some, Prod.mk.injEq, true_and, Option.some.injEq]
    funext name
    cases name
    change ((Binary.tape [3] (word bits ++ right) ()).write
      (Binary.tape [3] (word bits ++ right) ()).head).move .left = _
    rw [Turing.Tape.write_self]
    simp [Binary.tape, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have second : step shiftMachine (1, Binary.tape [] (3 :: (word bits ++ right))) =
      some (2, Binary.tape [] (0 :: 1 :: (word bits ++ right))) := by
    rfl
  have third : step shiftMachine (2, Binary.tape [] (0 :: 1 :: (word bits ++ right))) =
      some (3, Binary.tape [3] (1 :: (word bits ++ right))) := by
    rfl
  simpa [word, data] using Steps.next first (Steps.next second (Steps.next third (.zero _)))


/-- Multiplier, shifted multiplicand, accumulator, sum scratch, and zero word. -/
abbrev Alphabet := fun _ : Fin 5 => Symbol

def tape (bits : List Bool) : Turing.Tape Symbol :=
  Binary.tape [3] (word bits ++ [0]) ()

def frame (multiplier : Turing.Tape Symbol) (shifted total output zeros : List Bool) : Tapes Alphabet :=
  fun name => if name = 0 then multiplier else if name = 1 then tape shifted
    else if name = 2 then tape total else if name = 3 then tape output else tape zeros

@[simp] private theorem mk_two_blanks (payload : List Symbol) :
    Turing.ListBlank.mk (payload ++ [0, 0]) = Turing.ListBlank.mk (payload ++ [0]) := by
  exact Quotient.sound (Or.inr ⟨1, by simp [List.append_assoc]⟩)

def additionWiring (enabled : Bool) : Fin 3 ↪ Fin 5 where
  toFun name := if name = 0 then 2 else if name = 1 then (if enabled then 1 else 4) else 3
  inj' := by intro left right equal; cases enabled <;> fin_cases left <;> fin_cases right <;> simp_all

noncomputable def addition (enabled : Bool) : Machine Alphabet BinaryAddition.State :=
  wire (additionWiring enabled) BinaryAddition.machine

private theorem addition_steps (enabled : Bool) (multiplier : Turing.Tape Symbol)
    (shifted total output zeros : List Bool)
    (shiftedLength : shifted.length = total.length) (zeroLength : zeros.length = total.length)
    (outputLength : output.length = total.length) :
    Steps (addition enabled) (2 * total.length + 3)
      (.inl false, frame multiplier shifted total output zeros)
      (.inr 1, frame multiplier shifted total
        (BinaryAddition.add total (if enabled then shifted else zeros)) zeros) := by
  have selectedLength : (if enabled then shifted else zeros).length = total.length := by
    cases enabled <;> assumption
  apply wire_steps_of_eq (additionWiring enabled) _
    (BinaryAddition.steps total _ selectedLength (word output) (by simpa [word] using outputLength)
      [] [] [] [] [] [0])
  · intro name
    cases enabled <;> fin_cases name <;>
      simp [frame, additionWiring, tape, Binary.tape, BinaryAddition.frame]
  · intro name
    cases enabled <;> fin_cases name <;>
      simp [frame, additionWiring, tape, Binary.tape, BinaryAddition.frame]
  · intro name outside
    cases enabled <;> fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨0, rfl⟩)
      | exact False.elim (outside ⟨1, rfl⟩)
      | exact False.elim (outside ⟨2, rfl⟩)

noncomputable def selectAddition : Machine Alphabet
    (Sum (Sum Unit (Sum BinaryAddition.State BinaryAddition.State)) Unit) :=
  withExit (branchMachine (fun symbols => symbols 0 == 2)
    (addition true) (addition false) (.inl false) (.inl false))

private theorem selected_steps (bit : Bool) (before after shifted total output : List Bool)
    (shiftedLength : shifted.length = total.length) (outputLength : output.length = total.length) :
    let multiplier := Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ()
    Steps selectAddition (2 * total.length + 5)
      (.inl (.inl ()), frame multiplier shifted total output (List.replicate shifted.length false))
      (.inr (), frame multiplier shifted total
        (BinaryAddition.add total (if bit then shifted else List.replicate shifted.length false))
        (List.replicate shifted.length false)) := by
  dsimp only
  have zeroLength : (List.replicate shifted.length false).length = total.length := by
    simpa using shiftedLength
  cases bit with
  | false =>
    have trace := addition_steps false (Binary.tape (word before ++ [3]) (word (false :: after) ++ [0]) ()) shifted total output _ shiftedLength zeroLength outputLength
    convert branch_steps_false (fun symbols => symbols 0 == 2) (addition true) (addition false)
      (.inl false) (.inl false) (by simp [MultiTape.read, frame, Binary.tape, word, data])
      trace (by intro symbols; simp [addition, wire, BinaryAddition.machine]) using 1
    rfl
  | true =>
    have trace := addition_steps true (Binary.tape (word before ++ [3]) (word (true :: after) ++ [0]) ()) shifted total output _ shiftedLength zeroLength outputLength
    convert branch_steps_true (fun symbols => symbols 0 == 2) (addition true) (addition false)
      (.inl false) (.inl false) (by simp [MultiTape.read, frame, Binary.tape, word, data])
      trace (by intro symbols; simp [addition, wire, BinaryAddition.machine]) using 1
    rfl

noncomputable def saveSum : Machine Alphabet (Fin 3) :=
  wire (twoTapes (3 : Fin 5) 2 (by decide)) TerminatedCopy.machine

private theorem save_steps (multiplier : Turing.Tape Symbol) (shifted total output zeros : List Bool)
    (outputLength : output.length = total.length + 1) :
    Steps saveSum (2 * output.length + 3)
      (0, frame multiplier shifted total output zeros)
      (2, frame multiplier shifted output output zeros) := by
  apply wire_steps_of_eq (twoTapes (3 : Fin 5) 2 (by decide)) _
    (TerminatedCopy.steps output (word total ++ [0]) (by simp [word, outputLength]) [] [] [] [])
  · intro name
    cases name <;> simp [frame, tape, Binary.tape, Copy.frame, List.append_assoc]
  · intro name
    cases name <;> simp [frame, tape, Binary.tape, Copy.frame]
  · intro name outside
    fin_cases name <;> first
      | rfl
      | exact False.elim (outside ⟨false, rfl⟩)
      | exact False.elim (outside ⟨true, rfl⟩)

noncomputable def shiftAt (name : Fin 5) : Machine Alphabet (Fin 4) :=
  wire (oneTape name) shiftMachine

private theorem shift_multiplicand_steps (multiplier : Turing.Tape Symbol)
    (shifted total output zeros : List Bool) :
    Steps (shiftAt 1) 3 (0, frame multiplier shifted total output zeros)
      (3, frame multiplier (false :: shifted) total output zeros) := by
  apply wire_steps_of_eq (oneTape (1 : Fin 5)) _ (shift_steps shifted [0])
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)

private theorem shift_zeros_steps (multiplier : Turing.Tape Symbol)
    (shifted total output zeros : List Bool) :
    Steps (shiftAt 4) 3 (0, frame multiplier shifted total output zeros)
      (3, frame multiplier shifted total output (false :: zeros)) := by
  apply wire_steps_of_eq (oneTape (4 : Fin 5)) _ (shift_steps zeros [0])
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩)


def advance : Machine Alphabet Bool := fun finished symbols =>
  if finished then none else some (true,
    fun name => (symbols name, if name = 0 then some .right else none))

private theorem advance_steps (bit : Bool) (before after shifted total output zeros : List Bool) :
    Steps advance 1
      (false, frame (Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ())
        shifted total output zeros)
      (true, frame (Binary.tape (word (bit :: before) ++ [3]) (word after ++ [0]) ())
        shifted total output zeros) := by
  refine .next ?_ (.zero _)
  simp only [step, advance, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.some.injEq,
    Prod.mk.injEq, true_and]
  funext name
  fin_cases name <;>
    simp [act, MultiTape.read, frame, Binary.tape, word,
      Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]

abbrev SelectionState := Sum (Sum Unit (Sum BinaryAddition.State BinaryAddition.State)) Unit
abbrev BodyState := Sum (Sum (Sum (Sum SelectionState (Fin 3)) (Fin 4)) (Fin 4)) Bool

noncomputable def body : Machine Alphabet BodyState :=
  sequence (sequence (sequence (sequence selectAddition saveSum 0) (shiftAt 1) 0) (shiftAt 4) 0)
    advance false

def bodyEntry : BodyState := .inl (.inl (.inl (.inl (.inl (.inl ())))))
def bodyExit : BodyState := .inr true

private theorem body_halt (symbols : Symbols Alphabet) : body bodyExit symbols = none := by
  simp [body, bodyExit, MultiTape.sequence, advance]

private theorem body_steps (bit : Bool) (before after shifted total output : List Bool)
    (shiftedLength : shifted.length = total.length) (outputLength : output.length = total.length) :
    let updated := BinaryAddition.add total
      (if bit then shifted else List.replicate shifted.length false)
    Steps body (4 * total.length + 21)
      (bodyEntry, frame (Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ())
        shifted total output (List.replicate shifted.length false))
      (bodyExit, frame (Binary.tape (word (bit :: before) ++ [3]) (word after ++ [0]) ())
        (false :: shifted) updated updated (List.replicate (shifted.length + 1) false)) := by
  dsimp only
  let updated := BinaryAddition.add total
    (if bit then shifted else List.replicate shifted.length false)
  have updatedLength : updated.length = total.length + 1 :=
    BinaryAddition.add_length total _ (by cases bit <;> simp [shiftedLength])
  have selected := selected_steps bit before after shifted total output shiftedLength outputLength
  have saved := save_steps (Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ())
    shifted total updated (List.replicate shifted.length false) updatedLength
  have shiftedA := shift_multiplicand_steps (Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ())
    shifted updated updated (List.replicate shifted.length false)
  have shiftedZero := shift_zeros_steps (Binary.tape (word before ++ [3]) (word (bit :: after) ++ [0]) ())
    (false :: shifted) updated updated (List.replicate shifted.length false)
  have moved := advance_steps bit before after (false :: shifted) updated updated
    (false :: List.replicate shifted.length false)
  have first := sequence_steps _ _ 0 selected (by intro symbols; rfl) saved
  have second := sequence_steps _ _ 0 first
    (by intro symbols; simp [MultiTape.sequence, saveSum, wire, TerminatedCopy.machine]) shiftedA
  have third := sequence_steps _ _ 0 second
    (by intro symbols; simp [MultiTape.sequence, shiftAt, wire, shiftMachine]) shiftedZero
  have complete := sequence_steps _ _ false third
    (by intro symbols; simp [MultiTape.sequence, shiftAt, wire, shiftMachine]) moved
  convert complete using 1 <;> first
    | rfl
    | omega


def guard : Machine Alphabet Unit := fun _ _ => none

def hasDigit (symbols : Symbols Alphabet) : Bool := symbols 0 != 0

abbrev State := Sum (Sum Unit BodyState) Unit

noncomputable def machine : Machine Alphabet State :=
  withExit (whileMachine guard body () bodyEntry hasDigit)

def entry : State := .inl (.inl ())
def exit : State := .inr ()

private theorem loop_steps (bits before shifted total output : List Bool)
    (shiftedLength : shifted.length = total.length) (outputLength : output.length = total.length) :
    ∃ ticks finalOutput,
      ticks ≤ bits.length * (4 * (total.length + bits.length) + 23) ∧
      finalOutput.length = (accumulate shifted total bits).length ∧
      Steps (whileMachine guard body () bodyEntry hasDigit) ticks
        (.inl (), frame (Binary.tape (word before ++ [3]) (word bits ++ [0]) ())
          shifted total output (List.replicate shifted.length false))
        (.inl (), frame (Binary.tape (word (bits.reverse ++ before) ++ [3]) [0] ())
          (List.replicate bits.length false ++ shifted) (accumulate shifted total bits) finalOutput
          (List.replicate (shifted.length + bits.length) false)) := by
  induction bits generalizing before shifted total output with
  | nil =>
    refine ⟨0, output, by simp, ?_, ?_⟩
    · simpa [accumulate] using outputLength
    · simpa [accumulate, word] using Steps.zero
        (machine := whileMachine guard body () bodyEntry hasDigit)
        (.inl (), frame (Binary.tape (word before ++ [3]) [0] ())
          shifted total output (List.replicate shifted.length false))
  | cons bit bits hypothesis =>
    let updated := BinaryAddition.add total
      (if bit then shifted else List.replicate shifted.length false)
    have updatedLength : updated.length = total.length + 1 :=
      BinaryAddition.add_length total _ (by cases bit <;> simp [shiftedLength])
    have nextLength : (false :: shifted).length = updated.length := by
      rw [List.length_cons, shiftedLength, updatedLength]
    obtain ⟨ticks, finalOutput, cost, outputSize, rest⟩ :=
      hypothesis (bit :: before) (false :: shifted) updated updated nextLength rfl
    have started : step (whileMachine guard body () bodyEntry hasDigit)
        (.inl (), frame (Binary.tape (word before ++ [3]) (word (bit :: bits) ++ [0]) ())
          shifted total output (List.replicate shifted.length false)) =
        some (.inr bodyEntry, frame (Binary.tape (word before ++ [3]) (word (bit :: bits) ++ [0]) ())
          shifted total output (List.replicate shifted.length false)) := by
      have nonblank : data bit ≠ 0 := by cases bit <;> decide
      simp [step, whileMachine, guard, hasDigit, MultiTape.read, frame, Binary.tape, word, nonblank]
    have run := (body_steps bit before bits shifted total output shiftedLength outputLength).rename Sum.inr
      (target := whileMachine guard body () bodyEntry hasDigit)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    have returned : step (whileMachine guard body () bodyEntry hasDigit)
        (.inr bodyExit, frame (Binary.tape (word (bit :: before) ++ [3]) (word bits ++ [0]) ())
          (false :: shifted) updated updated (List.replicate (shifted.length + 1) false)) =
        some (.inl (), frame (Binary.tape (word (bit :: before) ++ [3]) (word bits ++ [0]) ())
          (false :: shifted) updated updated (List.replicate (shifted.length + 1) false)) := by
      simp [step, whileMachine, body_halt]
    simp only [List.length_cons] at rest
    have trace := Steps.next started (run.trans (Steps.next returned rest))
    refine ⟨4 * total.length + 21 + (ticks + 1) + 1, finalOutput, ?_, ?_, ?_⟩
    · simp only [List.length_cons, updatedLength] at cost ⊢
      nlinarith
    · exact outputSize
    · convert trace using 1
      simp [accumulate, updated, List.reverse_cons, List.append_assoc, word,
            List.replicate_succ', Nat.add_comm, Nat.add_left_comm]

/-- A complete multiplication loop with a polynomial bound in both digit counts.
All operands and buffers have runtime widths; the controller remains fixed. -/
theorem steps (shifted bits : List Bool) :
    ∃ ticks finalOutput,
      ticks ≤ bits.length * (4 * (shifted.length + bits.length) + 23) + 1 ∧
      finalOutput.length = shifted.length + bits.length ∧
      Steps machine ticks
        (entry, frame (tape bits) shifted (List.replicate shifted.length false)
          (List.replicate shifted.length false) (List.replicate shifted.length false))
        (exit, frame (Binary.tape (word bits.reverse ++ [3]) [0] ())
          (List.replicate bits.length false ++ shifted)
          (accumulate shifted (List.replicate shifted.length false) bits) finalOutput
          (List.replicate (shifted.length + bits.length) false)) := by
  obtain ⟨ticks, finalOutput, cost, outputSize, trace⟩ := loop_steps bits [] shifted
    (List.replicate shifted.length false) (List.replicate shifted.length false) (by simp) rfl
  have stopped : step (whileMachine guard body () bodyEntry hasDigit)
      (.inl (), frame (Binary.tape (word (bits.reverse ++ []) ++ [3]) [0] ())
        (List.replicate bits.length false ++ shifted)
        (accumulate shifted (List.replicate shifted.length false) bits) finalOutput
        (List.replicate (shifted.length + bits.length) false)) = none := by
    simp [step, whileMachine, guard, hasDigit, MultiTape.read, frame, Binary.tape]
  refine ⟨ticks + 1, finalOutput, ?_, ?_, ?_⟩
  · simpa using Nat.add_le_add_right cost 1
  · simpa [accumulate_length shifted (List.replicate shifted.length false) bits (by simp)] using outputSize
  · simpa [machine, entry, exit, tape, word] using withExit_steps _ trace stopped

/-- The machine computes the mathematical product within polynomial bit capacity. -/
theorem contract :
    Computes machine entry exit
      (fun _sizes : Bool → ℕ => fun (operands : List Bool × List Bool) tapes =>
        tapes = frame (tape operands.2) operands.1 (List.replicate operands.1.length false)
          (List.replicate operands.1.length false) (List.replicate operands.1.length false))
      (fun sizes => fun result tapes => ∃ resultBits,
        value resultBits = result ∧ resultBits.length ≤ sizes false + sizes true ∧
          tapes 2 = tape resultBits)
      (fun sizes operands => operands.1.length ≤ sizes false ∧ operands.2.length ≤ sizes true)
      (fun _ operands => value operands.1 * value operands.2) := by
  refine ⟨by intro symbols; rfl,
    MvPolynomial.X true * (4 * (MvPolynomial.X false + MvPolynomial.X true) + 23) + 1, ?_⟩
  intro sizes operands initial valid represented
  subst initial
  obtain ⟨ticks, output, cost, outputLength, trace⟩ := steps operands.1 operands.2
  refine ⟨ticks, _, ?_, trace,
    accumulate operands.1 (List.replicate operands.1.length false) operands.2, ?_, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
    have inner : 4 * (operands.1.length + operands.2.length) + 23 ≤
        4 * (sizes false + sizes true) + 23 := by omega
    exact cost.trans (Nat.add_le_add_right (Nat.mul_le_mul valid.2 inner) 1)
  · simp [accumulate_value operands.1 (List.replicate operands.1.length false) operands.2 (by simp), zero_value]
  · rw [accumulate_length operands.1 (List.replicate operands.1.length false) operands.2 (by simp), List.length_replicate]
    omega
  · rfl

end Polytime2.BinaryMultiplication
