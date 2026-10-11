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

import Polytime2.Binary
import Polytime2.Head
import Polytime2.HeadTable
import Polytime2.Copy

/-! # Polynomially bounded unary counters

Counters use one digit per unit. Increment consumes one reserved zero cell;
reset clears all live digits. Both preserve surrounding storage and restore
the head. These counters are used for matrix addresses and loop indices.
-/

namespace Polytime2.Unary

open MultiTape
open Binary (Symbol tape)

private theorem replicate_cons (count : ℕ) (symbol : Symbol) (left : List Symbol) :
    List.replicate count symbol ++ symbol :: left = symbol :: (List.replicate count symbol ++ left) := by
  induction count with
  | zero => rfl
  | succ count hypothesis => simp [List.replicate_succ, hypothesis]

def scanEnd : Machine (fun _ : Unit => Symbol) (Fin 2) := fun state symbols =>
  if state = 0 then
    if symbols () = 0 then some (1, stationary symbols)
    else some (0, fun _ => (symbols (), some .right))
  else none

theorem scanEnd_steps (count : ℕ) (left right : List Symbol) :
    Steps scanEnd (count + 1)
      (0, tape left (List.replicate count 2 ++ 0 :: right))
      (1, tape (List.replicate count 2 ++ left) (0 :: right)) := by
  induction count generalizing left with
  | zero =>
    refine .next ?_ (.zero _)
    simp [step, scanEnd, MultiTape.read, tape]
  | succ count hypothesis =>
    have first : step scanEnd (0, tape left (List.replicate (count + 1) 2 ++ 0 :: right)) =
        some (0, tape (2 :: left) (List.replicate count 2 ++ 0 :: right)) := by
      simp only [step, scanEnd, ↓reduceIte, MultiTape.read, tape, List.replicate_succ,
        List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        show (2 : Symbol) ≠ 0 by decide, Option.map_some]
      congr 2
    simpa [List.replicate_succ, replicate_cons, Nat.add_assoc] using Steps.next first (hypothesis (2 :: left))

abbrev DecrementState := Sum (Sum (Sum (Fin 2) (Fin 2)) Bool) (Fin 2)

/-- Scan to the end, erase the last digit, then return to the left boundary. -/
def decrement : Machine (fun _ : Unit => Symbol) DecrementState :=
  sequence (sequence (sequence scanEnd (Move.machine 1 .left) 1)
    (HeadTable.machine (fun _ _ => 0)) false) BoundaryReturn.machine 0

theorem decrement_steps (count : ℕ) (left right : List Symbol) :
    Steps decrement (2 * (count + 1) + 7)
      (.inl (.inl (.inl 0)), tape (3 :: left) (List.replicate (count + 1) 2 ++ 0 :: right))
      (.inr 1, tape (3 :: left) (List.replicate count 2 ++ 0 :: 0 :: right)) := by
  have scanned := scanEnd_steps (count + 1) (3 :: left) right
  have moved : Steps (Move.machine 1 .left) 1
      (1, tape (List.replicate (count + 1) 2 ++ 3 :: left) (0 :: right))
      (0, tape (List.replicate count 2 ++ 3 :: left) (2 :: 0 :: right)) := by
    have trace := Move.steps 1 .left (tape (List.replicate (count + 1) 2 ++ 3 :: left) (0 :: right))
    have movedTape : (fun name : Unit => (Turing.Tape.move .left)^[1]
        (tape (List.replicate (count + 1) 2 ++ 3 :: left) (0 :: right) name)) =
        tape (List.replicate count 2 ++ 3 :: left) (2 :: 0 :: right) := by
      funext name
      simp [Binary.tape, List.replicate_succ, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    rw [movedTape] at trace
    exact trace
  have erased : Steps (HeadTable.machine (fun _ _ => (0 : Symbol))) 1
      (false, tape (List.replicate count 2 ++ 3 :: left) (2 :: 0 :: right))
      (true, tape (List.replicate count 2 ++ 3 :: left) (0 :: 0 :: right)) := by
    convert HeadTable.steps (fun _ _ => (0 : Symbol))
      (tape (List.replicate count 2 ++ 3 :: left) (2 :: 0 :: right)) using 1
    rfl
  have restored : Steps BoundaryReturn.machine (count + 2)
      (0, tape (List.replicate count 2 ++ 3 :: left) (0 :: 0 :: right))
      (1, tape (3 :: left) (List.replicate count 2 ++ 0 :: 0 :: right)) := by
    simpa [Binary.word, Binary.data] using
      BoundaryReturn.steps (List.replicate count true) 0 (by decide) left (0 :: right)
  have first := sequence_steps scanEnd (Move.machine 1 .left) 1 scanned
    (by intro symbols; simp [scanEnd]) moved
  have second := sequence_steps (sequence scanEnd (Move.machine 1 .left) 1)
    (HeadTable.machine (fun _ _ => (0 : Symbol))) false first
    (by intro symbols; simp [MultiTape.sequence, Move.machine]) erased
  have complete := sequence_steps _ BoundaryReturn.machine 0 second
    (by intro symbols; simp [MultiTape.sequence, HeadTable.machine]) restored
  convert complete using 1 <;> first | rfl | omega

/-- A canonical unary counter exposes nonzeroness under its initial head. -/
def guard : Machine (fun _ : Bool => Symbol) Bool :=
  HeadTable.machine (fun symbols name =>
    if name then Binary.data (decide (symbols false = 2)) else symbols false)

theorem guard_steps (count : ℕ) (left right flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps guard 1
      (false, Copy.frame (3 :: left) (List.replicate count 2 ++ 0 :: right) flagLeft (oldFlag :: flagRight))
      (true, Copy.frame (3 :: left) (List.replicate count 2 ++ 0 :: right)
        flagLeft (Binary.data (decide (0 < count)) :: flagRight)) := by
  have trace := HeadTable.steps
    (fun (symbols : Bool → Symbol) name => if name then Binary.data (decide (symbols false = 2)) else symbols false)
    (Copy.frame (3 :: left) (List.replicate count 2 ++ 0 :: right) flagLeft (oldFlag :: flagRight))
  convert trace using 1 <;> first
  | rfl
  | (congr 1
     funext name
     cases name <;> cases count <;>
       simp [Copy.frame, MultiTape.read, List.replicate_succ, Turing.Tape.write_mk', Turing.ListBlank.cons_mk])

def machine (reset : Bool) : Machine (fun _ : Unit => Symbol) (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => if symbols () = 0 then
      some (1, fun _ => (if reset then 0 else 2, none))
    else some (0, fun _ => (if reset then 0 else symbols (), some .right))
  | 1 => if symbols () = 3 then some (2, fun _ => (3, some .right))
    else some (1, fun _ => (symbols (), some .left))
  | _ => none

private theorem forward (reset : Bool) (count : ℕ) (left right : List Symbol) :
    Steps (machine reset) count
      (0, tape left (List.replicate count 2 ++ right))
      (0, tape (List.replicate count (if reset then 0 else 2) ++ left) right) := by
  induction count generalizing left with
  | zero => simpa using Steps.zero (machine := machine reset) (0, tape left right)
  | succ count hypothesis =>
    have first : step (machine reset) (0, tape left (List.replicate (count + 1) 2 ++ right)) =
        some (0, tape ((if reset then 0 else 2) :: left) (List.replicate count 2 ++ right)) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, tape, List.replicate_succ,
        List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        show (2 : Symbol) ≠ 0 by decide, ↓reduceIte, Option.map_some]
      congr 2
    simpa [List.replicate_succ, replicate_cons] using Steps.next first (hypothesis ((if reset then 0 else 2) :: left))

private theorem rewind (reset : Bool) (preceding : List Symbol)
    (valid : ∀ symbol ∈ preceding, symbol ≠ 3) (current : Symbol) (notBoundary : current ≠ 3)
    (left right : List Symbol) :
    Steps (machine reset) (preceding.length + 2)
      (1, tape (preceding ++ 3 :: left) (current :: right))
      (2, tape (3 :: left) (preceding.reverse ++ current :: right)) := by
  induction preceding generalizing current right with
  | nil =>
    have first : step (machine reset) (1, tape (3 :: left) (current :: right)) =
        some (1, tape left (3 :: current :: right)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
    have second : step (machine reset) (1, tape left (3 :: current :: right)) =
        some (2, tape (3 :: left) (current :: right)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
    simpa using Steps.next first (Steps.next second (.zero _))
  | cons symbol preceding hypothesis =>
    have first : step (machine reset) (1, tape (symbol :: preceding ++ 3 :: left) (current :: right)) =
        some (1, tape (preceding ++ 3 :: left) (symbol :: current :: right)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
    have rest := hypothesis (by intro value member; exact valid value (by simp [member]))
      symbol (valid symbol (by simp)) (current :: right)
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

theorem increment_steps (count : ℕ) (left right : List Symbol) :
    Steps (machine false) (2 * count + 3)
      (0, tape (3 :: left) (List.replicate count 2 ++ 0 :: right))
      (2, tape (3 :: left) (List.replicate (count + 1) 2 ++ right)) := by
  have scanned := forward false count (3 :: left) (0 :: right)
  have increment : step (machine false)
      (0, tape (List.replicate count 2 ++ 3 :: left) (0 :: right)) =
      some (1, tape (List.replicate count 2 ++ 3 :: left) (2 :: right)) := by
    simp only [step, machine, Fin.val_zero, MultiTape.read, tape, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
    congr 2
  have restored := rewind false (List.replicate count 2)
    (by intro symbol member; have equal := List.mem_replicate.mp member; rcases equal with ⟨_, rfl⟩; decide)
    2 (by decide) left right
  have commute : List.replicate count (2 : Symbol) ++ 2 :: right =
      List.replicate (count + 1) 2 ++ right := by
    rw [List.replicate_succ', List.append_assoc]; rfl
  simp only [Bool.false_eq_true, ite_false] at scanned
  simpa [List.reverse_replicate, commute, Nat.add_assoc, Nat.two_mul] using
    scanned.trans (Steps.next increment restored)

theorem reset_steps (count : ℕ) (left right : List Symbol) :
    Steps (machine true) (2 * count + 3)
      (0, tape (3 :: left) (List.replicate count 2 ++ 0 :: right))
      (2, tape (3 :: left) (List.replicate count 0 ++ 0 :: right)) := by
  have scanned := forward true count (3 :: left) (0 :: right)
  have finish : step (machine true)
      (0, tape (List.replicate count 0 ++ 3 :: left) (0 :: right)) =
      some (1, tape (List.replicate count 0 ++ 3 :: left) (0 :: right)) := by
    rfl
  have restored := rewind true (List.replicate count 0)
    (by intro symbol member; have equal := List.mem_replicate.mp member; rcases equal with ⟨_, rfl⟩; decide)
    0 (by decide) left right
  simp only [ite_true] at scanned
  simpa [List.reverse_replicate, Nat.add_assoc, Nat.two_mul] using
    scanned.trans (Steps.next finish restored)

/-- Increment a standalone counter, retaining its explicit trailing blank. -/
theorem increment_counter_steps (count : ℕ) :
    Steps (machine false) (2 * count + 3)
      (0, tape [3] (List.replicate count 2 ++ [0]))
      (2, tape [3] (List.replicate (count + 1) 2 ++ [0])) := by
  have blank : Turing.ListBlank.mk (List.replicate (count + 1) (2 : Symbol) ++ [0]) =
      Turing.ListBlank.mk (List.replicate (count + 1) (2 : Symbol)) :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  have finalTape : tape [3] (List.replicate (count + 1) 2 ++ [0]) = tape [3] (List.replicate (count + 1) 2) := by
    funext name
    exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk [3])) blank
  rw [finalTape]
  simpa only [List.append_nil] using increment_steps count [] []

/-- Reset a standalone counter to its canonical zero representation. -/
theorem reset_counter_steps (count : ℕ) :
    Steps (machine true) (2 * count + 3)
      (0, tape [3] (List.replicate count 2 ++ [0])) (2, tape [3] [0]) := by
  have blank : Turing.ListBlank.mk (List.replicate count (0 : Symbol) ++ [0]) = Turing.ListBlank.mk [0] := by
    have zeros : Turing.ListBlank.mk (List.replicate count (0 : Symbol) ++ [0]) = Turing.ListBlank.mk [] :=
      Quotient.sound (Or.inr ⟨count + 1, by simp [List.replicate_succ']⟩)
    exact zeros.trans (Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])).symm
  have finalTape : tape [3] (List.replicate count 0 ++ [0]) = tape [3] [0] := by
    funext name
    exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk [3])) blank
  simpa only [finalTape] using reset_steps count [] []

-- parameterLevel: the runtime size names bounding counter values.
universe parameterLevel

theorem decrement_realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes decrement (.inl (.inl (.inl 0))) (.inr 1)
      (fun assignment initial => ∃ (count : ℕ) (left right : List Symbol),
        count + 1 ≤ MvPolynomial.eval assignment capacity ∧
        initial = tape (3 :: left) (List.replicate (count + 1) 2 ++ 0 :: right))
      (fun _ initial final => ∃ (count : ℕ) (left right : List Symbol),
        initial = tape (3 :: left) (List.replicate (count + 1) 2 ++ 0 :: right) ∧
        final = tape (3 :: left) (List.replicate count 2 ++ 0 :: 0 :: right)) := by
  refine ⟨by intro symbols; simp [decrement, MultiTape.sequence, BoundaryReturn.machine], 2 * capacity + 7, ?_⟩
  intro assignment initial valid
  obtain ⟨count, left, right, bounded, rfl⟩ := valid
  refine ⟨2 * (count + 1) + 7, _, ?_, decrement_steps count left right, count, left, right, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (reset : Bool) (capacity : MvPolynomial Parameter ℕ) :
    Realizes (machine reset) 0 2
      (fun assignment initial => ∃ (count : ℕ) (left right : List Symbol),
        count ≤ MvPolynomial.eval assignment capacity ∧
        initial = tape (3 :: left) (List.replicate count 2 ++ 0 :: right))
      (fun _ initial final => ∃ (count : ℕ) (left right : List Symbol),
        initial = tape (3 :: left) (List.replicate count 2 ++ 0 :: right) ∧
        final = tape (3 :: left)
          (if reset then List.replicate count 0 ++ 0 :: right else List.replicate (count + 1) 2 ++ right)) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨count, left, right, bounded, rfl⟩ := valid
  have trace : Steps (machine reset) (2 * count + 3)
      (0, tape (3 :: left) (List.replicate count 2 ++ 0 :: right))
      (2, tape (3 :: left)
        (if reset then List.replicate count 0 ++ 0 :: right else List.replicate (count + 1) 2 ++ right)) := by
    cases reset with
    | false => exact increment_steps count left right
    | true => exact reset_steps count left right
  refine ⟨2 * count + 3, _, ?_, trace, count, left, right, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.Unary
