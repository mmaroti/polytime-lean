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

import Polytime2.Sweep
import Polytime2.Binary

/-! # Extracting a standalone binary word from simulated tracks

Find the selected head, project its contiguous binary word, erase the remaining
frame, and restore the physical head. The temporary boundary is also erased;
only the canonical output letters remain on the tape. All work is counted.
-/

namespace Polytime2.TrackOutput

open MultiTape

-- rowLevel: one physical row, containing the symbols and head flags of all tracks.
universe rowLevel
variable {Row : Type rowLevel}

abbrev Symbol (Row : Type rowLevel) := Sweep.Alphabet Row

def word (encodeBit : Bool → Row) (bits : List Bool) : List (Symbol Row) :=
  bits.map (Sweep.row ∘ encodeBit)

def machine (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row) :
    Machine (fun _ : Unit => Symbol Row) (Fin 8) := fun phase symbols =>
  let current := symbols ()
  match phase.val with
  | 0 => some (1, fun _ => (current, some .left))
  | 1 => some (2, fun _ => (none, some .right))
  | 2 => match current with
    | some (.inr row) => if selected row then some (3, fun _ => (current, some .left))
        else some (2, fun _ => (none, some .right))
    | _ => some (2, fun _ => (none, some .right))
  | 3 => some (4, fun _ => (Sweep.leftMarker, some .right))
  | 4 => match current with
    | some (.inr row) => if value row = 0 then some (5, fun _ => (none, some .right))
        else some (4, fun _ => (Sweep.row (encodeBit (decide (value row = 2))), some .right))
    | _ => some (6, fun _ => (none, some .right))
  | 5 => match current with
    | some (.inl true) => some (6, fun _ => (none, some .right))
    | _ => some (5, fun _ => (none, some .right))
  | 6 => if Sweep.isLeft current then some (7, fun _ => (none, some .right))
      else some (6, fun _ => (current, some .left))
  | _ => none

@[simp] private theorem mk_none : Turing.ListBlank.mk [(none : Symbol Row)] = Turing.ListBlank.mk [] :=
  Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

private theorem isLeft_false (current : Symbol Row) (different : current ≠ Sweep.leftMarker) :
    Sweep.isLeft current = false := by
  cases current with
  | none => rfl
  | some current => cases current with
    | inl marker => cases marker <;> simp_all [Sweep.isLeft, Sweep.leftMarker]
    | inr row => rfl

/-- Appended blank cells do not change a tape word. -/
theorem mk_append_blanks {Alphabet : Type rowLevel} [Inhabited Alphabet] (payload : List Alphabet) (count : ℕ) :
    Turing.ListBlank.mk (payload ++ List.replicate count default) = Turing.ListBlank.mk payload :=
  Quotient.sound (Or.inr ⟨count, rfl⟩)

private theorem start_steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (rows : List Row) :
    Steps (machine selected value encodeBit) 2
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (2, Sweep.tape [] (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
  refine Steps.next (middle := (1, Sweep.tape [] (Sweep.leftMarker :: (rows.map Sweep.row ++ [Sweep.rightMarker]))))
    ?_ (.next ?_ (.zero _))
  · cases rows <;> simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row, Sweep.leftMarker, Sweep.rightMarker] <;>
    funext name <;>
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk,
      Sweep.Alphabet]
  · simp [step, machine, Sweep.leftMarker, Sweep.rightMarker]
    funext name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk,
      Sweep.Alphabet]

private theorem search_steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (before : List Row) (current : Row) (after : List Row)
    (unmarked : ∀ row ∈ before, selected row = false) (marked : selected current = true) :
    Steps (machine selected value encodeBit) (before.length + 2)
      (2, Sweep.tape [] ((before ++ current :: after).map Sweep.row ++ [Sweep.rightMarker]))
      (4, Sweep.tape [Sweep.leftMarker] ((current :: after).map Sweep.row ++ [Sweep.rightMarker])) := by
  induction before with
  | nil =>
    refine Steps.next (middle := (3, Sweep.tape [] (none :: (current :: after).map Sweep.row ++ [Sweep.rightMarker])))
      ?_ (.next ?_ (.zero _))
    · simp [step, machine, MultiTape.read, Sweep.tape, marked, Sweep.row, Sweep.rightMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk,
        Sweep.Alphabet, default]
    · simp [step, machine, Sweep.row, Sweep.leftMarker, Sweep.rightMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk, Sweep.Alphabet]
  | cons row before hypothesis =>
    have first : step (machine selected value encodeBit)
        (2, Sweep.tape [] (((row :: before) ++ current :: after).map Sweep.row ++ [Sweep.rightMarker])) =
        some (2, Sweep.tape [] ((before ++ current :: after).map Sweep.row ++ [Sweep.rightMarker])) := by
      simp [step, machine, MultiTape.read, Sweep.tape, unmarked row (by simp),
        Sweep.row, Sweep.rightMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
    have rest := hypothesis (by intro other member; exact unmarked other (by simp [member]))
    simpa using Steps.next first rest

private theorem erase_steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (rows : List Row) (left : List (Symbol Row)) :
    Steps (machine selected value encodeBit) (rows.length + 1)
      (5, Sweep.tape left (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (6, Sweep.tape (List.replicate (rows.length + 1) none ++ left) [none]) := by
  induction rows generalizing left with
  | nil =>
    refine .next ?_ (.zero _)
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.rightMarker]
    funext name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk,
      Symbol, Sweep.Alphabet, default]
  | cons row rows hypothesis =>
    have first : step (machine selected value encodeBit)
        (5, Sweep.tape left ((row :: rows).map Sweep.row ++ [Sweep.rightMarker])) =
        some (5, Sweep.tape (none :: left) (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
      simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row, Sweep.rightMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
    have rest := hypothesis (none :: left)
    have commute (count : ℕ) : List.replicate count (none : Symbol Row) ++ none :: left =
        List.replicate (count + 1) none ++ left := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    simpa [commute] using Steps.next first rest

private theorem project_steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (rows : List Row) (bits : List Bool) (left : List (Symbol Row))
    (encoded : Turing.ListBlank.mk (rows.map value) = Turing.ListBlank.mk (Binary.word bits)) :
    bits.length ≤ rows.length ∧
    Steps (machine selected value encodeBit) (rows.length + 1)
      (4, Sweep.tape left (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (6, Sweep.tape (List.replicate (rows.length - bits.length + 1) none ++ (word encodeBit bits).reverse ++ left) [none]) := by
  induction bits generalizing rows left with
  | nil =>
    constructor
    · exact Nat.zero_le _
    · cases rows with
      | nil =>
        refine .next ?_ (.zero _)
        simp [step, machine, MultiTape.read, Sweep.tape, Sweep.rightMarker, word]
        funext name
        simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
          Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet, default]
      | cons row rows =>
        have zero : value row = 0 := by
          have heads := congrArg Turing.ListBlank.head encoded
          simpa [Binary.word] using heads
        have first : step (machine selected value encodeBit)
            (4, Sweep.tape left ((row :: rows).map Sweep.row ++ [Sweep.rightMarker])) =
            some (5, Sweep.tape (none :: left) (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
          simp [step, machine, MultiTape.read, Sweep.tape, zero, Sweep.row, Sweep.rightMarker]
          funext name
          simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
            Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
        have rest := erase_steps selected value encodeBit rows (none :: left)
        have commute (count : ℕ) : List.replicate count (none : Symbol Row) ++ none :: left =
            List.replicate (count + 1) none ++ left := by
          rw [List.replicate_succ', List.append_assoc]; rfl
        simpa [word, commute] using Steps.next first rest
  | cons bit bits hypothesis =>
    cases rows with
    | nil =>
      have heads := congrArg Turing.ListBlank.head encoded
      cases bit <;> simp [Binary.word, Binary.data] at heads
    | cons row rows =>
      have head : value row = Binary.data bit := by
        have heads := congrArg Turing.ListBlank.head encoded
        simpa [Binary.word] using heads
      have tail : Turing.ListBlank.mk (rows.map value) = Turing.ListBlank.mk (Binary.word bits) := by
        have tails := congrArg Turing.ListBlank.tail encoded
        simpa [Binary.word] using tails
      obtain ⟨length, rest⟩ := hypothesis rows (Sweep.row (encodeBit bit) :: left) tail
      refine ⟨by simpa using Nat.succ_le_succ length, ?_⟩
      have first : step (machine selected value encodeBit)
          (4, Sweep.tape left ((row :: rows).map Sweep.row ++ [Sweep.rightMarker])) =
          some (4, Sweep.tape (Sweep.row (encodeBit bit) :: left) (rows.map Sweep.row ++ [Sweep.rightMarker])) := by
        cases bit <;> simp [step, machine, MultiTape.read, Sweep.tape, head, Binary.data,
          Sweep.row, Sweep.rightMarker] <;>
          funext name <;>
          simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
            Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
      simpa [word, List.reverse_cons, List.append_assoc] using Steps.next first rest

private theorem rewind_steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (payload : List (Symbol Row)) (noMarker : ∀ symbol ∈ payload, symbol ≠ Sweep.leftMarker)
    (current : Symbol Row) (different : current ≠ Sweep.leftMarker) (right : List (Symbol Row)) :
    Steps (machine selected value encodeBit) (payload.length + 2)
      (6, Sweep.tape (payload ++ [Sweep.leftMarker]) (current :: right))
      (7, Sweep.tape [] (payload.reverse ++ current :: right)) := by
  induction payload generalizing current right with
  | nil =>
    refine Steps.next (middle := (6, Sweep.tape [] (Sweep.leftMarker :: current :: right)))
      ?_ (.next ?_ (.zero _))
    · simp [step, machine, MultiTape.read, Sweep.tape, isLeft_false current different,
        Sweep.leftMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        Turing.ListBlank.cons_mk, Sweep.Alphabet]
    · simp [step, machine, MultiTape.read, Sweep.tape,
        Sweep.leftMarker, Sweep.isLeft]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
        Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
  | cons symbol payload hypothesis =>
    have first : step (machine selected value encodeBit)
        (6, Sweep.tape ((symbol :: payload) ++ [Sweep.leftMarker]) (current :: right)) =
        some (6, Sweep.tape (payload ++ [Sweep.leftMarker]) (symbol :: current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, isLeft_false current different,
        Sweep.leftMarker]
      funext name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk',
        Turing.ListBlank.cons_mk, Symbol, Sweep.Alphabet]
    have rest := hypothesis (by intro other member; exact noMarker other (by simp [member]))
      symbol (noMarker symbol (by simp)) (current :: right)
    simpa [List.reverse_cons, List.append_assoc] using Steps.next first rest

/-- Extract and erase a whole frame in linear time, including an empty output. -/
theorem steps (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (before : List Row) (current : Row) (after : List Row) (bits : List Bool)
    (unmarked : ∀ row ∈ before, selected row = false) (marked : selected current = true)
    (encoded : Turing.ListBlank.mk ((current :: after).map value) = Turing.ListBlank.mk (Binary.word bits)) :
    ∃ ticks, ticks ≤ 2 * (before ++ current :: after).length + 8 ∧
      Steps (machine selected value encodeBit) ticks
        (0, Sweep.tape [Sweep.leftMarker] ((before ++ current :: after).map Sweep.row ++ [Sweep.rightMarker]))
        (7, Sweep.tape [] (word encodeBit bits)) := by
  have started := start_steps selected value encodeBit (before ++ current :: after)
  have found := search_steps selected value encodeBit before current after unmarked marked
  obtain ⟨length, projected⟩ := project_steps selected value encodeBit (current :: after) bits [Sweep.leftMarker] encoded
  let payload := List.replicate ((current :: after).length - bits.length + 1) (none : Symbol Row) ++ (word encodeBit bits).reverse
  have noMarker : ∀ symbol ∈ payload, symbol ≠ Sweep.leftMarker := by
    intro symbol member
    rcases List.mem_append.mp member with blank | code
    · have equal := List.eq_of_mem_replicate blank
      subst symbol
      simp [Sweep.leftMarker]
    · obtain ⟨bit, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp code)
      simp [Sweep.row, Sweep.leftMarker]
  have restored := rewind_steps selected value encodeBit payload noMarker none (by simp [Sweep.leftMarker]) []
  have erased : Sweep.tape [] (payload.reverse ++ [none]) = Sweep.tape [] (word encodeBit bits) := by
    funext name
    simp only [payload, List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.append_assoc]
    change Turing.Tape.mk' _ (Turing.ListBlank.mk (word encodeBit bits ++ (List.replicate _ none ++ [none]))) =
      Turing.Tape.mk' _ (Turing.ListBlank.mk (word encodeBit bits))
    rw [← List.replicate_succ']
    exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk [])) (mk_append_blanks (word encodeBit bits) _)
  rw [erased] at restored
  have complete := started.trans (found.trans (projected.trans restored))
  refine ⟨_, ?_, complete⟩
  simp only [payload, List.length_append, List.length_replicate, List.length_reverse, word, List.length_map] at length ⊢
  omega

theorem halt (selected : Row → Bool) (value : Row → Binary.Symbol) (encodeBit : Bool → Row)
    (symbols : Symbols (fun _ : Unit => Symbol Row)) : machine selected value encodeBit 7 symbols = none := rfl

end Polytime2.TrackOutput
