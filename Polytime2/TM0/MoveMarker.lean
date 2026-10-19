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


import Polytime2.TM0.Tracks

/-! # Moving a selected track's head marker

A fixed finite controller scans to one selected marker, clears it, moves one
cell left or right, sets the marker there, and returns to the first row. Only
that track's marker bit changes; all payload symbols and other tracks survive.
The direction is runtime controller memory. Blank margins ensure the adjacent
cell is a row. Return-trace proofs follow `Polytime2/Sweep.lean`.
-/

namespace Polytime2.MoveMarker

open MultiTape

-- tapeLevel: simulated tape names; symbolLevel: their alphabets.
-- parameterLevel: runtime sizes bounding the row interval.
universe tapeLevel symbolLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel}

abbrev Controller := Sum (Bool × Fin 3) Unit

instance : Inhabited Controller := ⟨.inr ()⟩

/-- Change one marker bit, preserving every data symbol and all other markers. -/
def mark (selected : TapeName) (value : Bool) (entry : Tracks.Row Alphabet) : Tracks.Row Alphabet :=
  (entry.1, Function.update entry.2 selected value)

@[simp] theorem mark_selected (selected : TapeName) (value : Bool) (entry : Tracks.Row Alphabet) :
    (mark selected value entry).2 selected = value := by simp [mark]

@[simp] theorem mark_other (selected other : TapeName) (distinct : other ≠ selected)
    (value : Bool) (entry : Tracks.Row Alphabet) :
    (mark selected value entry).2 other = entry.2 other := by simp [mark, distinct]

/-- `true` moves right; `false` moves left. The selected track is fixed by wiring. -/
def machine (selected : TapeName) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) Controller
  | .inl (moveRight, phase), symbols => match phase.val, symbols () with
    | 0, some (.inr entry) =>
      if entry.2 selected then
        some (.inl (moveRight, 1), fun _ =>
          (Sweep.row (mark selected false entry), some (if moveRight then .right else .left)))
      else some (.inl (moveRight, 0), fun _ => (Sweep.row entry, some .right))
    | 1, some (.inr entry) =>
      some (.inl (false, 2), fun _ => (Sweep.row (mark selected true entry), none))
    | 2, symbol =>
      if Sweep.isLeft symbol then some (.inr (), fun _ => (Sweep.leftMarker, some .right))
      else some (.inl (false, 2), fun _ => (symbol, some .left))
    | _, _ => none
  | .inr (), _ => none

private theorem seek (selected : TapeName) (moveRight : Bool) (before : List (Tracks.Row Alphabet))
    (unmarked : ∀ entry ∈ before, entry.2 selected = false)
    (left right : List (Sweep.Alphabet (Tracks.Row Alphabet))) :
    Steps (machine selected) before.length
      (.inl (moveRight, 0), Sweep.tape left (before.map Sweep.row ++ right))
      (.inl (moveRight, 0), Sweep.tape (before.reverse.map Sweep.row ++ left) right) := by
  induction before generalizing left with
  | nil => exact .zero _
  | cons entry rest hypothesis =>
    have first : step (machine selected)
        (.inl (moveRight, 0), Sweep.tape left (Sweep.row entry :: (rest.map Sweep.row ++ right))) =
        some (.inl (moveRight, 0), Sweep.tape (Sweep.row entry :: left) (rest.map Sweep.row ++ right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row, unmarked entry (by simp)]
      congr 2
    have remaining := hypothesis (by intro row member; exact unmarked row (by simp [member]))
      (Sweep.row entry :: left)
    simpa [List.map_cons, List.cons_append, List.reverse_cons, List.map_append, List.append_assoc] using
      Steps.next first remaining

private theorem rewind (selected : TapeName) (before : List (Tracks.Row Alphabet))
    (current : Sweep.Alphabet (Tracks.Row Alphabet)) (notLeft : Sweep.isLeft current = false)
    (left right : List (Sweep.Alphabet (Tracks.Row Alphabet))) :
    Steps (machine selected) (before.length + 2)
      (.inl (false, 2), Sweep.tape (before.map Sweep.row ++ Sweep.leftMarker :: left) (current :: right))
      (.inr (), Sweep.tape (Sweep.leftMarker :: left) ((before.map Sweep.row).reverse ++ current :: right)) := by
  induction before generalizing current right with
  | nil =>
    have first : step (machine selected)
        (.inl (false, 2), Sweep.tape (Sweep.leftMarker :: left) (current :: right)) =
        some (.inl (false, 2), Sweep.tape left (Sweep.leftMarker :: current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine selected)
        (.inl (false, 2), Sweep.tape left (Sweep.leftMarker :: current :: right)) =
        some (.inr (), Sweep.tape (Sweep.leftMarker :: left) (current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, Sweep.leftMarker, Sweep.isLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    exact Steps.next first (Steps.next second (.zero _))
  | cons entry rest hypothesis =>
    have first : step (machine selected)
        (.inl (false, 2), Sweep.tape (Sweep.row entry :: (rest.map Sweep.row ++ Sweep.leftMarker :: left)) (current :: right)) =
        some (.inl (false, 2), Sweep.tape (rest.map Sweep.row ++ Sweep.leftMarker :: left) (Sweep.row entry :: current :: right)) := by
      simp [step, machine, MultiTape.read, Sweep.tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have remaining := hypothesis (Sweep.row entry) (by rfl) (current :: right)
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using Steps.next first remaining

/-- Move the selected marker one row right, preserving every payload symbol,
all other marker bits, and both neighboring regions; restore the physical head. -/
theorem right_steps (selected : TapeName) (before : List (Tracks.Row Alphabet))
    (current next : Tracks.Row Alphabet) (after : List (Tracks.Row Alphabet))
    (unmarked : ∀ entry ∈ before, entry.2 selected = false) (marked : current.2 selected = true)
    (left right : List (Sweep.Alphabet (Tracks.Row Alphabet))) :
    Steps (machine selected) (2 * before.length + 5)
      (.inl (true, 0), Sweep.tape (Sweep.leftMarker :: left)
        ((before ++ current :: next :: after).map Sweep.row ++ Sweep.rightMarker :: right))
      (.inr (), Sweep.tape (Sweep.leftMarker :: left)
        ((before ++ mark selected false current :: mark selected true next :: after).map Sweep.row ++
          Sweep.rightMarker :: right)) := by
  have scanned := seek selected true before unmarked (Sweep.leftMarker :: left)
    (Sweep.row current :: Sweep.row next :: (after.map Sweep.row ++ Sweep.rightMarker :: right))
  have clear : step (machine selected)
      (.inl (true, 0), Sweep.tape (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left)
        (Sweep.row current :: Sweep.row next :: (after.map Sweep.row ++ Sweep.rightMarker :: right))) =
      some (.inl (true, 1), Sweep.tape (Sweep.row (mark selected false current) ::
        (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left))
        (Sweep.row next :: (after.map Sweep.row ++ Sweep.rightMarker :: right))) := by
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row, marked]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have set : step (machine selected)
      (.inl (true, 1), Sweep.tape (Sweep.row (mark selected false current) ::
        (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left))
        (Sweep.row next :: (after.map Sweep.row ++ Sweep.rightMarker :: right))) =
      some (.inl (false, 2), Sweep.tape (Sweep.row (mark selected false current) ::
        (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left))
        (Sweep.row (mark selected true next) :: (after.map Sweep.row ++ Sweep.rightMarker :: right))) := by
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  have returned := rewind selected (mark selected false current :: before.reverse)
    (Sweep.row (mark selected true next)) (by rfl) left (after.map Sweep.row ++ Sweep.rightMarker :: right)
  have combined := scanned.trans (Steps.next clear (Steps.next set returned))
  convert combined using 1 <;>
    simp [List.map_append, List.map_cons, List.map_reverse, List.cons_append,
      List.reverse_cons, List.append_assoc]
  omega

/-- The symmetric left move needs an unmarked row immediately before the head. -/
theorem left_steps (selected : TapeName) (before : List (Tracks.Row Alphabet))
    (previous current : Tracks.Row Alphabet) (after : List (Tracks.Row Alphabet))
    (unmarked : ∀ entry ∈ before, entry.2 selected = false)
    (previousUnmarked : previous.2 selected = false) (marked : current.2 selected = true)
    (left right : List (Sweep.Alphabet (Tracks.Row Alphabet))) :
    Steps (machine selected) (2 * before.length + 5)
      (.inl (false, 0), Sweep.tape (Sweep.leftMarker :: left)
        ((before ++ previous :: current :: after).map Sweep.row ++ Sweep.rightMarker :: right))
      (.inr (), Sweep.tape (Sweep.leftMarker :: left)
        ((before ++ mark selected true previous :: mark selected false current :: after).map Sweep.row ++
          Sweep.rightMarker :: right)) := by
  have scanned := seek selected false (before ++ [previous]) (by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact unmarked entry member
    · simpa using (List.mem_singleton.mp member) ▸ previousUnmarked)
    (Sweep.leftMarker :: left) (Sweep.row current :: (after.map Sweep.row ++ Sweep.rightMarker :: right))
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.map_append,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append] at scanned
  have clear : step (machine selected)
      (.inl (false, 0), Sweep.tape (Sweep.row previous :: (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left))
        (Sweep.row current :: (after.map Sweep.row ++ Sweep.rightMarker :: right))) =
      some (.inl (false, 1), Sweep.tape (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left)
        (Sweep.row previous :: Sweep.row (mark selected false current) ::
          (after.map Sweep.row ++ Sweep.rightMarker :: right))) := by
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row, marked]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
  have set : step (machine selected)
      (.inl (false, 1), Sweep.tape (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left)
        (Sweep.row previous :: Sweep.row (mark selected false current) ::
          (after.map Sweep.row ++ Sweep.rightMarker :: right))) =
      some (.inl (false, 2), Sweep.tape (before.reverse.map Sweep.row ++ Sweep.leftMarker :: left)
        (Sweep.row (mark selected true previous) :: Sweep.row (mark selected false current) ::
          (after.map Sweep.row ++ Sweep.rightMarker :: right))) := by
    simp [step, machine, MultiTape.read, Sweep.tape, Sweep.row]
    funext name
    cases name
    simp [MultiTape.act, Sweep.tape, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  have returned := rewind selected before.reverse (Sweep.row (mark selected true previous))
    (by rfl) left (Sweep.row (mark selected false current) :: (after.map Sweep.row ++ Sweep.rightMarker :: right))
  have combined := scanned.trans (Steps.next clear (Steps.next set returned))
  convert combined using 1 <;>
    simp [List.map_append, List.map_cons, List.map_reverse, List.cons_append, List.append_assoc]
  omega

section Representation

variable [∀ name, Inhabited (Alphabet name)]

/-- The adjacent right-marker swap represents exactly a source head move. -/
theorem right_represents (selected : TapeName) (before : List (Tracks.Row Alphabet))
    (current next : Tracks.Row Alphabet) (after : List (Tracks.Row Alphabet)) (tapes : Tapes Alphabet)
    (represented : Tracks.Represents (before ++ current :: next :: after) tapes)
    (beforeUnmarked : ∀ entry ∈ before, entry.2 selected = false)
    (afterUnmarked : ∀ entry ∈ after, entry.2 selected = false)
    (source : tapes selected = ⟨current.1 selected,
      Turing.ListBlank.mk (before.reverse.map fun entry => entry.1 selected),
      Turing.ListBlank.mk ((next :: after).map fun entry => entry.1 selected)⟩) :
    Tracks.Represents (before ++ mark selected false current :: mark selected true next :: after)
      (Function.update tapes selected ((tapes selected).move .right)) := by
  intro name
  by_cases equal : name = selected
  · subst name
    rw [Function.update_self]
    refine ⟨before ++ [mark selected false current], mark selected true next, after,
      by simp, ?_, by simp, afterUnmarked, ?_⟩
    · intro entry member
      rcases List.mem_append.mp member with member | member
      · exact beforeUnmarked entry member
      · have equal : entry = mark selected false current := List.mem_singleton.mp member
        subst entry
        simp
    · simp [source, mark, Turing.Tape.move, List.reverse_append, Turing.ListBlank.cons_mk]
  · rw [Function.update_of_ne equal]
    apply (represented name).congr
    simp [List.map_append, mark, equal]

/-- The adjacent left-marker swap represents exactly a source head move. -/
theorem left_represents (selected : TapeName) (before : List (Tracks.Row Alphabet))
    (previous current : Tracks.Row Alphabet) (after : List (Tracks.Row Alphabet)) (tapes : Tapes Alphabet)
    (represented : Tracks.Represents (before ++ previous :: current :: after) tapes)
    (beforeUnmarked : ∀ entry ∈ before, entry.2 selected = false)
    (afterUnmarked : ∀ entry ∈ after, entry.2 selected = false)
    (source : tapes selected = ⟨current.1 selected,
      Turing.ListBlank.mk ((previous :: before.reverse).map fun entry => entry.1 selected),
      Turing.ListBlank.mk (after.map fun entry => entry.1 selected)⟩) :
    Tracks.Represents (before ++ mark selected true previous :: mark selected false current :: after)
      (Function.update tapes selected ((tapes selected).move .left)) := by
  intro name
  by_cases equal : name = selected
  · subst name
    rw [Function.update_self]
    refine ⟨before, mark selected true previous, mark selected false current :: after,
      rfl, beforeUnmarked, by simp, ?_, ?_⟩
    · intro entry member
      rcases List.mem_cons.mp member with equal | member
      · subst entry; simp
      · exact afterUnmarked entry member
    · simp [source, mark, Turing.Tape.move, Turing.ListBlank.cons_mk]
  · rw [Function.update_of_ne equal]
    apply (represented name).congr
    simp [List.map_append, mark, equal]

/-- Blank margins make a selected head move possible at every source position.
The input interval is already padded: this theorem charges for marker movement,
not for physically creating the two margins. -/
theorem padded_steps (selected : TapeName) (moveRight : Bool)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes)
    (left right : List (Sweep.Alphabet (Tracks.Row Alphabet))) :
    ∃ finalRows ticks, finalRows.length = rows.length + 2 ∧ ticks ≤ 2 * rows.length + 7 ∧
      Tracks.Represents finalRows (Function.update tapes selected
        ((tapes selected).move (if moveRight then .right else .left))) ∧
      Steps (machine selected) ticks
        (.inl (moveRight, 0), Sweep.tape (Sweep.leftMarker :: left)
          ((Tracks.blank :: rows ++ [Tracks.blank]).map Sweep.row ++ Sweep.rightMarker :: right))
        (.inr (), Sweep.tape (Sweep.leftMarker :: left)
          (finalRows.map Sweep.row ++ Sweep.rightMarker :: right)) := by
  obtain ⟨before, current, after, split, beforeUnmarked, marked, afterUnmarked, source⟩ := represented selected
  have input : Tracks.blank :: rows ++ [Tracks.blank] =
      (Tracks.blank :: before) ++ current :: (after ++ [Tracks.blank]) := by
    simp [split, List.append_assoc]
  have beforePadded : ∀ entry ∈ Tracks.blank :: before, entry.2 selected = false := by
    intro entry member
    rcases List.mem_cons.mp member with equal | member
    · subst entry; rfl
    · exact beforeUnmarked entry member
  have afterPadded : ∀ entry ∈ after ++ [Tracks.blank], entry.2 selected = false := by
    intro entry member
    rcases List.mem_append.mp member with member | member
    · exact afterUnmarked entry member
    · have equal : entry = Tracks.blank := List.mem_singleton.mp member
      subst entry; rfl
  have paddedSource : tapes selected = ⟨current.1 selected,
      Turing.ListBlank.mk ((Tracks.blank :: before).reverse.map fun entry => entry.1 selected),
      Turing.ListBlank.mk ((after ++ [Tracks.blank]).map fun (entry : Tracks.Row Alphabet) => entry.1 selected)⟩ := by
    simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, Tracks.blank,
      List.append_nil, Tracks.blank_append] using source
  have size := congrArg List.length split
  simp only [List.length_append, List.length_cons] at size
  cases moveRight with
  | true =>
    obtain ⟨next, tail, tailSplit⟩ := List.exists_cons_of_ne_nil (l := after ++ [Tracks.blank]) (by simp)
    have tailUnmarked : ∀ entry ∈ tail, entry.2 selected = false := by
      intro entry member
      apply afterPadded entry
      rw [tailSplit]
      simp [member]
    have trace := right_steps selected (Tracks.blank :: before) current next tail beforePadded marked left right
    have correct := right_represents selected (Tracks.blank :: before) current next tail tapes
      (by simpa only [← tailSplit, ← input] using represented.pad) beforePadded tailUnmarked
      (by simpa only [tailSplit] using paddedSource)
    refine ⟨(Tracks.blank :: before) ++ mark selected false current :: mark selected true next :: tail,
      2 * (Tracks.blank :: before).length + 5, ?_, ?_, ?_, ?_⟩
    · have tailSize := congrArg List.length tailSplit
      simp only [List.length_append, List.length_cons, List.length_nil] at tailSize ⊢
      omega
    · simp only [List.length_cons]; omega
    · simpa using correct
    · simpa only [← tailSplit, ← input] using trace
  | false =>
    obtain empty | ⟨preceding, previous, prefixSplit⟩ := List.eq_nil_or_concat' (Tracks.blank :: before)
    · simp at empty
    have prefixUnmarked : ∀ entry ∈ preceding, entry.2 selected = false := by
      intro entry member
      apply beforePadded entry
      rw [prefixSplit]
      simp [member]
    have previousUnmarked : previous.2 selected = false := by
      apply beforePadded previous
      rw [prefixSplit]
      simp
    have localInput : Tracks.blank :: rows ++ [Tracks.blank] =
        preceding ++ previous :: current :: (after ++ [Tracks.blank]) := by
      rw [input, prefixSplit]
      simp [List.append_assoc]
    have trace := left_steps selected preceding previous current (after ++ [Tracks.blank])
      prefixUnmarked previousUnmarked marked left right
    have correct := left_represents selected preceding previous current (after ++ [Tracks.blank]) tapes
      (by simpa only [← localInput] using represented.pad) prefixUnmarked afterPadded (by
        simpa only [prefixSplit, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append] using paddedSource)
    refine ⟨preceding ++ mark selected true previous :: mark selected false current :: (after ++ [Tracks.blank]),
      2 * preceding.length + 5, ?_, ?_, ?_, ?_⟩
    · have prefixSize := congrArg List.length prefixSplit
      simp only [List.length_append, List.length_cons, List.length_nil] at prefixSize ⊢
      omega
    · have prefixSize := congrArg List.length prefixSplit
      simp only [List.length_append, List.length_cons, List.length_nil] at prefixSize
      omega
    · simpa using correct
    · simpa only [← localInput] using trace

end Representation

/-- Polynomial TM0 realization of a selected source head movement. The two
blank margins must already be present; creating them is a separate routine. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)] [∀ name, Inhabited (Alphabet name)]
    (selected : TapeName) (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment (rows : List (Tracks.Row Alphabet)) tapes, Tracks.Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∀ moveRight left right,
          ∃ finalRows ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
            finalRows.length = rows.length + 2 ∧
            Tracks.Represents finalRows (Function.update tapes selected
              ((tapes selected).move (if moveRight then .right else .left))) ∧
            (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine selected))))^[ticks]
              (some (SingleTape.configuration (.inl (moveRight, 0), Sweep.tape (Sweep.leftMarker :: left)
                ((Tracks.blank :: rows ++ [Tracks.blank]).map Sweep.row ++ Sweep.rightMarker :: right)))) =
              some (SingleTape.configuration (.inr (), Sweep.tape (Sweep.leftMarker :: left)
                (finalRows.map Sweep.row ++ Sweep.rightMarker :: right))) ∧
            Turing.TM0.step (SingleTape.compile (machine selected))
              (SingleTape.configuration (.inr (), Sweep.tape (Sweep.leftMarker :: left)
                (finalRows.map Sweep.row ++ Sweep.rightMarker :: right))) = none := by
  refine ⟨4 * capacity + 14, ?_⟩
  intro assignment rows tapes represented bounded moveRight left right
  obtain ⟨finalRows, ticks, length, cost, correct, trace⟩ := padded_steps selected moveRight represented left right
  refine ⟨finalRows, 2 * ticks, ?_, length, correct, SingleTape.steps (machine selected) trace, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · exact SingleTape.halt (machine selected) _ (by rfl)

end Polytime2.MoveMarker
