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


import Polytime2.TM0.Sweep

/-! # Marked tracks for a single-tape simulation

Each row stores one symbol and one head-marker bit per simulated tape. Every
track has exactly one marked row. Rows to the left and right of that marker
represent the corresponding two sides of the simulated tape; implicit blanks
extend beyond the finite interval. Head positions may differ between tracks.
-/

namespace Polytime2.Tracks

open MultiTape

-- tapeLevel: simulated tape names; symbolLevel: their individual alphabets.
-- parameterLevel: runtime sizes bounding the finite row interval.
universe tapeLevel symbolLevel parameterLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}

abbrev Row (Alphabet : TapeName → Type symbolLevel) := Symbols Alphabet × (TapeName → Bool)

/-- A single track represents a tape at its unique marked row. -/
def RepresentsAt [∀ name, Inhabited (Alphabet name)] (name : TapeName)
    (rows : List (Row Alphabet)) (tape : Turing.Tape (Alphabet name)) : Prop :=
  ∃ before current after,
    rows = before ++ current :: after ∧
    (∀ previous ∈ before, previous.2 name = false) ∧ current.2 name = true ∧
    (∀ following ∈ after, following.2 name = false) ∧
    tape = ⟨current.1 name,
      Turing.ListBlank.mk (before.reverse.map fun entry => entry.1 name),
      Turing.ListBlank.mk (after.map fun entry => entry.1 name)⟩

/-- A finite interval representing all tapes, with exactly one head per track. -/
def Represents [∀ name, Inhabited (Alphabet name)] (rows : List (Row Alphabet)) (tapes : Tapes Alphabet) : Prop :=
  ∀ name, RepresentsAt name rows (tapes name)

/-- Collect the marked symbols in finite controller memory, preserving every row. -/
def collect (memory : Symbols Alphabet) (entry : Row Alphabet) : Symbols Alphabet × Row Alphabet :=
  (fun name => if entry.2 name then entry.1 name else memory name, entry)

@[simp] theorem collect_rows (memory : Symbols Alphabet) (rows : List (Row Alphabet)) :
    (Sweep.run collect memory rows).2 = rows := by
  induction rows generalizing memory with
  | nil => rfl
  | cons entry rest hypothesis => simp [Sweep.run, collect, hypothesis]

private theorem collect_projection (memory : Symbols Alphabet) (rows : List (Row Alphabet))
    (name : TapeName) :
    (Sweep.run collect memory rows).1 name =
      rows.foldl (fun symbol entry => if entry.2 name then entry.1 name else symbol) (memory name) := by
  induction rows generalizing memory with
  | nil => rfl
  | cons entry rest hypothesis => simpa [Sweep.run, collect] using hypothesis (collect memory entry).1

private theorem fold_unmarked (name : TapeName) (rows : List (Row Alphabet))
    (unmarked : ∀ entry ∈ rows, entry.2 name = false) (symbol : Alphabet name) :
    rows.foldl (fun previous entry => if entry.2 name then entry.1 name else previous) symbol = symbol := by
  induction rows with
  | nil => rfl
  | cons entry rest hypothesis =>
    simp only [List.foldl_cons, unmarked entry (by simp), Bool.false_eq_true, ite_false]
    exact hypothesis (by intro row member; exact unmarked row (by simp [member]))

variable [∀ name, Inhabited (Alphabet name)]

/-- Changing other tracks cannot change the tape represented by this track. -/
theorem RepresentsAt.congr {name : TapeName} {rows newRows : List (Row Alphabet)}
    {tape : Turing.Tape (Alphabet name)} (represented : RepresentsAt name rows tape)
    (columns : newRows.map (fun entry => (entry.1 name, entry.2 name)) =
      rows.map (fun entry => (entry.1 name, entry.2 name))) : RepresentsAt name newRows tape := by
  obtain ⟨before, current, after, split, beforeUnmarked, marked, afterUnmarked, original⟩ := represented
  have splitColumns : newRows.map (fun entry => (entry.1 name, entry.2 name)) =
      before.map (fun entry => (entry.1 name, entry.2 name)) ++
        (current.1 name, current.2 name) :: after.map (fun entry => (entry.1 name, entry.2 name)) := by
    simp only [columns, split, List.map_append, List.map_cons]
  obtain ⟨newBefore, tail, newSplit, beforeColumns, tailColumns⟩ := List.map_eq_append_iff.mp splitColumns
  obtain ⟨newCurrent, newAfter, tailSplit, currentColumn, afterColumns⟩ := List.map_eq_cons_iff.mp tailColumns
  refine ⟨newBefore, newCurrent, newAfter, by rw [newSplit, tailSplit], ?_,
    (congrArg Prod.snd currentColumn).trans marked, ?_, ?_⟩
  · intro entry member
    have oldMember : (entry.1 name, entry.2 name) ∈ before.map (fun row => (row.1 name, row.2 name)) := by
      rw [← beforeColumns]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp oldMember
    exact (congrArg Prod.snd equal).symm.trans (beforeUnmarked old oldMember)
  · intro entry member
    have oldMember : (entry.1 name, entry.2 name) ∈ after.map (fun row => (row.1 name, row.2 name)) := by
      rw [← afterColumns]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    obtain ⟨old, oldMember, equal⟩ := List.mem_map.mp oldMember
    exact (congrArg Prod.snd equal).symm.trans (afterUnmarked old oldMember)
  · have beforeValues : newBefore.map (fun entry => entry.1 name) = before.map (fun entry => entry.1 name) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) beforeColumns
    have afterValues : newAfter.map (fun entry => entry.1 name) = after.map (fun entry => entry.1 name) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) afterColumns
    have headValue : newCurrent.1 name = current.1 name := congrArg Prod.fst currentColumn
    simpa only [headValue, List.map_reverse, beforeValues, afterValues] using original

/-- Reading the marked interval obtains exactly the symbols read by the source machine. -/
theorem collect_heads {rows : List (Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Represents rows tapes) (memory : Symbols Alphabet) :
    (Sweep.run collect memory rows).1 = MultiTape.read tapes := by
  funext name
  obtain ⟨before, current, after, split, beforeUnmarked, marked, afterUnmarked, tape⟩ := represented name
  rw [collect_projection, split, List.foldl_append, fold_unmarked name before beforeUnmarked,
    List.foldl_cons, marked, ite_eq_left rfl, fold_unmarked name after afterUnmarked]
  simp [MultiTape.read, tape]

/-- One blank, unmarked row extends every simulated track simultaneously. -/
def blank : Row Alphabet := (fun _ => default, fun _ => false)

theorem blank_append {Symbol : Type symbolLevel} [Inhabited Symbol] (word : List Symbol) :
    Turing.ListBlank.mk (word ++ [default]) = Turing.ListBlank.mk word := by
  exact Quotient.sound' (Or.inr ⟨1, by simp⟩)

/-- Blank margins provide a free adjacent position for either head movement.
This is a representation equality; physically creating the margins still needs
machine transitions in the simulator. -/
theorem Represents.pad {rows : List (Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Represents rows tapes) : Represents (blank :: rows ++ [blank]) tapes := by
  intro name
  obtain ⟨before, current, after, split, beforeUnmarked, marked, afterUnmarked, tape⟩ := represented name
  refine ⟨blank :: before, current, after ++ [blank], ?_, ?_, marked, ?_, ?_⟩
  · simp [split, List.append_assoc]
  · intro entry member
    rcases List.mem_cons.mp member with equal | member
    · subst entry; rfl
    · exact beforeUnmarked entry member
  · intro entry member
    rcases List.mem_append.mp member with member | member
    · exact afterUnmarked entry member
    · have equal : entry = blank := by simpa using member
      subst entry
      rfl
  · simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      blank, List.append_nil, blank_append] using tape

/-- Rewrite only the marked cell in each track. Marker positions are unchanged. -/
def write (values : Symbols Alphabet) (entry : Row Alphabet) : Row Alphabet :=
  (fun name => if entry.2 name then values name else entry.1 name, entry.2)

/-- The track-wise write pass realizes simultaneous source tape writes. -/
theorem Represents.write {rows : List (Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Represents rows tapes) (values : Symbols Alphabet) :
    Represents (rows.map (Tracks.write values)) (fun name => (tapes name).write (values name)) := by
  intro name
  obtain ⟨before, current, after, split, beforeUnmarked, marked, afterUnmarked, tape⟩ := represented name
  refine ⟨before.map (Tracks.write values), Tracks.write values current, after.map (Tracks.write values), ?_, ?_, marked, ?_, ?_⟩
  · simp [split]
  · intro entry member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact beforeUnmarked original originalMember
  · intro entry member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact afterUnmarked original originalMember
  · have beforeWords : (before.map (Tracks.write values)).reverse.map (fun entry => entry.1 name) =
        before.reverse.map (fun entry => entry.1 name) := by
      rw [← List.map_reverse, List.map_map]
      apply List.map_congr_left
      intro entry member
      simp [Tracks.write, beforeUnmarked entry (List.mem_reverse.mp member)]
    have afterWords : (after.map (Tracks.write values)).map (fun entry => entry.1 name) =
        after.map (fun entry => entry.1 name) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro entry member
      simp [Tracks.write, afterUnmarked entry member]
    dsimp only
    rw [beforeWords, afterWords, tape]
    simp [Tracks.write, marked, Turing.Tape.write]

/-- Values to write are finite runtime controller memory, not new specialization
parameters. The visitor and its machine are fixed before those values are known. -/
def writeVisit (values : Symbols Alphabet) (entry : Row Alphabet) : Symbols Alphabet × Row Alphabet :=
  (values, write values entry)

omit [∀ name, Inhabited (Alphabet name)] in
@[simp] theorem write_run (values : Symbols Alphabet) (rows : List (Row Alphabet)) :
    Sweep.run writeVisit values rows = (values, rows.map (Tracks.write values)) := by
  induction rows with
  | nil => rfl
  | cons entry rest hypothesis => simp [Sweep.run, writeVisit, hypothesis]

omit [∀ name, Inhabited (Alphabet name)] in
/-- A uniform physical sweep implementing the write phase of every source action. -/
theorem write_steps (values : Symbols Alphabet) (rows : List (Row Alphabet))
    (left right : List (Sweep.Alphabet (Row Alphabet))) :
    Steps (Sweep.machine writeVisit) (2 * rows.length + 3)
      (.inl (false, values), Sweep.tape (Sweep.leftMarker :: left)
        (rows.map Sweep.row ++ Sweep.rightMarker :: right))
      (.inr values, Sweep.tape (Sweep.leftMarker :: left)
        ((rows.map (Tracks.write values)).map Sweep.row ++ Sweep.rightMarker :: right)) := by
  simpa only [write_run] using Sweep.steps writeVisit values rows left right

/-- A concrete one-tape trace collecting all source heads, with the row interval unchanged. -/
theorem collect_steps {rows : List (Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Represents rows tapes) (memory : Symbols Alphabet)
    (left right : List (Sweep.Alphabet (Row Alphabet))) :
    Steps (Sweep.machine collect) (2 * rows.length + 3)
      (.inl (false, memory), Sweep.tape (Sweep.leftMarker :: left)
        (rows.map Sweep.row ++ Sweep.rightMarker :: right))
      (.inr (MultiTape.read tapes), Sweep.tape (Sweep.leftMarker :: left)
        (rows.map Sweep.row ++ Sweep.rightMarker :: right)) := by
  simpa only [collect_heads represented, collect_rows] using Sweep.steps collect memory rows left right

/-- Head collection has a polynomial TM0 certificate, for arbitrarily many rows
and fixed finite sets of tapes and symbols. -/
theorem collect_polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)]
    (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment (rows : List (Row Alphabet)) (tapes : Tapes Alphabet), Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∀ memory left right,
          ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
            (fun current => current.bind (Turing.TM0.step (SingleTape.compile (Sweep.machine collect))))^[ticks]
              (some (SingleTape.configuration (.inl (false, memory), Sweep.tape (Sweep.leftMarker :: left)
                (rows.map Sweep.row ++ Sweep.rightMarker :: right)))) =
              some (SingleTape.configuration (.inr (MultiTape.read tapes), Sweep.tape (Sweep.leftMarker :: left)
                (rows.map Sweep.row ++ Sweep.rightMarker :: right))) ∧
            Turing.TM0.step (SingleTape.compile (Sweep.machine collect))
              (SingleTape.configuration (.inr (MultiTape.read tapes), Sweep.tape (Sweep.leftMarker :: left)
                (rows.map Sweep.row ++ Sweep.rightMarker :: right))) = none := by
  classical
  obtain ⟨bound, runs⟩ := Sweep.polynomial_time (collect (Alphabet := Alphabet)) capacity
  refine ⟨bound, ?_⟩
  intro assignment rows tapes represented bounded memory left right
  simpa only [collect_heads represented, collect_rows] using runs assignment memory rows left right bounded

/-- The source write phase has one fixed finite controller and a uniform
polynomial TM0 bound, even though the values written vary at runtime. -/
theorem write_polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)]
    (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment (rows : List (Row Alphabet)) (tapes : Tapes Alphabet), Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∀ values left right,
          ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
            Represents (rows.map (Tracks.write values)) (fun name => (tapes name).write (values name)) ∧
            (fun current => current.bind (Turing.TM0.step (SingleTape.compile (Sweep.machine writeVisit))))^[ticks]
              (some (SingleTape.configuration (.inl (false, values), Sweep.tape (Sweep.leftMarker :: left)
                (rows.map Sweep.row ++ Sweep.rightMarker :: right)))) =
              some (SingleTape.configuration (.inr values, Sweep.tape (Sweep.leftMarker :: left)
                ((rows.map (Tracks.write values)).map Sweep.row ++ Sweep.rightMarker :: right))) ∧
            Turing.TM0.step (SingleTape.compile (Sweep.machine writeVisit))
              (SingleTape.configuration (.inr values, Sweep.tape (Sweep.leftMarker :: left)
                ((rows.map (Tracks.write values)).map Sweep.row ++ Sweep.rightMarker :: right))) = none := by
  classical
  obtain ⟨bound, runs⟩ := Sweep.polynomial_time (writeVisit (Alphabet := Alphabet)) capacity
  refine ⟨bound, ?_⟩
  intro assignment rows tapes represented bounded values left right
  obtain ⟨ticks, cost, trace, halted⟩ := runs assignment values rows left right bounded
  refine ⟨ticks, cost, represented.write values, ?_, ?_⟩
  · simpa only [write_run] using trace
  · simpa only [write_run] using halted

end Polytime2.Tracks
