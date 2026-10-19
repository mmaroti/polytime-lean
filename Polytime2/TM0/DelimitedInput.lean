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

import Polytime2.TM0.CallingConventionOutput

/-! # Preparing delimited input blocks for the finite-track simulator

A single sweep rewrites ordinary binary blocks and separators into tracks.
Each input head starts at its own block; all remaining tapes start blank at
one shared row. No runtime evaluator of encoded-domain widths is required.
-/

namespace Polytime2.DelimitedInput

open MultiTape CallingConvention

-- tapeLevel: the finite source tape catalogue; symbolLevel: external letters.
universe tapeLevel symbolLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]

/-- Binary digits, a separator, and the two framing delimiters. -/
abbrev Letter := Bool ⊕ Fin 3

/-- A fixed framing convention, including a leading separator and empty blocks. -/
def serialize {Symbol : Type symbolLevel} (letters : Letter → Symbol)
    (blocks : List (List Bool)) : List Symbol :=
  letters (.inr 1) :: letters (.inr 0) ::
    (blocks.flatMap (fun bits => bits.map (letters ∘ Sum.inl) ++ [letters (.inr 0)]) ++
      [letters (.inr 2)])

abbrev Row (TapeName : Type tapeLevel) := Tracks.Row (CallingConvention.Alphabet TapeName)

/-- The separator is distinct from both digit letters, even for an empty block. -/
def separator : Row TapeName := (fun _ => 0, fun _ => true)

def bit (anchor : TapeName) (value : Bool) : Row TapeName := outputLetter anchor value

def cell (name : TapeName) (value : Binary.Symbol) (marked : Bool) : Row TapeName :=
  ((fun other => if other = name then value else 0),
    fun other => if other = name then marked else false)

def initialRow (names : List TapeName) : Row TapeName :=
  (fun _ => 0, fun name => decide (name ∉ names))

def blockRows (name : TapeName) : Bool → List Bool → List (Row TapeName)
  | marked, [] => [cell name 0 marked]
  | marked, value :: rest => cell name (Binary.data value) marked :: blockRows name false rest

def rows (names : List TapeName) (bits : TapeName → List Bool) : List (Row TapeName) :=
  initialRow names :: names.flatMap (fun name => blockRows name true (bits name))

def rawBlocks (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    List (Row TapeName) :=
  names.flatMap (fun name => (bits name).map (bit anchor) ++ [separator])

def rawRows (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    List (Row TapeName) := separator :: rawBlocks anchor names bits

abbrev Memory (names : List TapeName) := Unit ⊕ (Fin (names.length + 1) × Bool)

/-- All parser state is finite and fixed by the program's input tape catalogue. -/
def visit (anchor : TapeName) (names : List TapeName) :
    Memory names → Row TapeName → Memory names × Row TapeName
  | .inl _, _ => (.inr (0, true), initialRow names)
  | .inr (index, marked), entry =>
    if within : index.val < names.length then
      let name := names[index.val]
      if entry.2 anchor then
        (.inr (⟨index.val + 1, by omega⟩, true), cell name 0 marked)
      else (.inr (index, false), cell name (entry.1 anchor) marked)
    else (.inr (index, marked), Tracks.blank)

def machine (anchor : TapeName) (names : List TapeName) := Sweep.machine (visit anchor names)

def entry (names : List TapeName) : Sweep.Controller (Memory names) := .inl (false, .inl ())
def exit (names : List TapeName) : Sweep.Controller (Memory names) :=
  .inr (.inr (Fin.last names.length, true))

private theorem run_append {Memory Row : Type*} (visitor : Memory → Row → Memory × Row)
    (memory : Memory) (first second : List Row) :
    Sweep.run visitor memory (first ++ second) =
      ((Sweep.run visitor (Sweep.run visitor memory first).1 second).1,
        (Sweep.run visitor memory first).2 ++
          (Sweep.run visitor (Sweep.run visitor memory first).1 second).2) := by
  induction first generalizing memory with
  | nil => rfl
  | cons current rest induction => simp [Sweep.run, induction]

private theorem run_block (anchor : TapeName) (names before after : List TapeName)
    (name : TapeName) (split : names = before ++ name :: after)
    (marked : Bool) (bits : List Bool) :
    Sweep.run (visit anchor names)
      (.inr (⟨before.length, by simp [split]⟩, marked))
      (bits.map (bit anchor) ++ [separator]) =
      (.inr (⟨before.length + 1, by simp [split]⟩, true), blockRows name marked bits) := by
  have within : before.length < names.length := by simp [split]
  have selected : names[before.length]'within = name := by simp [split]
  induction bits generalizing marked with
  | nil => simp [Sweep.run, visit, within, selected, separator, blockRows]
  | cons value rest induction =>
    simp [Sweep.run, visit, within, selected, bit, outputLetter, blockRows, induction]

private theorem run_blocks (anchor : TapeName) (names before after : List TapeName)
    (split : names = before ++ after) (bits : TapeName → List Bool) :
    Sweep.run (visit anchor names)
      (.inr (⟨before.length, by simp [split]⟩, true)) (rawBlocks anchor after bits) =
      (.inr (Fin.last names.length, true), after.flatMap (fun name => blockRows name true (bits name))) := by
  induction after generalizing before with
  | nil =>
    subst names
    simp [rawBlocks, Sweep.run, Fin.last]
  | cons name after induction =>
    have nextSplit : names = (before ++ [name]) ++ after := by simp [split, List.append_assoc]
    have next := induction (before ++ [name]) nextSplit
    simp only [rawBlocks, List.flatMap_cons]
    rw [run_append, run_block anchor names before after name split true (bits name)]
    simpa [rawBlocks, List.length_append, List.append_assoc] using
      congrArg (fun result => (result.1, blockRows name true (bits name) ++ result.2)) next

/-- The visitor realizes the complete functional preparation, including empty
blocks and a catalogue containing no input tapes. -/
theorem run (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    Sweep.run (visit anchor names) (.inl ()) (rawRows anchor names bits) =
      (.inr (Fin.last names.length, true), rows names bits) := by
  have prepared := run_blocks anchor names [] names (by simp) bits
  simpa [rawRows, Sweep.run, visit, rows] using
    congrArg (fun result => (result.1, initialRow names :: result.2)) prepared

/-- Preparation costs a linear number of one-tape write-and-move transitions. -/
theorem steps (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    Steps (machine anchor names) (2 * (rawRows anchor names bits).length + 3)
      (entry names, Sweep.tape [Sweep.leftMarker]
        ((rawRows anchor names bits).map Sweep.row ++ [Sweep.rightMarker]))
      (exit names, Sweep.tape [Sweep.leftMarker]
        ((rows names bits).map Sweep.row ++ [Sweep.rightMarker])) := by
  simpa only [machine, entry, exit, run] using
    Sweep.steps (visit anchor names) (.inl ()) (rawRows anchor names bits) [] []

theorem halt (anchor : TapeName) (names : List TapeName) (symbols) :
    machine anchor names (exit names) symbols = none := rfl

private def letter (anchor : TapeName) : Letter → Sweep.Alphabet (Row TapeName)
  | .inl value => Sweep.row (bit anchor value)
  | .inr 0 => Sweep.row separator
  | .inr 1 => Sweep.leftMarker
  | .inr 2 => Sweep.rightMarker

private def readLetter (anchor : TapeName) : Sweep.Alphabet (Row TapeName) → Option Letter
  | some (.inl false) => some (.inr 1)
  | some (.inl true) => some (.inr 2)
  | some (.inr entry) => if entry.2 anchor then some (.inr 0)
      else if entry.1 anchor = Binary.data false then some (.inl false)
      else if entry.1 anchor = Binary.data true then some (.inl true) else none
  | none => none

/-- Public symbols do not expose source track names or scratch contents. -/
def letters (anchor : TapeName) : Letter ↪ Sweep.Alphabet (Row TapeName) := by
  have roundtrip (value : Letter) : readLetter anchor (letter anchor value) = some value := by
    rcases value with value | value
    · cases value <;> simp [readLetter, letter, Sweep.row, bit, outputLetter, Binary.data]
    · fin_cases value <;> rfl
  exact ⟨letter anchor, fun first second equal => Option.some.inj
    ((roundtrip first).symm.trans ((congrArg (readLetter anchor) equal).trans (roundtrip second)))⟩

@[simp] theorem letters_bit (anchor : TapeName) (value : Bool) :
    letters anchor (.inl value) = Sweep.row (outputLetter anchor value) := rfl

/-- Every external letter is nonblank, including separators and framing. -/
theorem letters_nonblank (anchor : TapeName) (value : Letter) : letters anchor value ≠ none := by
  change letter anchor value ≠ none
  rcases value with value | value
  · simp [letter, Sweep.row]
  · fin_cases value <;> simp [letter, Sweep.row, Sweep.leftMarker, Sweep.rightMarker]

/-- The abstract serialization is the ordinary input word of the preparer. -/
theorem serialize_eq (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    serialize (letters anchor) (names.map bits) =
      Sweep.leftMarker :: ((rawRows anchor names bits).map Sweep.row ++ [Sweep.rightMarker]) := by
  change serialize (letter anchor) (names.map bits) = _
  simp [serialize, letter, rawRows, rawBlocks, List.map_flatMap, Function.comp_def,
    List.flatMap_map, List.map_append]

@[simp] theorem blockRows_length (name : TapeName) (marked : Bool) (bits : List Bool) :
    (blockRows name marked bits).length = bits.length + 1 := by
  induction bits generalizing marked <;> simp [blockRows, *]

/-- Preparation reserves one row per bit, one per separator, and one shared
blank head row, so its interval is polynomially bounded by its input widths. -/
theorem rawRows_length (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    (rawRows anchor names bits).length = 1 + (names.map (fun name => (bits name).length + 1)).sum := by
  have blocks : (rawBlocks anchor names bits).length = (names.map (fun name => (bits name).length + 1)).sum := by
    induction names with
    | nil => rfl
    | cons name rest induction => simp [rawBlocks, List.flatMap_cons] at *; omega
  simp [rawRows, blocks, Nat.add_comm]

theorem rows_length (anchor : TapeName) (names : List TapeName) (bits : TapeName → List Bool) :
    (rows names bits).length = (rawRows anchor names bits).length := by
  have length := Sweep.run_length (visit anchor names) (.inl ()) (rawRows anchor names bits)
  simpa only [run] using length

private theorem block_other (selected name : TapeName) (different : selected ≠ name)
    (marked : Bool) (bits : List Bool) :
    ∀ entry ∈ blockRows name marked bits, entry.1 selected = 0 ∧ entry.2 selected = false := by
  induction bits generalizing marked with
  | nil => simp [blockRows, cell, different]
  | cons value rest induction =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | inside
    · simp [cell, different]
    · exact induction false entry inside

private theorem blocks_other (selected : TapeName) (names : List TapeName)
    (absent : selected ∉ names) (bits : TapeName → List Bool) :
    ∀ entry ∈ names.flatMap (fun name => blockRows name true (bits name)),
      entry.1 selected = 0 ∧ entry.2 selected = false := by
  intro entry member
  obtain ⟨name, member, inside⟩ := List.mem_flatMap.mp member
  exact block_other selected name (fun equal => absent (equal ▸ member)) true (bits name) entry inside

private theorem block_values (name : TapeName) (marked : Bool) (bits : List Bool) :
    (blockRows name marked bits).map (fun entry => entry.1 name) = Binary.word bits ++ [0] := by
  induction bits generalizing marked <;> simp [blockRows, cell, Binary.word, *]

private theorem block_unmarked (name : TapeName) (bits : List Bool) :
    ∀ entry ∈ blockRows name false bits, entry.2 name = false := by
  induction bits with
  | nil => simp [blockRows, cell]
  | cons value rest induction =>
    intro entry member
    rcases List.mem_cons.mp member with rfl | inside
    · simp [cell]
    · exact induction entry inside

private theorem mk_blank_suffix (payload blanks : List Binary.Symbol)
    (blank : ∀ value ∈ blanks, value = 0) :
    Turing.ListBlank.mk (payload ++ blanks) = Turing.ListBlank.mk payload := by
  induction blanks generalizing payload with
  | nil => simp
  | cons value rest induction =>
    have valueZero : value = 0 := blank value (by simp)
    subst value
    have remaining : ∀ value ∈ rest, value = 0 := fun value member => blank value (by simp [member])
    rw [← List.singleton_append, ← List.append_assoc, induction _ remaining]
    exact Tracks.blank_append payload

omit [DecidableEq TapeName] in
private theorem mk_blank_rows (entries : List (Row TapeName)) (name : TapeName)
    (blank : ∀ entry ∈ entries, entry.1 name = 0) :
    Turing.ListBlank.mk (entries.map (fun entry => entry.1 name)) = Turing.ListBlank.mk [] := by
  exact mk_blank_suffix [] (entries.map (fun entry => entry.1 name)) (by
    intro value member
    obtain ⟨entry, inside, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact blank entry inside)

private theorem represents_block (name : TapeName) (bits : List Bool)
    (before after : List (Row TapeName))
    (beforeBlank : ∀ entry ∈ before, entry.1 name = 0 ∧ entry.2 name = false)
    (afterBlank : ∀ entry ∈ after, entry.1 name = 0 ∧ entry.2 name = false) :
    Tracks.RepresentsAt name (before ++ blockRows name true bits ++ after) (CallingConvention.tape bits) := by
  have leftBlank : Turing.ListBlank.mk (before.reverse.map (fun entry => entry.1 name)) = Turing.ListBlank.mk [] :=
    mk_blank_rows before.reverse name (by intro entry member; exact (beforeBlank entry (List.mem_reverse.mp member)).1)
  have suffixBlank (payload : List Binary.Symbol) :
      Turing.ListBlank.mk (payload ++ after.map (fun entry => entry.1 name)) = Turing.ListBlank.mk payload :=
    mk_blank_suffix payload (after.map (fun entry => entry.1 name)) (by
      intro value member
      obtain ⟨entry, inside, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact (afterBlank entry inside).1)
  cases bits with
  | nil =>
    refine ⟨before, cell name 0 true, after, by simp [blockRows],
      (fun entry member => (beforeBlank entry member).2), by simp [cell],
      (fun entry member => (afterBlank entry member).2), ?_⟩
    have rightBlank := mk_blank_rows after name (fun entry member => (afterBlank entry member).1)
    rw [leftBlank, rightBlank]
    simp [CallingConvention.tape, Binary.word, cell, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']
  | cons value rest =>
    refine ⟨before, cell name (Binary.data value) true, blockRows name false rest ++ after,
      by simp [blockRows, List.append_assoc],
      (fun entry member => (beforeBlank entry member).2), by simp [cell], ?_, ?_⟩
    · intro entry member
      rcases List.mem_append.mp member with inside | outside
      · exact block_unmarked name rest entry inside
      · exact (afterBlank entry outside).2
    · rw [List.map_append, block_values, suffixBlank, leftBlank]
      have strip : Turing.ListBlank.mk (Binary.word rest ++ [0]) = Turing.ListBlank.mk (Binary.word rest) :=
        Tracks.blank_append (Binary.word rest)
      rw [strip]
      simp [CallingConvention.tape, Binary.word, cell, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']

/-- The prepared interval represents precisely the given input words, with all
other source tapes blank. Every source head is marked exactly once. -/
theorem represents (names : List TapeName) (unique : names.Nodup) (bits : TapeName → List Bool) :
    Tracks.Represents (rows names bits)
      (fun name => if name ∈ names then CallingConvention.tape (bits name) else buffer []) := by
  intro name
  by_cases present : name ∈ names
  · obtain ⟨before, after, split⟩ := List.mem_iff_append.mp present
    have valid := List.nodup_append.mp (split ▸ unique)
    have beforeAbsent : name ∉ before := fun member => valid.2.2 name member name (by simp) rfl
    have afterAbsent : name ∉ after := (List.nodup_cons.mp valid.2.1).1
    have beforeBlank : ∀ entry ∈ initialRow names :: before.flatMap (fun other => blockRows other true (bits other)),
        entry.1 name = 0 ∧ entry.2 name = false := by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · simp [initialRow, present]
      · exact blocks_other name before beforeAbsent bits entry member
    have represented := represents_block name (bits name)
      (initialRow names :: before.flatMap (fun other => blockRows other true (bits other)))
      (after.flatMap (fun other => blockRows other true (bits other))) beforeBlank
      (blocks_other name after afterAbsent bits)
    simpa [rows, split, List.flatMap_append, List.flatMap_cons, List.append_assoc, present] using represented
  · have afterBlank := blocks_other name names present bits
    have represented := represents_block name [] []
      (names.flatMap (fun other => blockRows other true (bits other))) (by simp) afterBlank
    have changed : Tracks.RepresentsAt name (rows names bits) (buffer []) :=
      represented.congr (by simp [rows, blockRows, cell, initialRow, present])
    simpa [present] using changed

end Polytime2.DelimitedInput
