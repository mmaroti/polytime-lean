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

import Polytime2.AddMultiply
import Polytime2.ReadBlock
import Polytime2.Pipeline

/-! # Arithmetic input preparation from blank working tapes

The input is a unary addend width, two binary words of that width, a unary
multiplier width, and the multiplier bits. Width fields end in `3`; operands
have no delimiters because their widths control transfer. All working tapes
start blank. Pipeline stages hide controller handovers from the preparation
contract.
-/

namespace Polytime2.AddMultiplyInput

open MultiTape
open Binary (Symbol word)

-- Tape roles 0–6 are the arithmetic workspace: multiplier, sum, accumulator,
-- addition output, zero buffer, and the two addends. Role 7 is external input;
-- roles 8 and 9 hold the addend and multiplier widths.
abbrev Alphabet := fun _ : Fin 10 => Symbol
abbrev Input := AddMultiply.Input

def blank : Turing.Tape Symbol := Binary.tape [] [] ()
def bitsTape (bits : List Bool) : Turing.Tape Symbol := BinaryMultiplication.tape bits

def sizeField (count : ℕ) : List Symbol := List.replicate count 2 ++ [3]

def inputWord (input : Input) : List Symbol :=
  sizeField input.1.length ++ word input.1 ++ word input.2.1 ++
    sizeField input.2.2.length ++ word input.2.2 ++ [0]

private def sourceLeft (input : Input) (stage : ℕ) : List Symbol :=
  if stage = 0 then [3]
  else if stage ≤ 5 then (sizeField input.1.length).reverse ++ [3]
  else if stage = 6 then (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]
  else if stage = 7 then (word input.2.1).reverse ++ (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]
  else if stage = 8 then (sizeField input.2.2.length).reverse ++ (word input.2.1).reverse ++
    (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]
  else (word input.2.2).reverse ++ (sizeField input.2.2.length).reverse ++ (word input.2.1).reverse ++
    (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]

private def sourceRight (input : Input) (stage : ℕ) : List Symbol :=
  if stage = 0 then inputWord input
  else if stage ≤ 5 then word input.1 ++ word input.2.1 ++ sizeField input.2.2.length ++ word input.2.2 ++ [0]
  else if stage = 6 then word input.2.1 ++ sizeField input.2.2.length ++ word input.2.2 ++ [0]
  else if stage = 7 then sizeField input.2.2.length ++ word input.2.2 ++ [0]
  else if stage = 8 then word input.2.2 ++ [0]
  else [0]

/-- The only nonblank tape at stage zero is the external input. -/
def preparedAt (input : Input) (stage : Fin 10) : Tapes Alphabet := fun name =>
  if name = 7 then Binary.tape (sourceLeft input stage.val) (sourceRight input stage.val) ()
  else if name = 8 then if 1 ≤ stage.val then
    Binary.tape [3] (List.replicate input.1.length 2 ++ [0]) () else blank
  else if name = 9 then if 8 ≤ stage.val then
    Binary.tape [3] (List.replicate input.2.2.length 2 ++ [0]) () else blank
  else if name = 1 then if 2 ≤ stage.val then bitsTape (List.replicate input.1.length false) else blank
  else if name = 2 then if 3 ≤ stage.val then bitsTape (List.replicate (input.1.length + 1) false) else blank
  else if name = 3 then if 4 ≤ stage.val then bitsTape (List.replicate (input.1.length + 1) false) else blank
  else if name = 4 then if 5 ≤ stage.val then bitsTape (List.replicate (input.1.length + 1) false) else blank
  else if name = 5 then if 6 ≤ stage.val then bitsTape input.1 else blank
  else if name = 6 then if 7 ≤ stage.val then bitsTape input.2.1 else blank
  else if 9 ≤ stage.val then bitsTape input.2.2 else blank

def headerWiring (second : Bool) : Bool ↪ Fin 10 := twoTapes 7 (if second then 9 else 8) (by cases second <;> decide)

def blockWiring (counter target : Fin 10) (targetBound : target.val < 7) (counterValid : counter = 8 ∨ counter = 9) :
    Fin 3 ↪ Fin 10 :=
  ⟨(fun name => if name = 0 then 7 else if name = 1 then counter else target), by
    intro left right equal
    rcases counterValid with rfl | rfl <;> fin_cases left <;> fin_cases right <;> simp_all <;> omega⟩

@[simp] theorem blockWiring_zero (counter target : Fin 10) (bound : target.val < 7) (valid : counter = 8 ∨ counter = 9) :
    blockWiring counter target bound valid 0 = 7 := rfl
@[simp] theorem blockWiring_one (counter target : Fin 10) (bound : target.val < 7) (valid : counter = 8 ∨ counter = 9) :
    blockWiring counter target bound valid 1 = counter := rfl
@[simp] theorem blockWiring_two (counter target : Fin 10) (bound : target.val < 7) (valid : counter = 8 ∨ counter = 9) :
    blockWiring counter target bound valid 2 = target := rfl

noncomputable def header (second : Bool) : Machine Alphabet UnaryRead.State := wire (headerWiring second) UnaryRead.machine

noncomputable def block (counter target : Fin 10) (targetBound : target.val < 7) (counterValid : counter = 8 ∨ counter = 9)
    (fillZeros extra : Bool) : Machine Alphabet ReadBlock.State :=
  wire (blockWiring counter target targetBound counterValid) (ReadBlock.machine fillZeros extra)

def LocalState (index : Fin 9) : Type := match index.val with
  | 0 | 7 => UnaryRead.State
  | _ => ReadBlock.State

noncomputable def components : (index : Fin 9) → Machine Alphabet (LocalState index)
  | ⟨0, _⟩ => header false
  | ⟨1, _⟩ => block 8 1 (by decide) (Or.inl rfl) true false
  | ⟨2, _⟩ => block 8 2 (by decide) (Or.inl rfl) true true
  | ⟨3, _⟩ => block 8 3 (by decide) (Or.inl rfl) true true
  | ⟨4, _⟩ => block 8 4 (by decide) (Or.inl rfl) true true
  | ⟨5, _⟩ => block 8 5 (by decide) (Or.inl rfl) false false
  | ⟨6, _⟩ => block 8 6 (by decide) (Or.inl rfl) false false
  | ⟨7, _⟩ => header true
  | ⟨8, _⟩ => block 9 0 (by decide) (Or.inr rfl) false false

def entries : (index : Fin 9) → LocalState index
  | ⟨0, _⟩ | ⟨7, _⟩ => UnaryRead.entry
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨8, _⟩ => ReadBlock.entry

def exits : (index : Fin 9) → LocalState index
  | ⟨0, _⟩ | ⟨7, _⟩ => UnaryRead.exit
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨8, _⟩ => ReadBlock.exit

instance localStateFinite (index : Fin 9) : Fintype (LocalState index) := by
  unfold LocalState
  split <;> infer_instance

abbrev State := Pipeline.State LocalState
noncomputable def machine : Machine Alphabet State := Pipeline.machine components entries
def entry : State := Pipeline.position entries 0

private theorem header_steps (input : Input) (second : Bool) :
    let stage : Fin 9 := if second then 7 else 0
    Steps (components stage) (2 * (if second then input.2.2.length else input.1.length) + 6)
      (entries stage, preparedAt input ⟨stage.val, by omega⟩)
      (exits stage, preparedAt input ⟨stage.val + 1, by omega⟩) := by
  cases second
  · have trace := UnaryRead.steps input.1.length [3]
      (word input.1 ++ word input.2.1 ++ sizeField input.2.2.length ++ word input.2.2 ++ [0])
    apply wire_steps_of_eq (headerWiring false) _ trace
    · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, inputWord, sizeField, blank,
        Copy.frame, headerWiring, Binary.tape, List.append_assoc]
    · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, sizeField,
        Copy.frame, headerWiring, Binary.tape, List.reverse_append, List.append_assoc]
    · intro name outside
      fin_cases name <;> simp_all [preparedAt, headerWiring, twoTapes]
  · have trace := UnaryRead.steps input.2.2.length (sourceLeft input 7) (word input.2.2 ++ [0])
    apply wire_steps_of_eq (headerWiring true) _ trace
    · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, sizeField, blank,
        Copy.frame, headerWiring, Binary.tape, List.append_assoc]
    · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, sizeField,
        Copy.frame, headerWiring, Binary.tape, List.reverse_append, List.append_assoc]
    · intro name outside
      fin_cases name <;> simp_all [preparedAt, headerWiring, twoTapes]

private theorem block_steps (input : Input) (sameLength : input.2.1.length = input.1.length)
    (index : Fin 9) (isBlock : index ≠ 0 ∧ index ≠ 7) :
    ∃ ticks, ticks ≤ 3 * (input.1.length + input.2.2.length) + 11 ∧
      Steps (components index) ticks (entries index, preparedAt input ⟨index.val, by omega⟩)
        (exits index, preparedAt input ⟨index.val + 1, by omega⟩) := by
  fin_cases index
  all_goals try simp at isBlock
  · refine ⟨3 * input.1.length + 10, by omega, ?_⟩
    have trace := ReadBlock.steps true false (List.replicate input.1.length false) (sourceLeft input 1) (sourceRight input 1)
    simp only [List.length_replicate] at trace
    apply wire_steps_of_eq (blockWiring 8 1 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.1.length + 11, by omega, ?_⟩
    have trace := ReadBlock.steps true true (List.replicate input.1.length false) (sourceLeft input 2) (sourceRight input 2)
    simp only [List.length_replicate] at trace
    apply wire_steps_of_eq (blockWiring 8 2 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.replicate_succ, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.1.length + 11, by omega, ?_⟩
    have trace := ReadBlock.steps true true (List.replicate input.1.length false) (sourceLeft input 3) (sourceRight input 3)
    simp only [List.length_replicate] at trace
    apply wire_steps_of_eq (blockWiring 8 3 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.replicate_succ, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.1.length + 11, by omega, ?_⟩
    have trace := ReadBlock.steps true true (List.replicate input.1.length false) (sourceLeft input 4) (sourceRight input 4)
    simp only [List.length_replicate] at trace
    apply wire_steps_of_eq (blockWiring 8 4 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.replicate_succ, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.1.length + 10, by omega, ?_⟩
    have trace := ReadBlock.steps false false (input.1) (sourceLeft input 5) (sourceRight input 6)
    apply wire_steps_of_eq (blockWiring 8 5 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.1.length + 10, by omega, ?_⟩
    have trace := ReadBlock.steps false false (input.2.1) (sourceLeft input 6) (sourceRight input 7)
    simp only [sameLength] at trace
    apply wire_steps_of_eq (blockWiring 8 6 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · refine ⟨3 * input.2.2.length + 10, by omega, ?_⟩
    have trace := ReadBlock.steps false false (input.2.2) (sourceLeft input 8) (sourceRight input 9)
    apply wire_steps_of_eq (blockWiring 9 0 (by decide) (by simp)) _ trace
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.source, blank,
          Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;>
        simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame, ReadBlock.consumed, ReadBlock.payload,
          bitsTape, BinaryMultiplication.tape, Binary.tape, word,
          List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)

/-- One fixed finite pipeline prepares every runtime operand width. -/
theorem steps (input : Input) (sameLength : input.2.1.length = input.1.length) :
    ∃ ticks, ticks ≤ 9 * (3 * (input.1.length + input.2.2.length) + 12) ∧
      Steps machine ticks (entry, preparedAt input 0) (none, preparedAt input 9) := by
  obtain ⟨ticks, final, cost, trace, encoded⟩ := Pipeline.steps components entries exits
    (fun stage tapes => tapes = preparedAt input stage) (3 * (input.1.length + input.2.2.length) + 11)
    (by intro index symbols; fin_cases index <;>
        simp [components, exits, header, block, wire, UnaryRead.halt, ReadBlock.halt] <;> rfl)
    (by
      intro index tapes represented
      subst tapes
      by_cases first : index = 0
      · subst index
        exact ⟨_, _, by simp; omega, header_steps input false, rfl⟩
      · by_cases second : index = 7
        · subst index
          exact ⟨_, _, by simp; omega, header_steps input true, rfl⟩
        · obtain ⟨ticks, cost, trace⟩ := block_steps input sameLength index ⟨first, second⟩
          exact ⟨ticks, _, cost, trace, rfl⟩)
    (preparedAt input 0) rfl
  subst final
  exact ⟨ticks, cost, trace⟩

def workWiring : Fin 7 ↪ Fin 10 :=
  ⟨fun name => ⟨name.val, by omega⟩, by intro left right equal; exact Fin.ext (congrArg (fun name : Fin 10 => name.val) equal)⟩

/-- The prepared workspace satisfies the existing arithmetic calling convention. -/
theorem prepared (input : Input) :
    AddMultiply.inputRepresentation input (fun name => preparedAt input 9 (workWiring name)) := by
  unfold AddMultiply.inputRepresentation
  funext name
  fin_cases name <;> rfl

/-- Mathematical preparation contract: no controller, scratch, or runtime
polynomial appears in the caller's proof obligations. -/
theorem contract : Computes machine entry none
    (fun _sizes : Bool → ℕ => fun input tapes => tapes = preparedAt input 0)
    (fun _sizes => fun input tapes => AddMultiply.inputRepresentation input (fun name => tapes (workWiring name)))
    (fun sizes input => input.2.1.length = input.1.length ∧
      input.1.length ≤ sizes false ∧ input.2.2.length ≤ sizes true)
    (fun _ input => input) := by
  refine ⟨by intro symbols; rfl, 9 * (3 * (MvPolynomial.X false + MvPolynomial.X true) + 12), ?_⟩
  intro sizes input initial valid represented
  subst initial
  obtain ⟨ticks, cost, trace⟩ := steps input valid.1
  refine ⟨ticks, _, ?_, trace, prepared input⟩
  simp only [map_mul, map_add, map_ofNat, MvPolynomial.eval_X]
  nlinarith [valid.2.1, valid.2.2]

end Polytime2.AddMultiplyInput
