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

import Polytime2.Wiring
import Polytime2.GcdMachine
import Polytime2.ReadBlock
import Polytime2.Pipeline

/-! # External gcd input preparation

The input contains a unary width, terminated by `3`, followed by two equally
padded little-endian binary words. Each word reserves a high zero digit for
remainder shifts. All working tapes start blank; a fixed pipeline prepares the
operands, zero scratch, and guard flag required by the gcd machine.
-/

namespace Polytime2.GcdInput

open MultiTape
open Binary (Symbol data word value)

-- Roles 0–3 are gcd workspace; 4 is external input; 5 holds the unary width.
abbrev Alphabet := fun _ : Fin 6 => Symbol
abbrev Input := List Bool × List Bool

def blank : Turing.Tape Symbol := Binary.tape [] [] ()
def bitsTape (bits : List Bool) : Turing.Tape Symbol := Binary.tape [3] (word bits ++ [0]) ()
def sizeField (count : ℕ) : List Symbol := List.replicate count 2 ++ [3]
def inputWord (input : Input) : List Symbol := sizeField input.1.length ++ word input.1 ++ word input.2 ++ [0]

private def sourceLeft (input : Input) (stage : ℕ) : List Symbol :=
  if stage ≤ 1 then [3]
  else if stage ≤ 3 then (sizeField input.1.length).reverse ++ [3]
  else if stage = 4 then (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]
  else (word input.2).reverse ++ (word input.1).reverse ++ (sizeField input.1.length).reverse ++ [3]

private def sourceRight (input : Input) (stage : ℕ) : List Symbol :=
  if stage ≤ 1 then inputWord input
  else if stage ≤ 3 then word input.1 ++ word input.2 ++ [0]
  else if stage = 4 then word input.2 ++ [0]
  else [0]

/-- At stage zero only the external input tape is nonblank. -/
def preparedAt (input : Input) (stage : Fin 6) : Tapes Alphabet := fun name =>
  if name = 4 then Binary.tape (sourceLeft input stage.val) (sourceRight input stage.val) ()
  else if name = 5 then if 2 ≤ stage.val then
    Binary.tape [3] (List.replicate input.1.length 2 ++ [0]) () else blank
  else if name = 3 then if 1 ≤ stage.val then Binary.tape [3] [1] () else blank
  else if name = 2 then if 3 ≤ stage.val then bitsTape (List.replicate input.1.length false) else blank
  else if name = 0 then if 4 ≤ stage.val then bitsTape input.1 else blank
  else if 5 ≤ stage.val then bitsTape input.2 else blank

private def flagMachine : Machine Alphabet (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => some (1, fun name => if name = 3 then (3, some .right) else (symbols name, none))
  | 1 => some (2, fun name => if name = 3 then (1, none) else (symbols name, none))
  | _ => none

private theorem flag_steps (input : Input) :
    Steps flagMachine 2 (0, preparedAt input 0) (2, preparedAt input 1) := by
  let middle : Tapes Alphabet := Function.update (preparedAt input 0) 3 (Binary.tape [3] [] ())
  refine Steps.next (middle := (1, middle)) ?_ (.next ?_ (.zero _))
  · simp only [step, flagMachine, Fin.val_zero, Option.map_some]
    congr 2
    funext name
    fin_cases name <;>
      simp [act, MultiTape.read, preparedAt, sourceLeft, sourceRight, blank, Binary.tape, middle,
        Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  · simp only [step, flagMachine, Fin.val_one, Option.map_some]
    congr 2
    funext name
    fin_cases name <;>
      simp [act, MultiTape.read, preparedAt, sourceLeft, sourceRight, blank, Binary.tape, middle,
        Turing.Tape.write_mk']

def headerWiring : Bool ↪ Fin 6 := twoTapes 4 5 (by decide)

def blockWiring (target : Fin 6) (bound : target.val < 3) : Fin 3 ↪ Fin 6 :=
  ⟨fun name => if name = 0 then 4 else if name = 1 then 5 else target, by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all <;> omega⟩

@[simp] theorem blockWiring_zero (target : Fin 6) (bound : target.val < 3) :
    blockWiring target bound 0 = 4 := rfl
@[simp] theorem blockWiring_one (target : Fin 6) (bound : target.val < 3) :
    blockWiring target bound 1 = 5 := rfl
@[simp] theorem blockWiring_two (target : Fin 6) (bound : target.val < 3) :
    blockWiring target bound 2 = target := rfl

noncomputable def header : Machine Alphabet UnaryRead.State := wire headerWiring UnaryRead.machine
noncomputable def block (target : Fin 6) (bound : target.val < 3) (fillZeros : Bool) : Machine Alphabet ReadBlock.State :=
  wire (blockWiring target bound) (ReadBlock.machine fillZeros false)

def LocalState (index : Fin 5) : Type := match index.val with
  | 0 => Fin 3
  | 1 => UnaryRead.State
  | _ => ReadBlock.State

noncomputable def components : (index : Fin 5) → Machine Alphabet (LocalState index)
  | ⟨0, _⟩ => flagMachine
  | ⟨1, _⟩ => header
  | ⟨2, _⟩ => block 2 (by decide) true
  | ⟨3, _⟩ => block 0 (by decide) false
  | ⟨4, _⟩ => block 1 (by decide) false

def entries : (index : Fin 5) → LocalState index
  | ⟨0, _⟩ => (0 : Fin 3)
  | ⟨1, _⟩ => UnaryRead.entry
  | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ => ReadBlock.entry

def exits : (index : Fin 5) → LocalState index
  | ⟨0, _⟩ => (2 : Fin 3)
  | ⟨1, _⟩ => UnaryRead.exit
  | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ => ReadBlock.exit

instance localStateFinite (index : Fin 5) : Fintype (LocalState index) := by
  unfold LocalState
  split <;> infer_instance

abbrev State := Pipeline.State LocalState
noncomputable def machine : Machine Alphabet State := Pipeline.machine components entries
def entry : State := Pipeline.position entries 0

private theorem header_steps (input : Input) :
    Steps header (2 * input.1.length + 6)
      (UnaryRead.entry, preparedAt input 1) (UnaryRead.exit, preparedAt input 2) := by
  apply wire_steps_of_eq headerWiring _ (UnaryRead.steps input.1.length [3] (word input.1 ++ word input.2 ++ [0]))
  · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, inputWord, sizeField,
      blank, Copy.frame, headerWiring, Binary.tape, List.append_assoc]
  · intro name; cases name <;> simp [preparedAt, sourceLeft, sourceRight, sizeField, Copy.frame,
      headerWiring, Binary.tape, List.reverse_append, List.append_assoc]
  · intro name outside
    fin_cases name <;> first
      | (solve | simp [preparedAt])
      | exact False.elim (outside ⟨false, rfl⟩)
      | exact False.elim (outside ⟨true, rfl⟩)

private theorem block_steps (input : Input) (sameLength : input.2.length = input.1.length)
    (index : Fin 5) (isBlock : index ≠ 0 ∧ index ≠ 1) :
    Steps (components index) (3 * input.1.length + 10)
      (entries index, preparedAt input ⟨index.val, by omega⟩)
      (exits index, preparedAt input ⟨index.val + 1, by omega⟩) := by
  fin_cases index
  all_goals try simp at isBlock
  · have trace := ReadBlock.steps true false input.1 (sourceLeft input 2) (sourceRight input 2)
    apply wire_steps_of_eq (blockWiring 2 (by decide)) _ trace
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.source, blank, Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.consumed, ReadBlock.payload, bitsTape, Binary.tape, word, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · have trace := ReadBlock.steps false false input.1 (sourceLeft input 3) (sourceRight input 4)
    apply wire_steps_of_eq (blockWiring 0 (by decide)) _ trace
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.source, blank, Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.consumed, ReadBlock.payload, bitsTape, Binary.tape, word, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)
  · have trace := ReadBlock.steps false false input.2 (sourceLeft input 4) (sourceRight input 5)
    simp only [sameLength] at trace
    apply wire_steps_of_eq (blockWiring 1 (by decide)) _ trace
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.source, blank, Binary.tape, word, List.append_assoc]
    · intro name; fin_cases name <;> simp [preparedAt, sourceLeft, sourceRight, ReadBlock.frame,
        ReadBlock.consumed, ReadBlock.payload, bitsTape, Binary.tape, word, List.append_assoc]
    · intro name outside; fin_cases name <;> first
        | (solve | simp [preparedAt])
        | exact False.elim (outside ⟨0, rfl⟩)
        | exact False.elim (outside ⟨1, rfl⟩)
        | exact False.elim (outside ⟨2, rfl⟩)

/-- Preparation charges every initialization and handover transition. -/
theorem steps (input : Input) (sameLength : input.2.length = input.1.length) :
    ∃ ticks, ticks ≤ 5 * (3 * input.1.length + 11) ∧
      Steps machine ticks (entry, preparedAt input 0) (none, preparedAt input 5) := by
  obtain ⟨ticks, final, cost, trace, encoded⟩ := Pipeline.steps components entries exits
    (fun stage tapes => tapes = preparedAt input stage) (3 * input.1.length + 10)
    (by intro index symbols; fin_cases index <;>
      simp [components, exits, flagMachine, header, block, wire, UnaryRead.halt, ReadBlock.halt] <;> rfl)
    (by
      intro index tapes represented
      subst tapes
      by_cases flag : index = 0
      · subst index
        exact ⟨2, _, by omega, flag_steps input, rfl⟩
      · by_cases size : index = 1
        · subst index
          exact ⟨_, _, by omega, header_steps input, rfl⟩
        · exact ⟨_, _, le_rfl, block_steps input sameLength index ⟨flag, size⟩, rfl⟩)
    (preparedAt input 0) rfl
  subst final
  exact ⟨ticks, cost, trace⟩

def workWiring : Fin 4 ↪ Fin 6 :=
  ⟨fun name => ⟨name.val, by omega⟩,
    by intro first second equal; exact Fin.ext (congrArg (fun name : Fin 6 => name.val) equal)⟩

/-- Widths are one greater than the mathematical operand bit capacity. -/
def hypothesis (sizes : Unit → ℕ) (input : Input) : Prop :=
  input.1.length = sizes () + 1 ∧ input.2.length = sizes () + 1 ∧
    value input.1 < 2 ^ sizes () ∧ value input.2 < 2 ^ sizes ()

/-- Preparation returns mathematical operands in the gcd calling convention. -/
theorem contract : Computes machine entry none
    (fun _sizes : Unit → ℕ => fun input tapes => tapes = preparedAt input 0)
    (fun sizes operands tapes => GcdMachine.representation sizes operands (fun name => tapes (workWiring name)))
    hypothesis (fun _ input => (value input.1, value input.2)) := by
  refine ⟨by intro symbols; rfl, 20 * (MvPolynomial.X () + 4), ?_⟩
  intro sizes input initial valid represented
  subst initial
  obtain ⟨ticks, cost, trace⟩ := steps input (by obtain ⟨first, second, _⟩ := valid; omega)
  refine ⟨ticks, _, ?_, trace, input.1, input.2, List.replicate input.1.length false, false,
    valid.1, valid.2.1, by simpa using valid.1, rfl, rfl, ?_⟩
  · simp only [map_mul, map_add, map_ofNat, MvPolynomial.eval_X]
    rw [valid.1] at cost
    omega
  · funext name
    fin_cases name <;> rfl

end Polytime2.GcdInput
