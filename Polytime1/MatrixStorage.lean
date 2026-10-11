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
import Polytime1.Examples.MatrixWrite

/-! # Mathematical access to a prepared fixed-entry matrix

Runtime row and column indices select one entry. Scalar scratch is existential;
the navigation window and caller suffix belong to the storage representation.
The backend is the existing indexed reader/table/writer, including its costs.
-/

namespace Polytime1.MatrixStorage

open Examples.Matrices TupleMachine

-- entryLevel: the fixed carrier stored in each matrix entry.
universe entryLevel

abbrev Value (entries : FixedPresentation.{entryLevel}) (sizes : SizeAssignment context) :=
  ℕ × (ℕ × Matrix (Fin (sizes .K)) (Fin (sizes .L)) entries.Carrier)

noncomputable section IndexedMap

variable (entries : FixedPresentation.{entryLevel})

abbrev valid (sizes : SizeAssignment context) (value : Value entries sizes) : Prop :=
  value.1 < sizes .K ∧ value.2.1 < sizes .L

def advance (operation : entries.Carrier → entries.Carrier)
    (sizes : SizeAssignment context) (value : Value entries sizes) : Value entries sizes :=
  if bounded : valid entries sizes value then
    let row : Fin (sizes .K) := ⟨value.1, bounded.1⟩
    let column : Fin (sizes .L) := ⟨value.2.1, bounded.2⟩
    (value.1, value.2.1 + 1, Function.update value.2.2 row
      (Function.update (value.2.2 row) column (operation (value.2.2 row column))))
  else value

def frame (sizes : SizeAssignment context) (value : Value entries sizes)
    (scalar : entries.Carrier) (right : List Symbol) : List Symbol :=
  let width := (domain entries).bitWidth (assignment (sizes .K) (sizes .L))
  UnaryMachine.fields [value.1, value.2.1, sizes .L] ++
    word (List.ofFn (BoolTuple.fromBits (entries.codec.encode scalar))) ++
    3 :: (List.replicate width (data true) ++ 4 ::
      (word (List.ofFn (fun index : Fin width =>
        (encode entries (sizes .K) (sizes .L) value.2.2).getLsbD index.val)) ++ right))

/-- The caller may supply any canonical scalar in the reusable temporary slot. -/
def representation (sizes : SizeAssignment context) (right : List Symbol)
    (value : Value entries sizes) (actual : Turing.Tape Symbol) : Prop :=
  ∃ scalar, actual = (Tape.configuration () [] (frame entries sizes value scalar right)).Tape

/-- Transform one selected entry and advance its column counter. The contract
exposes mathematical update only; the runtime polynomial and scratch stay hidden. -/
theorem map_contract [Nontrivial entries.Carrier] (operation : entries.Carrier → entries.Carrier) :
    Realization.Realizes (representation entries) (representation entries) (valid entries)
      (fun sizes initial final => final = advance entries operation sizes initial) := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ :=
    Examples.MatrixWrite.realizes_entry_map_next_column entries operation
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro sizes right value initial bounded represented
  obtain ⟨scalar, rfl⟩ := represented
  let row : Fin (sizes .K) := ⟨value.1, bounded.1⟩
  let column : Fin (sizes .L) := ⟨value.2.1, bounded.2⟩
  obtain ⟨ticks, cost, trace⟩ := runs (sizes .K) (sizes .L) value.2.2 row column
    (word (List.ofFn (BoolTuple.fromBits (entries.codec.encode scalar)))) (data true) right
    (by simp) (by
      intro symbol member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      cases bit <;> decide) (by decide)
  have sizesEqual : assignment (sizes .K) (sizes .L) = sizes := by
    funext name; cases name <;> rfl
  rw [sizesEqual] at cost
  refine ⟨advance entries operation sizes value,
    (Tape.configuration () [] (frame entries sizes (advance entries operation sizes value)
      (operation (value.2.2 row column)) right)).Tape, ticks, cost, ?_, rfl,
    ⟨operation (value.2.2 row column), rfl⟩⟩
  convert trace using 1 <;> simp [frame, advance, row, column, Tape.configuration, List.append_assoc]
  all_goals simp [dite_eq_left bounded, UnaryMachine.units,
    UnaryMachine.fields, List.replicate_add, List.append_assoc]
  all_goals rfl

end IndexedMap
end Polytime1.MatrixStorage
