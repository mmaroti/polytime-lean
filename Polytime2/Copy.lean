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

/-! # Fixed-width element transfer

Tape false is the source and tape true is the destination. Copying a fixed
number of cells preserves the source, both left prefixes, and the destination
suffix. Both heads return to their entry positions. The width is a controller
specialization constant, not a runtime register.
-/

namespace Polytime2.Copy

open MultiTape

-- symbolLevel: the common finite alphabet of the two data tapes.
universe symbolLevel
variable {Symbol : Type symbolLevel} [Inhabited Symbol]

abbrev State (width : ℕ) := Bool × Fin (width + 1)

def machine (width : ℕ) : Machine (fun _ : Bool => Symbol) (State width)
  | (false, remaining), symbols =>
    if finished : remaining.val = 0 then
      some ((true, Fin.last width), stationary symbols)
    else some ((false, ⟨remaining.val - 1, by omega⟩),
      fun _ => (symbols false, some .right))
  | (true, remaining), symbols =>
    if finished : remaining.val = 0 then none
    else some ((true, ⟨remaining.val - 1, by omega⟩),
      fun name => (symbols name, some .left))

def frame (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Tapes (fun _ : Bool => Symbol)
  | false => Turing.Tape.mk' (Turing.ListBlank.mk sourceLeft) (Turing.ListBlank.mk sourceRight)
  | true => Turing.Tape.mk' (Turing.ListBlank.mk targetLeft) (Turing.ListBlank.mk targetRight)

private theorem forward (width : ℕ) (payload old : List Symbol) (sameLength : old.length = payload.length)
    (fits : payload.length < width + 1) (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine (Symbol := Symbol) width) payload.length
      ((false, ⟨payload.length, fits⟩), frame sourceLeft (payload ++ sourceRight) targetLeft (old ++ targetRight))
      ((false, 0), frame (payload.reverse ++ sourceLeft) sourceRight (payload.reverse ++ targetLeft) targetRight) := by
  induction payload generalizing old sourceLeft targetLeft with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [frame] using Steps.zero (machine := machine (Symbol := Symbol) width)
      ((false, 0), frame sourceLeft sourceRight targetLeft targetRight)
  | cons symbol payload hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have smaller : payload.length < width + 1 := by simp at fits; omega
      have first : step (machine (Symbol := Symbol) width)
          ((false, ⟨(symbol :: payload).length, fits⟩),
            frame sourceLeft ((symbol :: payload) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight)) =
          some ((false, ⟨payload.length, smaller⟩),
            frame (symbol :: sourceLeft) (payload ++ sourceRight) (symbol :: targetLeft) (old ++ targetRight)) := by
        simp only [step, machine, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, dite_false, Option.map_some, Nat.add_sub_cancel]
        congr 2
        funext name
        cases name <;>
          simp [act, MultiTape.read, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk',
            Turing.ListBlank.cons_mk]
      have rest := hypothesis old (by simpa using sameLength) smaller (symbol :: sourceLeft) (symbol :: targetLeft)
      simpa [List.reverse_cons, List.append_assoc] using Steps.next first rest

private theorem rewind (width : ℕ) (sourceBlock targetBlock : List Symbol)
    (sameLength : targetBlock.length = sourceBlock.length) (fits : sourceBlock.length < width + 1)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine (Symbol := Symbol) width) sourceBlock.length
      ((true, ⟨sourceBlock.length, fits⟩),
        frame (sourceBlock ++ sourceLeft) sourceRight (targetBlock ++ targetLeft) targetRight)
      ((true, 0), frame sourceLeft (sourceBlock.reverse ++ sourceRight) targetLeft (targetBlock.reverse ++ targetRight)) := by
  induction sourceBlock generalizing targetBlock sourceRight targetRight with
  | nil =>
    have empty : targetBlock = [] := List.eq_nil_of_length_eq_zero sameLength
    subst targetBlock
    simpa [frame] using Steps.zero (machine := machine (Symbol := Symbol) width)
      ((true, 0), frame sourceLeft sourceRight targetLeft targetRight)
  | cons symbol sourceBlock hypothesis =>
    cases targetBlock with
    | nil => simp at sameLength
    | cons target targetBlock =>
      have smaller : sourceBlock.length < width + 1 := by simp at fits; omega
      have first : step (machine (Symbol := Symbol) width)
          ((true, ⟨(symbol :: sourceBlock).length, fits⟩),
            frame ((symbol :: sourceBlock) ++ sourceLeft) sourceRight
              ((target :: targetBlock) ++ targetLeft) targetRight) =
          some ((true, ⟨sourceBlock.length, smaller⟩),
            frame (sourceBlock ++ sourceLeft) (symbol :: sourceRight)
              (targetBlock ++ targetLeft) (target :: targetRight)) := by
        simp only [step, machine, List.length_cons, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false, dite_false, Option.map_some, Nat.add_sub_cancel]
        congr 2
        rw [act_move]
        funext name
        cases name <;>
          simp [frame, Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis targetBlock (by simpa using sameLength) smaller
        (symbol :: sourceRight) (target :: targetRight)
      simpa [List.reverse_cons, List.append_assoc] using Steps.next first rest

/-- Exact transition cost, including restoration of both head positions. -/
theorem steps (width : ℕ) (payload old : List Symbol)
    (payloadLength : payload.length = width) (oldLength : old.length = width)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine (Symbol := Symbol) width) (2 * width + 1)
      ((false, Fin.last width), frame sourceLeft (payload ++ sourceRight) targetLeft (old ++ targetRight))
      ((true, 0), frame sourceLeft (payload ++ sourceRight) targetLeft (payload ++ targetRight)) := by
  have copied := forward width payload old (oldLength.trans payloadLength.symm)
    (by omega) sourceLeft sourceRight targetLeft targetRight
  have handover : step (machine (Symbol := Symbol) width)
      ((false, 0), frame (payload.reverse ++ sourceLeft) sourceRight (payload.reverse ++ targetLeft) targetRight) =
      some ((true, Fin.last width),
        frame (payload.reverse ++ sourceLeft) sourceRight (payload.reverse ++ targetLeft) targetRight) := by
    simp [step, machine]
  have restored := rewind width payload.reverse payload.reverse rfl (by simp [payloadLength])
    sourceLeft sourceRight targetLeft targetRight
  simp only [List.length_reverse, payloadLength, List.reverse_reverse] at copied restored
  have trace := copied.trans (Steps.next handover restored)
  convert trace using 1 <;> first | omega | rfl

end Polytime2.Copy
