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

import Polytime2.Machine

/-! # Returning a tape head to a boundary marker

The routine works for arbitrary finite alphabets, including both binary words
and scalar arrays. It preserves all cells and stops immediately to the right
of the specified marker. Scalar stream preparation and extraction use it.
-/

namespace Polytime2.ReturnToMarker

open MultiTape

-- symbolLevel: the alphabet of the tape whose head is restored.
universe symbolLevel
variable {Symbol : Type symbolLevel} [Inhabited Symbol] [DecidableEq Symbol]

def tape (left right : List Symbol) : Tapes (fun _ : Unit => Symbol) :=
  fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)

def machine (marker : Symbol) : Machine (fun _ : Unit => Symbol) (Fin 2) :=
  fun state symbols => if state = 0 then
    if symbols () = marker then some (1, fun _ => (symbols (), some .right))
    else some (0, fun _ => (symbols (), some .left))
  else none

/-- A scan and return preserve the entire word and its neighboring regions. -/
theorem steps (marker : Symbol) (payload : List Symbol)
    (noMarker : ∀ symbol ∈ payload, symbol ≠ marker)
    (current : Symbol) (different : current ≠ marker) (left right : List Symbol) :
    Steps (machine marker) (payload.length + 2)
      (0, tape (payload ++ marker :: left) (current :: right))
      (1, tape (marker :: left) (payload.reverse ++ current :: right)) := by
  induction payload generalizing current right with
  | nil =>
    have first : step (machine marker) (0, tape (marker :: left) (current :: right)) =
        some (0, tape left (marker :: current :: right)) := by
      simp only [step, machine, ↓reduceIte, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, different, Option.map_some]
      congr 2
    have second : step (machine marker) (0, tape left (marker :: current :: right)) =
        some (1, tape (marker :: left) (current :: right)) := by
      simp only [step, machine, ↓reduceIte, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, Option.map_some]
      congr 2
    simpa using Steps.next first (Steps.next second (.zero _))
  | cons symbol payload hypothesis =>
    have first : step (machine marker)
        (0, tape ((symbol :: payload) ++ marker :: left) (current :: right)) =
        some (0, tape (payload ++ marker :: left) (symbol :: current :: right)) := by
      simp only [step, machine, ↓reduceIte, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, different, Option.map_some]
      congr 2
    have rest := hypothesis (by intro other member; exact noMarker other (by simp [member]))
      symbol (noMarker symbol (by simp)) (current :: right)
    simpa [List.reverse_cons, List.append_assoc] using Steps.next first rest

omit [Inhabited Symbol] in
theorem halt (marker : Symbol) (symbols : Symbols (fun _ : Unit => Symbol)) :
    machine marker 1 symbols = none := by simp [machine]

end Polytime2.ReturnToMarker
