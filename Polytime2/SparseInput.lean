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

import Polytime2.Tracks

/-! # A single external input with blank working tapes

Each external symbol is placed in one fixed track; every other track is blank.
All initial heads occupy the same fixed row. This uses only a constant amount
of framing around the input, with no size-dependent padding or working markers.
-/

namespace Polytime2.Tracks

open MultiTape

-- tapeLevel: tape names; symbolLevel: their potentially different alphabets.
universe tapeLevel symbolLevel
variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]

def inputSymbols (input : TapeName) (symbol : Alphabet input) : Symbols Alphabet :=
  Function.update (fun _ => default) input symbol

/-- The external head and tail are ordinary symbols on one input tape. -/
def inputRows (input : TapeName) (marker head : Alphabet input) (tail : List (Alphabet input)) : List (Row Alphabet) :=
  (inputSymbols input marker, fun _ => false) ::
    (inputSymbols input head, fun _ => true) ::
      tail.map (fun symbol => (inputSymbols input symbol, fun _ => false))

def inputTapes (input : TapeName) (marker head : Alphabet input) (tail : List (Alphabet input)) : Tapes Alphabet :=
  Function.update (fun _ => Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk [])) input
    (Turing.Tape.mk' (Turing.ListBlank.mk [marker]) (Turing.ListBlank.mk (head :: tail)))

@[simp] theorem inputRows_length (input : TapeName) (marker head : Alphabet input) (tail : List (Alphabet input)) :
    (inputRows input marker head tail).length = tail.length + 2 := by simp [inputRows]

private theorem blankReplicate {Symbol : Type symbolLevel} [Inhabited Symbol] (count : ℕ) :
    Turing.ListBlank.mk (List.replicate count (default : Symbol)) = Turing.ListBlank.mk [] :=
  Quotient.sound (Or.inr ⟨count, rfl⟩)

/-- The input format represents an unprepared machine with all working tapes blank. -/
theorem inputRows_represents (input : TapeName) (marker head : Alphabet input) (tail : List (Alphabet input)) :
    Represents (inputRows input marker head tail) (inputTapes input marker head tail) := by
  intro name
  refine ⟨[(inputSymbols input marker, fun _ => false)], (inputSymbols input head, fun _ => true),
    tail.map (fun symbol => (inputSymbols input symbol, fun _ => false)), rfl, ?_, rfl, ?_, ?_⟩
  · intro previous member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro following member
    obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp member
    rfl
  · by_cases equal : name = input
    · subst name
      simp [inputTapes, inputSymbols, Turing.Tape.mk', List.map_map, Function.comp_def]
    · simp [inputTapes, inputSymbols, equal, Turing.Tape.mk', List.map_map, Function.comp_def,
        blankReplicate]
      exact (Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk ([] : List (Alphabet name)))).symm

end Polytime2.Tracks
