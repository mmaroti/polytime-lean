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


import Polytime2.Extend

/-! # A complete selected-head movement on encoded tracks

Physical interval extension followed by marker movement. This routine starts
with an ordinary marked interval, provides its own margins, preserves all other
simulated tapes, and returns to the first row. The two direction routines form
a fixed finite family for use by the simulator's runtime action dispatcher.
-/

namespace Polytime2.MoveHead

open MultiTape

-- tapeLevel: simulated tape names; symbolLevel: their individual alphabets.
-- parameterLevel: runtime size names bounding row intervals.
universe tapeLevel symbolLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]

abbrev Controller := Sum (Fin 7) MoveMarker.Controller

instance : Inhabited Controller := ⟨.inl 0⟩

def machine (selected : TapeName) (moveRight : Bool) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) Controller :=
  sequence (Extend.machine Tracks.blank) (MoveMarker.machine selected) (.inl (moveRight, 0))

@[simp] theorem halt (selected : TapeName) (moveRight : Bool)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    machine selected moveRight (.inr (.inr ())) symbols = none := rfl

/-- A single source head moves with linear row cost, including physical margins,
controller handover, and restoration of the simulator's tape head. -/
theorem steps (selected : TapeName) (moveRight : Bool)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes) :
    ∃ finalRows ticks, finalRows.length = rows.length + 2 ∧ ticks ≤ 4 * rows.length + 17 ∧
      Tracks.Represents finalRows (Function.update tapes selected
        ((tapes selected).move (if moveRight then .right else .left))) ∧
      Steps (machine selected moveRight) ticks
        (.inl 0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (.inr (.inr ()), Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  have extended := Extend.steps (Tracks.blank (Alphabet := Alphabet)) rows
  obtain ⟨finalRows, ticks, length, cost, correct, moved⟩ := MoveMarker.padded_steps selected moveRight represented [] []
  refine ⟨finalRows, (2 * rows.length + 9) + ticks + 1, length, by omega, correct, ?_⟩
  exact sequence_steps _ _ _ extended (by intro symbols; rfl) moved

/-- Uniform polynomial TM0 certificate for the complete selected-head operation.
The input needs no preexisting padding rows or scratch interval. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)]
    (selected : TapeName) (moveRight : Bool) (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment (rows : List (Tracks.Row Alphabet)) tapes, Tracks.Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∃ finalRows ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
          finalRows.length = rows.length + 2 ∧
          Tracks.Represents finalRows (Function.update tapes selected
            ((tapes selected).move (if moveRight then .right else .left))) ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine selected moveRight))))^[ticks]
            (some (SingleTape.configuration (.inl 0, Sweep.tape [Sweep.leftMarker]
              (rows.map Sweep.row ++ [Sweep.rightMarker])))) =
            some (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) ∧
          Turing.TM0.step (SingleTape.compile (machine selected moveRight))
            (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  refine ⟨8 * capacity + 34, ?_⟩
  intro assignment rows tapes represented bounded
  obtain ⟨finalRows, ticks, length, cost, correct, trace⟩ := steps selected moveRight represented
  refine ⟨finalRows, 2 * ticks, ?_, length, correct, SingleTape.steps (machine selected moveRight) trace, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · exact SingleTape.halt (machine selected moveRight) _ (by simp [step])

end Polytime2.MoveHead
