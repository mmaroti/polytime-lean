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


import Polytime2.TM0.MoveAll

/-! # Applying a complete multi-tape action on one tape

Write marked cells, then move all source heads through the fixed catalogue.
Commands are finite runtime controller memory. One compiled machine handles
all command vectors and all runtime interval lengths, including stationary
source heads. Physical padding, head restoration, and handovers are charged.
-/

namespace Polytime2.Act

open MultiTape

-- tapeLevel: simulated tape names; symbolLevel: their alphabets.
-- parameterLevel: runtime size names bounding row intervals.
universe tapeLevel symbolLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]

abbrev Packet (Alphabet : TapeName → Type symbolLevel) := Symbols Alphabet × MoveAll.Directions TapeName

/-- Finite writes and optional movements; booleans avoid an extra direction instance. -/
def packet (actions : Actions Alphabet) : Packet Alphabet :=
  (fun name => (actions name).1,
    fun name => (actions name).2.map (fun | .left => false | .right => true))

def effect (command : Packet Alphabet) (tapes : Tapes Alphabet) : Tapes Alphabet :=
  fun name => MoveAll.moveTape (command.2 name) ((tapes name).write (command.1 name))

omit [DecidableEq TapeName] in
@[simp] theorem effect_packet (actions : Actions Alphabet) (tapes : Tapes Alphabet) :
    effect (packet actions) tapes = MultiTape.act actions tapes := by
  funext name
  cases movement : (actions name).2 with
  | none => simp [effect, packet, MoveAll.moveTape, MultiTape.act, movement]
  | some direction => cases direction <;> simp [effect, packet, MoveAll.moveTape, MultiTape.act, movement]

abbrev Controller (Alphabet : TapeName → Type symbolLevel) (names : List TapeName) :=
  Sum (Sweep.Controller (Symbols Alphabet)) (MoveAll.Controller names)

instance controllerInhabited (names : List TapeName) : Inhabited (Controller Alphabet names) :=
  ⟨.inr (MoveAll.entry names)⟩

instance controllerFintype [Fintype TapeName] [∀ name, Fintype (Alphabet name)] (names : List TapeName) :
    Fintype (Controller Alphabet names) := inferInstanceAs
      (Fintype (Sum (Sweep.Controller (Symbols Alphabet)) (MoveAll.Controller names)))

def entry (names : List TapeName) (command : Packet Alphabet) : Controller Alphabet names :=
  .inl (.inl (false, command.1))

def exit (names : List TapeName) : Controller Alphabet names := .inr (MoveAll.exit names)

def machine (names : List TapeName) (command : Packet Alphabet) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) (Controller Alphabet names) :=
  sequence (Sweep.machine Tracks.writeVisit) (MoveAll.machine names command.2) (MoveAll.entry names)

@[simp] theorem halt (names : List TapeName) (command : Packet Alphabet)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    machine names command (exit names) symbols = none := by
  simp [machine, exit, MultiTape.sequence]

/-- A complete source action is realized by actual one-tape transitions, with
polynomial row cost and at most two new rows per simulated tape. -/
theorem steps (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    (command : Packet Alphabet) {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes) :
    ∃ finalRows ticks, finalRows.length ≤ rows.length + 2 * names.length ∧
      ticks ≤ 2 * rows.length + 4 + names.length * (4 * rows.length + 8 * names.length + 19) ∧
      Tracks.Represents finalRows (effect command tapes) ∧
      Steps (machine names command) ticks
        (entry names command, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (exit names, Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  have written := Tracks.write_steps command.1 rows [] []
  obtain ⟨finalRows, ticks, length, cost, correct, moved⟩ := MoveAll.steps names command.2 (represented.write command.1)
  simp only [List.length_map] at length cost
  rw [MoveAll.moveTapes_eq names unique complete] at correct
  refine ⟨finalRows, (2 * rows.length + 3) + ticks + 1, length, by omega, correct, ?_⟩
  exact sequence_steps _ _ _ written (by intro symbols; rfl) moved

/-- Runtime command dispatch: source action values are not specialization data. -/
def dispatch (names : List TapeName) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) (Packet Alphabet × Controller Alphabet names) :=
  fun state symbols => (machine names state.1 state.2 symbols).map fun command =>
    ((state.1, command.1), command.2)

@[simp] theorem dispatch_halt (names : List TapeName) (command : Packet Alphabet)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    dispatch names (command, exit names) symbols = none := by simp [dispatch]

/-- Polynomial TM0 certificate for full source actions on the represented tapes.
One controller and bound work for every runtime action and size assignment. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)]
    (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment command (rows : List (Tracks.Row Alphabet)) tapes, Tracks.Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∃ finalRows ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
          finalRows.length ≤ rows.length + 2 * names.length ∧
          Tracks.Represents finalRows (effect command tapes) ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (dispatch names))))^[ticks]
            (some (SingleTape.configuration ((command, entry names command), Sweep.tape [Sweep.leftMarker]
              (rows.map Sweep.row ++ [Sweep.rightMarker])))) =
            some (SingleTape.configuration ((command, exit names), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) ∧
          Turing.TM0.step (SingleTape.compile (dispatch names))
            (SingleTape.configuration ((command, exit names), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  refine ⟨4 * capacity + 8 + MvPolynomial.C (2 * names.length) *
    (4 * capacity + MvPolynomial.C (8 * names.length + 19)), ?_⟩
  intro assignment command rows tapes represented bounded
  obtain ⟨finalRows, ticks, length, cost, correct, trace⟩ := steps names unique complete command represented
  have lifted := trace.rename (fun state => (command, state)) (target := dispatch names)
    (by intro state symbols next actions transition; simp [dispatch, transition])
  refine ⟨finalRows, 2 * ticks, ?_, length, correct, SingleTape.steps (dispatch names) lifted, ?_⟩
  · have capacityBound : 4 * rows.length + 8 * names.length + 19 ≤
        4 * MvPolynomial.eval assignment capacity + (8 * names.length + 19) := by omega
    have multiplied := Nat.mul_le_mul_left names.length capacityBound
    simp only [map_mul, map_add, map_ofNat, MvPolynomial.eval_C]
    nlinarith
  · exact SingleTape.halt (dispatch names) _ (by simp [step])

end Polytime2.Act
