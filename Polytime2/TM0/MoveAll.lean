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


import Polytime2.TM0.MoveHead

/-! # Moving all source heads in a fixed tape catalogue

The catalogue is fixed by specialization. Each listed head is moved in turn,
with a stationary routine for a `none` direction. Controller types and row
alphabets do not depend on runtime row counts or direction values. The family
of machines below is lifted to runtime direction memory at the end of this file.
-/

namespace Polytime2.MoveAll

open MultiTape

-- tapeLevel: simulated tape names; symbolLevel: their alphabets.
-- parameterLevel: runtime sizes bounding the encoded row interval.
universe tapeLevel symbolLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]

abbrev Directions (TapeName : Type tapeLevel) := TapeName → Option Bool

/-- `none` stays put; `some false` moves left; `some true` moves right. -/
def moveTape {Symbol : Type symbolLevel} [Inhabited Symbol]
    (direction : Option Bool) (tape : Turing.Tape Symbol) : Turing.Tape Symbol :=
  match direction with
  | none => tape
  | some moveRight => tape.move (if moveRight then .right else .left)

def moveAt (selected : TapeName) (direction : Option Bool) (tapes : Tapes Alphabet) : Tapes Alphabet :=
  Function.update tapes selected (moveTape direction (tapes selected))

@[simp] theorem moveAt_none (selected : TapeName) (tapes : Tapes Alphabet) : moveAt selected none tapes = tapes := by
  funext name
  by_cases equal : name = selected
  · subst name; simp [moveAt, moveTape]
  · simp [moveAt, equal]

def moveTapes : List TapeName → Directions TapeName → Tapes Alphabet → Tapes Alphabet
  | [], _, tapes => tapes
  | name :: rest, directions, tapes => moveTapes rest directions (moveAt name (directions name) tapes)

/-- Tapes outside a catalogue are preserved, including their head positions. -/
theorem moveTapes_outside (names : List TapeName) (directions : Directions TapeName)
    (tapes : Tapes Alphabet) (name : TapeName) (outside : name ∉ names) :
    moveTapes names directions tapes name = tapes name := by
  induction names generalizing tapes with
  | nil => rfl
  | cons selected rest hypothesis =>
    have different : name ≠ selected := by intro equal; subst name; simp at outside
    have absent : name ∉ rest := by intro member; exact outside (by simp [member])
    rw [moveTapes, hypothesis _ absent]
    simp [moveAt, different]

/-- A duplicate-free catalogue applies each listed source movement exactly once. -/
theorem moveTapes_apply (names : List TapeName) (unique : names.Nodup)
    (directions : Directions TapeName) (tapes : Tapes Alphabet) (name : TapeName) :
    moveTapes names directions tapes name =
      if name ∈ names then moveTape (directions name) (tapes name) else tapes name := by
  induction names generalizing tapes with
  | nil => simp [moveTapes]
  | cons selected rest hypothesis =>
    have tailUnique := (List.nodup_cons.mp unique).2
    have selectedAbsent := (List.nodup_cons.mp unique).1
    by_cases equal : name = selected
    · subst name
      rw [moveTapes, moveTapes_outside rest directions _ selected selectedAbsent]
      simp [moveAt]
    · rw [moveTapes, hypothesis tailUnique]
      simp [moveAt, equal]

/-- On a complete catalogue, sequential marker operations implement simultaneous
source head movements; no tape is omitted or moved twice. -/
theorem moveTapes_eq (names : List TapeName) (unique : names.Nodup)
    (complete : ∀ name, name ∈ names) (directions : Directions TapeName) (tapes : Tapes Alphabet) :
    moveTapes names directions tapes = fun name => moveTape (directions name) (tapes name) := by
  funext name
  simp [moveTapes_apply names unique, complete]

/-- A finite sum of component controllers; no runtime size is stored here. -/
def Controller : List TapeName → Type
  | [] => Unit
  | _ :: rest => Sum MoveHead.Controller (Controller rest)

def entry : (names : List TapeName) → Controller names
  | [] => ()
  | _ :: _rest => .inl (.inl 0)

def exit : (names : List TapeName) → Controller names
  | [] => ()
  | _ :: rest => .inr (exit rest)

instance controllerInhabited (names : List TapeName) : Inhabited (Controller names) := ⟨entry names⟩

instance controllerFintype (names : List TapeName) : Fintype (Controller names) := by
  induction names with
  | nil => exact inferInstanceAs (Fintype Unit)
  | cons name rest hypothesis =>
    letI := hypothesis
    exact inferInstanceAs (Fintype (Sum MoveHead.Controller (Controller rest)))

def skip : Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) MoveHead.Controller :=
  fun state symbols => if state = .inl 0 then some (.inr (.inr ()), stationary symbols) else none

def headMachine (selected : TapeName) (direction : Option Bool) :
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) MoveHead.Controller :=
  match direction with
  | none => skip
  | some moveRight => MoveHead.machine selected moveRight

def machine : (names : List TapeName) → Directions TapeName →
    Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet)) (Controller names)
  | [], _ => fun _ _ => none
  | name :: rest, directions =>
    sequence (headMachine name (directions name)) (machine rest directions) (entry rest)

@[simp] theorem head_halt (selected : TapeName) (direction : Option Bool)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    headMachine selected direction (.inr (.inr ())) symbols = none := by
  cases direction <;> simp [headMachine, skip]

@[simp] theorem halt (names : List TapeName) (directions : Directions TapeName)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    machine names directions (exit names) symbols = none := by
  induction names with
  | nil => rfl
  | cons name rest hypothesis =>
    simp [machine, exit, MultiTape.sequence, hypothesis]
    rfl

private theorem head_steps (selected : TapeName) (direction : Option Bool)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes) :
    ∃ finalRows ticks, finalRows.length ≤ rows.length + 2 ∧ ticks ≤ 4 * rows.length + 17 ∧
      Tracks.Represents finalRows (moveAt selected direction tapes) ∧
      Steps (headMachine selected direction) ticks
        (.inl 0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (.inr (.inr ()), Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  cases direction with
  | none =>
    refine ⟨rows, 1, by omega, by omega, by simpa using represented, ?_⟩
    exact Steps.next (by simp [step, headMachine, skip]) (.zero _)
  | some moveRight =>
    obtain ⟨finalRows, ticks, length, cost, correct, trace⟩ := MoveHead.steps selected moveRight represented
    exact ⟨finalRows, ticks, length.le, cost, correct, trace⟩

/-- A complete catalogue pass has linear row growth and polynomial transition
cost. Its tape count and controller are fixed before direction values and rows. -/
theorem steps (names : List TapeName) (directions : Directions TapeName)
    {rows : List (Tracks.Row Alphabet)} {tapes : Tapes Alphabet}
    (represented : Tracks.Represents rows tapes) :
    ∃ finalRows ticks, finalRows.length ≤ rows.length + 2 * names.length ∧
      ticks ≤ names.length * (4 * rows.length + 8 * names.length + 19) ∧
      Tracks.Represents finalRows (moveTapes names directions tapes) ∧
      Steps (machine names directions) ticks
        (entry names, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
        (exit names, Sweep.tape [Sweep.leftMarker] (finalRows.map Sweep.row ++ [Sweep.rightMarker])) := by
  induction names generalizing rows tapes with
  | nil => exact ⟨rows, 0, by simp, by simp, represented, .zero _⟩
  | cons name rest hypothesis =>
    obtain ⟨middle, firstTicks, middleLength, firstCost, firstCorrect, firstTrace⟩ :=
      head_steps name (directions name) represented
    obtain ⟨finalRows, secondTicks, finalLength, secondCost, correct, secondTrace⟩ := hypothesis firstCorrect
    refine ⟨finalRows, firstTicks + secondTicks + 1, ?_, ?_, correct, ?_⟩
    · simp only [List.length_cons]; omega
    · have monotone : 4 * middle.length + 8 * rest.length + 19 ≤
          4 * (rows.length + 2) + 8 * rest.length + 19 := by omega
      have suffixCost := secondCost.trans (Nat.mul_le_mul_left rest.length monotone)
      simp only [List.length_cons]
      nlinarith
    · exact sequence_steps _ _ _ firstTrace (head_halt name (directions name)) secondTrace

/-- Lift the finite family to one machine whose direction vector is runtime
controller memory. The program and controller type depend only on the catalogue. -/
def dispatch (names : List TapeName) : Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))
    (Directions TapeName × Controller names) :=
  fun state symbols => (machine names state.1 state.2 symbols).map fun command =>
    ((state.1, command.1), command.2)

@[simp] theorem dispatch_halt (names : List TapeName) (directions : Directions TapeName)
    (symbols : Symbols (fun _ : Unit => Sweep.Alphabet (Tracks.Row Alphabet))) :
    dispatch names (directions, exit names) symbols = none := by simp [dispatch]

/-- All source heads move on one TM0 with one polynomial bound, uniformly over
runtime direction vectors and track intervals. Stationary directions are included. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype TapeName] [∀ name, Fintype (Alphabet name)]
    (names : List TapeName) (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment directions (rows : List (Tracks.Row Alphabet)) tapes, Tracks.Represents rows tapes →
        rows.length ≤ MvPolynomial.eval assignment capacity →
        ∃ finalRows ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
          finalRows.length ≤ rows.length + 2 * names.length ∧
          Tracks.Represents finalRows (moveTapes names directions tapes) ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (dispatch names))))^[ticks]
            (some (SingleTape.configuration ((directions, entry names), Sweep.tape [Sweep.leftMarker]
              (rows.map Sweep.row ++ [Sweep.rightMarker])))) =
            some (SingleTape.configuration ((directions, exit names), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) ∧
          Turing.TM0.step (SingleTape.compile (dispatch names))
            (SingleTape.configuration ((directions, exit names), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker]))) = none := by
  refine ⟨MvPolynomial.C (2 * names.length) * (4 * capacity + MvPolynomial.C (8 * names.length + 19)), ?_⟩
  intro assignment directions rows tapes represented bounded
  obtain ⟨finalRows, ticks, length, cost, correct, trace⟩ := steps names directions represented
  have lifted := trace.rename (fun state => (directions, state)) (target := dispatch names)
    (by intro state symbols next actions transition; simp [dispatch, transition])
  refine ⟨finalRows, 2 * ticks, ?_, length, correct, SingleTape.steps (dispatch names) lifted, ?_⟩
  · have capacityBound : 4 * rows.length + 8 * names.length + 19 ≤
        4 * MvPolynomial.eval assignment capacity + (8 * names.length + 19) := by omega
    have multiplied := Nat.mul_le_mul_left names.length capacityBound
    simp only [map_mul, map_add, map_ofNat, MvPolynomial.eval_C]
    nlinarith
  · exact SingleTape.halt (dispatch names) _ (by simp [step])

end Polytime2.MoveAll
