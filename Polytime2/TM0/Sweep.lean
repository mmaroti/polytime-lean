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


import Polytime2.TM0.SingleTape

/-! # Finite-state sweeps of a marked tape interval

A sweep transforms each row of an interval while updating finite controller
memory, then returns to the first row. This is the scan primitive needed to
collect marked heads and apply actions in a single-tape multi-track simulator.
The row count lives on tape, never in the finite controller.
-/

namespace Polytime2.Sweep

open MultiTape

-- symbolLevel: payload rows, which may contain one track per simulated tape.
-- memoryLevel: finite memory accumulated by a scan; parameterLevel: runtime sizes.
universe symbolLevel memoryLevel parameterLevel

variable {Symbol : Type symbolLevel} {Memory : Type memoryLevel}

abbrev Alphabet (Symbol : Type symbolLevel) := Option (Sum Bool Symbol)
abbrev Controller (Memory : Type memoryLevel) := Sum (Bool × Memory) Memory

/-- Left/right markers are distinct from every payload row and from blank. -/
def leftMarker : Alphabet Symbol := some (.inl false)
def rightMarker : Alphabet Symbol := some (.inl true)
def row (symbol : Symbol) : Alphabet Symbol := some (.inr symbol)

def isLeft : Alphabet Symbol → Bool
  | some (.inl false) => true
  | _ => false

def run (visit : Memory → Symbol → Memory × Symbol) : Memory → List Symbol → Memory × List Symbol
  | memory, [] => (memory, [])
  | memory, symbol :: rest =>
    let next := visit memory symbol
    let tail := run visit next.1 rest
    (tail.1, next.2 :: tail.2)

@[simp] theorem run_length (visit : Memory → Symbol → Memory × Symbol)
    (memory : Memory) (payload : List Symbol) : (run visit memory payload).2.length = payload.length := by
  induction payload generalizing memory with
  | nil => rfl
  | cons symbol rest hypothesis => simp [run, hypothesis]

def machine (visit : Memory → Symbol → Memory × Symbol) :
    Machine (fun _ : Unit => Alphabet Symbol) (Controller Memory)
  | .inl (false, memory), symbols => match symbols () with
    | some (.inr symbol) =>
      let next := visit memory symbol
      some (.inl (false, next.1), fun _ => (row next.2, some .right))
    | some (.inl true) => some (.inl (true, memory), fun _ => (rightMarker, none))
    | _ => none
  | .inl (true, memory), symbols =>
    if isLeft (symbols ()) then some (.inr memory, fun _ => (leftMarker, some .right))
    else some (.inl (true, memory), fun _ => (symbols (), some .left))
  | .inr _, _ => none

def tape (left right : List (Alphabet Symbol)) : Tapes (fun _ : Unit => Alphabet Symbol) :=
  fun _ => Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)

private theorem forward (visit : Memory → Symbol → Memory × Symbol)
    (memory : Memory) (payload : List Symbol) (left right : List (Alphabet Symbol)) :
    Steps (machine visit) payload.length
      (.inl (false, memory), tape left (payload.map row ++ right))
      (.inl (false, (run visit memory payload).1),
        tape ((run visit memory payload).2.reverse.map row ++ left) right) := by
  induction payload generalizing memory left with
  | nil => exact .zero _
  | cons symbol rest hypothesis =>
    have first : step (machine visit)
        (.inl (false, memory), tape left (row symbol :: (rest.map row ++ right))) =
        some (.inl (false, (visit memory symbol).1),
          tape (row (visit memory symbol).2 :: left) (rest.map row ++ right)) := by
      simp [step, machine, MultiTape.read, tape, row]
      congr 2
    have remaining := hypothesis (visit memory symbol).1 (row (visit memory symbol).2 :: left)
    simpa [run, List.map_cons, List.cons_append, List.reverse_cons, List.map_append,
      List.append_assoc] using Steps.next first remaining

private theorem rewind (visit : Memory → Symbol → Memory × Symbol)
    (memory : Memory) (payload : List Symbol) (current : Alphabet Symbol) (notLeft : isLeft current = false)
    (left right : List (Alphabet Symbol)) :
    Steps (machine visit) (payload.length + 2)
      (.inl (true, memory), tape (payload.map row ++ leftMarker :: left) (current :: right))
      (.inr memory, tape (leftMarker :: left) ((payload.map row).reverse ++ current :: right)) := by
  induction payload generalizing current right with
  | nil =>
    have first : step (machine visit)
        (.inl (true, memory), tape (leftMarker :: left) (current :: right)) =
        some (.inl (true, memory), tape left (leftMarker :: current :: right)) := by
      simp [step, machine, MultiTape.read, tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step (machine visit)
        (.inl (true, memory), tape left (leftMarker :: current :: right)) =
        some (.inr memory, tape (leftMarker :: left) (current :: right)) := by
      simp [step, machine, MultiTape.read, tape, leftMarker, isLeft]
      funext name
      cases name
      simp [MultiTape.act, tape, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    exact Steps.next first (Steps.next second (.zero _))
  | cons symbol rest hypothesis =>
    have first : step (machine visit)
        (.inl (true, memory), tape (row symbol :: (rest.map row ++ leftMarker :: left)) (current :: right)) =
        some (.inl (true, memory), tape (rest.map row ++ leftMarker :: left) (row symbol :: current :: right)) := by
      simp [step, machine, MultiTape.read, tape, notLeft]
      funext name
      cases name
      simp [MultiTape.act, tape, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have remaining := hypothesis (row symbol) (by rfl) (current :: right)
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using Steps.next first remaining

/-- Transform every row, then restore the head to the first row. Empty intervals
are allowed; neither marker nor either neighboring region is modified. -/
theorem steps (visit : Memory → Symbol → Memory × Symbol)
    (memory : Memory) (payload : List Symbol) (left right : List (Alphabet Symbol)) :
    Steps (machine visit) (2 * payload.length + 3)
      (.inl (false, memory), tape (leftMarker :: left) (payload.map row ++ rightMarker :: right))
      (.inr (run visit memory payload).1,
        tape (leftMarker :: left) ((run visit memory payload).2.map row ++ rightMarker :: right)) := by
  have scanned := forward visit memory payload (leftMarker :: left) (rightMarker :: right)
  have turn : step (machine visit)
      (.inl (false, (run visit memory payload).1),
        tape ((run visit memory payload).2.reverse.map row ++ leftMarker :: left) (rightMarker :: right)) =
      some (.inl (true, (run visit memory payload).1),
        tape ((run visit memory payload).2.reverse.map row ++ leftMarker :: left) (rightMarker :: right)) := by
    simp [step, machine, MultiTape.read, tape, rightMarker]
    funext name
    cases name
    simp [MultiTape.act, tape, Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  have returned := rewind visit (run visit memory payload).1 (run visit memory payload).2.reverse
    rightMarker (by rfl) left right
  simpa [List.map_reverse, run_length, Nat.two_mul, Nat.add_assoc] using
    scanned.trans (Steps.next turn returned)

instance [Inhabited Memory] : Inhabited (Controller Memory) := ⟨.inr default⟩

/-- A sweep is a finite-controller TM0 routine with exact linear cost. -/
theorem tm0_steps [Inhabited Memory] [Fintype Memory] [Fintype Symbol] (visit : Memory → Symbol → Memory × Symbol)
    (memory : Memory) (payload : List Symbol) (left right : List (Alphabet Symbol)) :
    (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine visit))))^[4 * payload.length + 6]
      (some (SingleTape.configuration
        (.inl (false, memory), tape (leftMarker :: left) (payload.map row ++ rightMarker :: right)))) =
      some (SingleTape.configuration (.inr (run visit memory payload).1,
        tape (leftMarker :: left) ((run visit memory payload).2.map row ++ rightMarker :: right))) ∧
      Turing.TM0.step (SingleTape.compile (machine visit))
        (SingleTape.configuration (.inr (run visit memory payload).1,
          tape (leftMarker :: left) ((run visit memory payload).2.map row ++ rightMarker :: right))) = none := by
  constructor
  · have cost : 4 * payload.length + 6 = 2 * (2 * payload.length + 3) := by omega
    rw [cost]
    exact SingleTape.steps (machine visit) (steps visit memory payload left right)
  · exact SingleTape.halt (machine visit) _ (by simp [step, machine])

/-- Uniform polynomial certificate for marked sweeps on TM0. The row alphabet,
visitor, and finite memory are fixed before runtime interval lengths. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    [Inhabited Memory] [Fintype Memory] [Fintype Symbol]
    (visit : Memory → Symbol → Memory × Symbol) (capacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment memory (payload : List Symbol) left right,
        payload.length ≤ MvPolynomial.eval assignment capacity →
        ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
          (fun current => current.bind (Turing.TM0.step (SingleTape.compile (machine visit))))^[ticks]
            (some (SingleTape.configuration
              (.inl (false, memory), tape (leftMarker :: left) (payload.map row ++ rightMarker :: right)))) =
            some (SingleTape.configuration (.inr (run visit memory payload).1,
              tape (leftMarker :: left) ((run visit memory payload).2.map row ++ rightMarker :: right))) ∧
          Turing.TM0.step (SingleTape.compile (machine visit))
            (SingleTape.configuration (.inr (run visit memory payload).1,
              tape (leftMarker :: left) ((run visit memory payload).2.map row ++ rightMarker :: right))) = none := by
  refine ⟨4 * capacity + 6, ?_⟩
  intro assignment memory payload left right bounded
  refine ⟨4 * payload.length + 6, ?_, tm0_steps visit memory payload left right⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.Sweep
