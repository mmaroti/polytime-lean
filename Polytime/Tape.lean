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

import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Tactic

/-! # Counted execution on Mathlib's deterministic tape machine

Each counted transition is one TM0 move or write. The lists in `configuration`
are proof notation for tapes, not atomic machine instructions.
-/

namespace Polytime.Tape

-- u: tape symbols; v: finite-controller states.
universe u v

variable {Symbol : Type u} {State : Type v} [Inhabited Symbol] [Inhabited State]

abbrev Configuration (Symbol : Type u) (State : Type v) [Inhabited Symbol] :=
  Turing.TM0.Cfg Symbol State

def configuration (state : State) (left right : List Symbol) : Configuration Symbol State :=
  ⟨state, Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)⟩

/-- Exactly this many actual tape transitions, without an abstract cost oracle. -/
inductive Steps (machine : Turing.TM0.Machine Symbol State) :
    ℕ → Configuration Symbol State → Configuration Symbol State → Prop
  | zero (configuration : Configuration Symbol State) : Steps machine 0 configuration configuration
  | next {count : ℕ} {initial middle final : Configuration Symbol State}
      (transition : Turing.TM0.step machine initial = some middle)
      (rest : Steps machine count middle final) : Steps machine (count + 1) initial final

namespace Steps

variable {machine : Turing.TM0.Machine Symbol State}

theorem trans {firstCount secondCount : ℕ} {initial middle final : Configuration Symbol State}
    (first : Steps machine firstCount initial middle)
    (second : Steps machine secondCount middle final) :
    Steps machine (firstCount + secondCount) initial final := by
  induction first with
  | zero => simpa using second
  | next transition rest hypothesis =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next transition (hypothesis second)

end Steps

/-- A bounded executable observer of machine runs; fuel is not a stopping
condition of the machine itself. -/
def run (machine : Turing.TM0.Machine Symbol State) :
    ℕ → Configuration Symbol State → Option (Configuration Symbol State)
  | 0, initial => (Turing.TM0.step machine initial).elim (some initial) (fun _ => none)
  | remaining + 1, initial => match Turing.TM0.step machine initial with
    | none => some initial
    | some next => run machine remaining next

theorem run_of_steps {machine : Turing.TM0.Machine Symbol State} {ticks fuel : ℕ}
    {initial final : Configuration Symbol State} (trace : Steps machine ticks initial final)
    (halts : Turing.TM0.step machine final = none) (enough : ticks ≤ fuel) :
    run machine fuel initial = some final := by
  induction trace generalizing fuel with
  | zero => cases fuel <;> simp [run, halts]
  | next transition rest hypothesis =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [run, transition]
      exact hypothesis halts (by omega)

variable {machine : Turing.TM0.Machine Symbol State} {state nextState : State}

theorem move_right (left right : List Symbol) (symbol : Symbol)
    (transition : machine state symbol = some (nextState, .move .right)) :
    Turing.TM0.step machine (configuration state left (symbol :: right)) =
      some (configuration nextState (symbol :: left) right) := by
  simp [Turing.TM0.step, configuration, Turing.Tape.mk', Turing.Tape.move, transition,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]

theorem move_left (left right : List Symbol) (symbol current : Symbol)
    (transition : machine state current = some (nextState, .move .left)) :
    Turing.TM0.step machine (configuration state (symbol :: left) (current :: right)) =
      some (configuration nextState left (symbol :: current :: right)) := by
  simp [Turing.TM0.step, configuration, Turing.Tape.mk', Turing.Tape.move, transition,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]

theorem write (left right : List Symbol) (symbol output : Symbol)
    (transition : machine state symbol = some (nextState, .write output)) :
    Turing.TM0.step machine (configuration state left (symbol :: right)) =
      some (configuration nextState left (output :: right)) := by
  simp [Turing.TM0.step, configuration, Turing.Tape.mk', Turing.Tape.write, transition,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk]

theorem scan_right (symbols left right : List Symbol)
    (transition : ∀ symbol ∈ symbols, machine state symbol = some (state, .move .right)) :
    Steps machine symbols.length (configuration state left (symbols ++ right))
      (configuration state (symbols.reverse ++ left) right) := by
  induction symbols generalizing left with
  | nil => exact .zero _
  | cons symbol symbols hypothesis =>
    simpa [List.reverse_cons, List.append_assoc] using
      Steps.next (move_right left (symbols ++ right) symbol (transition symbol (by simp)))
        (hypothesis (symbol :: left) (fun other member => transition other (by simp [member])))

theorem scan_left (symbols left right : List Symbol) (marker current : Symbol)
    (transition : ∀ symbol ∈ current :: symbols,
      machine state symbol = some (state, .move .left)) :
    Steps machine (symbols.length + 1)
      (configuration state (symbols ++ marker :: left) (current :: right))
      (configuration state left (marker :: (symbols.reverse ++ current :: right))) := by
  induction symbols generalizing current right with
  | nil => exact .next (move_left left right marker current (transition current (by simp))) (.zero _)
  | cons symbol symbols hypothesis =>
    have first := move_left (symbols ++ marker :: left) right symbol current
      (transition current (by simp))
    have rest := hypothesis (current :: right) symbol
      (fun other member => transition other (by simp at member ⊢; tauto))
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

end Polytime.Tape
