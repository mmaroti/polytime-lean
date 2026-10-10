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

import Mathlib.Computability.TuringMachine.Tape

/-! # Deterministic multi-tape machines

Each transition writes one symbol on every tape, then independently moves
each head left, right, or leaves it stationary. Tapes reuse Mathlib's
two-sided, eventually blank tape representation. Finiteness is imposed by
the polynomial-time certificate, rather than by these execution definitions.
The counted-trace composition proofs follow the pattern in `Polytime/Tape.lean`;
this module has no dependency on that implementation.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape names; symbolLevel: tape alphabets; stateLevel: controllers.
-- targetStateLevel: controllers into which execution is embedded.
universe tapeLevel symbolLevel stateLevel targetStateLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}

abbrev Symbols (Alphabet : TapeName → Type symbolLevel) := ∀ name, Alphabet name
abbrev Tapes (Alphabet : TapeName → Type symbolLevel) [∀ name, Inhabited (Alphabet name)] :=
  ∀ name, Turing.Tape (Alphabet name)
abbrev Actions (Alphabet : TapeName → Type symbolLevel) :=
  ∀ name, Alphabet name × Option Turing.Dir
abbrev Machine (Alphabet : TapeName → Type symbolLevel) (State : Type stateLevel) :=
  State → Symbols Alphabet → Option (State × Actions Alphabet)
abbrev Configuration (Alphabet : TapeName → Type symbolLevel) (State : Type stateLevel)
    [∀ name, Inhabited (Alphabet name)] := State × Tapes Alphabet

def read (tapes : Tapes Alphabet) : Symbols Alphabet := fun name => (tapes name).head

/-- Rewriting the current symbol without moving is a stationary action. -/
def stationary (symbols : Symbols Alphabet) : Actions Alphabet :=
  fun name => (symbols name, none)

def act (actions : Actions Alphabet) (tapes : Tapes Alphabet) : Tapes Alphabet :=
  fun name =>
    let written := (tapes name).write (actions name).1
    match (actions name).2 with
    | none => written
    | some direction => written.move direction

@[simp] theorem act_stationary (tapes : Tapes Alphabet) :
    act (stationary (read tapes)) tapes = tapes := by
  funext name
  simp [act, stationary, read, Turing.Tape.write_self]

@[simp] theorem act_move (tapes : Tapes Alphabet) (direction : Turing.Dir) :
    act (fun name => (read tapes name, some direction)) tapes =
      fun name => (tapes name).move direction := by
  funext name
  simp [act, read]

def step (machine : Machine Alphabet State) (configuration : Configuration Alphabet State) :
    Option (Configuration Alphabet State) :=
  (machine configuration.1 (read configuration.2)).map fun command =>
    (command.1, act command.2 configuration.2)

/-- Exactly the stated number of actual multi-tape transitions. -/
inductive Steps (machine : Machine Alphabet State) :
    ℕ → Configuration Alphabet State → Configuration Alphabet State → Prop
  | zero (configuration) : Steps machine 0 configuration configuration
  | next {count initial middle final}
      (transition : step machine initial = some middle)
      (rest : Steps machine count middle final) : Steps machine (count + 1) initial final

namespace Steps

variable {machine : Machine Alphabet State}

theorem trans {firstCount secondCount : ℕ} {initial middle final : Configuration Alphabet State}
    (first : Steps machine firstCount initial middle)
    (second : Steps machine secondCount middle final) :
    Steps machine (firstCount + secondCount) initial final := by
  induction first with
  | zero => simpa using second
  | next transition rest hypothesis =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      next transition (hypothesis second)

/-- A deterministic machine has a unique terminal configuration, regardless of trace length. -/
theorem final_eq {firstCount secondCount : ℕ}
    {initial firstFinal secondFinal : Configuration Alphabet State}
    (first : Steps machine firstCount initial firstFinal)
    (second : Steps machine secondCount initial secondFinal)
    (firstHalt : step machine firstFinal = none) (secondHalt : step machine secondFinal = none) :
    firstFinal = secondFinal := by
  induction first generalizing secondCount secondFinal with
  | zero configuration =>
    cases second with
    | zero => rfl
    | next transition rest => simp [firstHalt] at transition
  | next transition rest hypothesis =>
    cases second with
    | zero => simp [secondHalt] at transition
    | next otherTransition otherRest =>
      have same := Option.some.inj (transition.symm.trans otherTransition)
      cases same
      exact hypothesis otherRest firstHalt secondHalt

theorem map {TargetState : Type targetStateLevel}
    {target : Machine Alphabet TargetState}
    (embed : Configuration Alphabet State → Configuration Alphabet TargetState)
    (simulation : ∀ initial middle, step machine initial = some middle →
      step target (embed initial) = some (embed middle))
    {ticks : ℕ} {initial final : Configuration Alphabet State}
    (trace : Steps machine ticks initial final) :
    Steps target ticks (embed initial) (embed final) := by
  induction trace with
  | zero => exact .zero _
  | next transition rest hypothesis => exact .next (simulation _ _ transition) hypothesis

theorem rename {TargetState : Type targetStateLevel}
    {target : Machine Alphabet TargetState} (embed : State → TargetState)
    (instruction : ∀ state symbols next actions,
      machine state symbols = some (next, actions) →
        target (embed state) symbols = some (embed next, actions))
    {ticks : ℕ} {initial final : Configuration Alphabet State}
    (trace : Steps machine ticks initial final) :
    Steps target ticks (embed initial.1, initial.2) (embed final.1, final.2) := by
  apply trace.map (fun configuration => (embed configuration.1, configuration.2))
  intro initial middle transition
  rcases initial with ⟨state, tapes⟩
  cases equation : machine state (read tapes) with
  | none => simp [step, equation] at transition
  | some command =>
    rcases command with ⟨next, actions⟩
    have transferred := instruction state (read tapes) next actions equation
    simp only [step, equation, Option.map_some, Option.some.injEq] at transition
    subst middle
    simp [step, transferred]

end Steps

/-- Give every terminal configuration a common, unconditionally halting exit.
This costs one stationary transition and makes conditional halting composable. -/
def withExit (machine : Machine Alphabet State) : Machine Alphabet (Sum State Unit)
  | .inl state, symbols => match machine state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => some (.inr (), stationary symbols)
  | .inr (), _ => none

theorem withExit_steps (machine : Machine Alphabet State)
    {ticks : ℕ} {initial final : Configuration Alphabet State}
    (trace : Steps machine ticks initial final) (halt : step machine final = none) :
    Steps (withExit machine) (ticks + 1) (.inl initial.1, initial.2) (.inr (), final.2) := by
  have lifted := trace.rename Sum.inl (target := withExit machine)
    (by intro state symbols next actions transition; simp [withExit, transition])
  have terminal : machine final.1 (read final.2) = none := by
    cases equation : machine final.1 (read final.2) with
    | none => rfl
    | some command => simp [step, equation] at halt
  have handover : step (withExit machine) (.inl final.1, final.2) = some (.inr (), final.2) := by
    simp [step, withExit, terminal]
  exact lifted.trans (.next handover (.zero _))

section Sequencing

-- firstLevel and secondLevel: the component controller carriers.
universe firstLevel secondLevel
variable {First : Type firstLevel} {Second : Type secondLevel}

/-- One stationary transition hands control from the first controller to the second.
The first component's contract must return at a halting state. -/
def sequence (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (secondEntry : Second) : Machine Alphabet (Sum First Second)
  | .inl state, symbols => match first state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => some (.inr secondEntry, stationary symbols)
  | .inr state, symbols =>
    (second state symbols).map fun command => (.inr command.1, command.2)

theorem sequence_steps (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (secondEntry : Second) {firstEntry firstExit : First} {secondExit : Second}
    {initial middle final : Tapes Alphabet} {firstTicks secondTicks : ℕ}
    (firstTrace : Steps first firstTicks (firstEntry, initial) (firstExit, middle))
    (firstHalt : ∀ symbols, first firstExit symbols = none)
    (secondTrace : Steps second secondTicks (secondEntry, middle) (secondExit, final)) :
    Steps (sequence first second secondEntry) (firstTicks + secondTicks + 1)
      (.inl firstEntry, initial) (.inr secondExit, final) := by
  have liftedFirst := firstTrace.rename Sum.inl
    (target := sequence first second secondEntry)
    (by intro state symbols next actions transition; simp [sequence, transition])
  have liftedSecond := secondTrace.rename Sum.inr
    (target := sequence first second secondEntry)
    (by intro state symbols next actions transition; simp [sequence, transition])
  have handover : step (sequence first second secondEntry) (.inl firstExit, middle) =
      some (.inr secondEntry, middle) := by
    simp [step, sequence, firstHalt]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    liftedFirst.trans (.next handover liftedSecond)

end Sequencing
end Polytime2.MultiTape
