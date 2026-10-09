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

-- u: tape symbols; v: source-controller states; w: target-controller states.
universe u v w

variable {Symbol : Type u} {State : Type v} [Inhabited Symbol] [Inhabited State]

abbrev Configuration (Symbol : Type u) (State : Type v) [Inhabited Symbol] :=
  Turing.TM0.Cfg Symbol State

def configuration (state : State) (left right : List Symbol) : Configuration Symbol State :=
  ⟨state, Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right)⟩

omit [Inhabited State] in
/-- Explicitly showing a trailing blank does not change a half-tape. -/
@[simp] theorem configuration_append_blank (state : State) (left right : List Symbol) :
    configuration state (left ++ [default]) right = configuration state left right := by
  have equality : Turing.ListBlank.mk (left ++ [default]) = Turing.ListBlank.mk left := by
    apply Quotient.sound
    exact Or.inr ⟨1, by simp⟩
  simp only [configuration, equality]

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

/-- Reuse a counted routine inside another controller without changing its cost. -/
theorem Steps.map {TargetState : Type w} [Inhabited TargetState]
    {machine : Turing.TM0.Machine Symbol State}
    {targetMachine : Turing.TM0.Machine Symbol TargetState}
    (embed : Configuration Symbol State → Configuration Symbol TargetState)
    (simulation : ∀ initial middle, Turing.TM0.step machine initial = some middle →
      Turing.TM0.step targetMachine (embed initial) = some (embed middle))
    {ticks : ℕ} {initial final : Configuration Symbol State}
    (trace : Steps machine ticks initial final) :
    Steps targetMachine ticks (embed initial) (embed final) := by
  induction trace with
  | zero => exact .zero _
  | next transition rest hypothesis => exact .next (simulation _ _ transition) hypothesis

/-- A change of finite controller preserves every tape transition. -/
theorem Steps.rename {TargetState : Type w} [Inhabited TargetState]
    {machine : Turing.TM0.Machine Symbol State}
    {targetMachine : Turing.TM0.Machine Symbol TargetState}
    (rename : State → TargetState)
    (instruction : ∀ state symbol next action, machine state symbol = some (next, action) →
      targetMachine (rename state) symbol = some (rename next, action))
    {ticks : ℕ} {initial final : Configuration Symbol State}
    (trace : Steps machine ticks initial final) :
    Steps targetMachine ticks ⟨rename initial.q, initial.Tape⟩
      ⟨rename final.q, final.Tape⟩ := by
  apply trace.map (fun source => ⟨rename source.q, source.Tape⟩)
  intro initial middle transition
  obtain ⟨state, tape⟩ := initial
  cases equation : machine state tape.1 with
  | none => simp [Turing.TM0.step, equation] at transition
  | some command =>
    obtain ⟨next, action⟩ := command
    have transferred := instruction state tape.1 next action equation
    simp only [Turing.TM0.step, equation, Option.map_some, Option.some.injEq] at transition
    subst middle
    simp [Turing.TM0.step, transferred]

/-- Reuse a routine up to its exit state, even when the target controller
changes instructions in later phases. Earlier phases cannot be re-entered. -/
theorem Steps.rename_until {TargetState : Type w} [Inhabited TargetState]
    {machine : Turing.TM0.Machine Symbol State}
    {targetMachine : Turing.TM0.Machine Symbol TargetState}
    (rename : State → TargetState) (allowed : State → Prop)
    (predecessor : ∀ state symbol next action, machine state symbol = some (next, action) →
      allowed next → allowed state)
    (instruction : ∀ state symbol next action, allowed state → allowed next →
      machine state symbol = some (next, action) →
      targetMachine (rename state) symbol = some (rename next, action))
    {ticks : ℕ} {initial final : Configuration Symbol State}
    (trace : Steps machine ticks initial final) (exit : allowed final.q) :
    allowed initial.q ∧
      Steps targetMachine ticks ⟨rename initial.q, initial.Tape⟩
        ⟨rename final.q, final.Tape⟩ := by
  induction trace with
  | zero => exact ⟨exit, .zero _⟩
  | @next count initial middle final transition rest hypothesis =>
    obtain ⟨middleAllowed, transferred⟩ := hypothesis exit
    cases equation : machine initial.q initial.Tape.1 with
    | none => simp [Turing.TM0.step, equation] at transition
    | some command =>
      obtain ⟨next, action⟩ := command
      simp only [Turing.TM0.step, equation, Option.map_some, Option.some.injEq] at transition
      subst middle
      have initialAllowed := predecessor initial.q initial.Tape.1 next action equation middleAllowed
      refine ⟨initialAllowed, .next ?_ transferred⟩
      simp [Turing.TM0.step, instruction _ _ _ _ initialAllowed middleAllowed equation]

/-- Reuse a later routine whose phases are closed under its transitions. -/
theorem Steps.rename_from {TargetState : Type w} [Inhabited TargetState]
    {machine : Turing.TM0.Machine Symbol State}
    {targetMachine : Turing.TM0.Machine Symbol TargetState}
    (rename : State → TargetState) (allowed : State → Prop)
    (successor : ∀ state symbol next action, allowed state →
      machine state symbol = some (next, action) → allowed next)
    (instruction : ∀ state symbol next action, allowed state →
      machine state symbol = some (next, action) →
      targetMachine (rename state) symbol = some (rename next, action))
    {ticks : ℕ} {initial final : Configuration Symbol State}
    (trace : Steps machine ticks initial final) (entry : allowed initial.q) :
    Steps targetMachine ticks ⟨rename initial.q, initial.Tape⟩
      ⟨rename final.q, final.Tape⟩ := by
  induction trace with
  | zero => exact .zero _
  | @next count initial middle final transition rest hypothesis =>
    cases equation : machine initial.q initial.Tape.1 with
    | none => simp [Turing.TM0.step, equation] at transition
    | some command =>
      obtain ⟨next, action⟩ := command
      simp only [Turing.TM0.step, equation, Option.map_some, Option.some.injEq] at transition
      subst middle
      refine .next ?_ (hypothesis (successor _ _ _ _ entry equation))
      simp [Turing.TM0.step, instruction _ _ _ _ entry equation]

/-- Run the second finite controller after the first halts. The handoff is
one write of the current symbol, so it preserves the entire tape. -/
def sequence {SecondState : Type w} [Inhabited SecondState] (first : Turing.TM0.Machine Symbol State)
    (second : Turing.TM0.Machine Symbol SecondState) (entry : SecondState) :
    Turing.TM0.Machine Symbol (Sum State SecondState)
  | .inl state, symbol => match first state symbol with
    | some (next, action) => some (.inl next, action)
    | none => some (.inr entry, .write symbol)
  | .inr state, symbol => (second state symbol).map fun (next, action) => (.inr next, action)

theorem sequence_steps {SecondState : Type w} [Inhabited SecondState]
    {first : Turing.TM0.Machine Symbol State} {second : Turing.TM0.Machine Symbol SecondState}
    {firstCount secondCount : ℕ} {initial middle : Configuration Symbol State}
    {final : Configuration Symbol SecondState} (entry : SecondState)
    (firstTrace : Steps first firstCount initial middle)
    (halts : ∀ symbol, first middle.q symbol = none)
    (secondTrace : Steps second secondCount ⟨entry, middle.Tape⟩ final) :
    Steps (sequence first second entry) (firstCount + (secondCount + 1))
      ⟨.inl initial.q, initial.Tape⟩ ⟨.inr final.q, final.Tape⟩ := by
  have leftTrace := firstTrace.rename Sum.inl
    (targetMachine := sequence first second entry)
    (by intro state symbol next action transition; simp [sequence, transition])
  have rightTrace := secondTrace.rename Sum.inr
    (targetMachine := sequence first second entry)
    (by intro state symbol next action transition; simp [sequence, transition])
  have handoff : Turing.TM0.step (sequence first second entry) ⟨.inl middle.q, middle.Tape⟩ =
      some ⟨.inr entry, middle.Tape⟩ := by
    simp [Turing.TM0.step, sequence, halts, Turing.Tape.write_self]
  exact leftTrace.trans (.next handoff rightTrace)

/-- Compose after a halt on the actual tape, as needed when a while loop stops
on its false result bit. Other symbols need not halt the first controller. -/
theorem sequence_steps_of_halt {SecondState : Type w} [Inhabited SecondState]
    {first : Turing.TM0.Machine Symbol State} {second : Turing.TM0.Machine Symbol SecondState}
    {firstCount secondCount : ℕ} {initial middle : Configuration Symbol State}
    {final : Configuration Symbol SecondState} (entry : SecondState)
    (firstTrace : Steps first firstCount initial middle)
    (halts : Turing.TM0.step first middle = none)
    (secondTrace : Steps second secondCount ⟨entry, middle.Tape⟩ final) :
    Steps (sequence first second entry) (firstCount + (secondCount + 1))
      ⟨.inl initial.q, initial.Tape⟩ ⟨.inr final.q, final.Tape⟩ := by
  have command : first middle.q middle.Tape.head = none := by
    simpa only [Turing.TM0.step, Option.map_eq_none_iff] using halts
  have leftTrace := firstTrace.rename Sum.inl
    (targetMachine := sequence first second entry)
    (by intro state symbol next action transition; simp [sequence, transition])
  have rightTrace := secondTrace.rename Sum.inr
    (targetMachine := sequence first second entry)
    (by intro state symbol next action transition; simp [sequence, transition])
  have handoff : Turing.TM0.step (sequence first second entry) ⟨.inl middle.q, middle.Tape⟩ =
      some ⟨.inr entry, middle.Tape⟩ := by
    simp [Turing.TM0.step, sequence, command, Turing.Tape.write_self]
  exact leftTrace.trans (.next handoff rightTrace)

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

/-- Change controller state while preserving the tape and head position. -/
theorem stay (left right : List Symbol)
    (transition : ∀ symbol, machine state symbol = some (nextState, .write symbol)) :
    Turing.TM0.step machine (configuration state left right) =
      some (configuration nextState left right) := by
  simp only [Turing.TM0.step, configuration, transition, Option.map_some, Turing.Tape.write_self]

/-- Move left without needing to expose the current symbol in the proof. -/
theorem move_left_list (left right : List Symbol) (symbol : Symbol)
    (transition : ∀ current, machine state current = some (nextState, .move .left)) :
    Turing.TM0.step machine (configuration state (symbol :: left) right) =
      some (configuration nextState left (symbol :: right)) := by
  simp [Turing.TM0.step, configuration, transition, Turing.Tape.move_left_mk',
    Turing.ListBlank.tail_mk, Turing.ListBlank.head_mk, Turing.ListBlank.cons_mk]

theorem move_left_empty (right : List Symbol)
    (transition : ∀ symbol, machine state symbol = some (nextState, .move .left)) :
    Turing.TM0.step machine (configuration state [] right) =
      some (configuration nextState [] (default :: right)) := by
  simp [Turing.TM0.step, configuration, Turing.Tape.move_left_mk', transition,
    Turing.ListBlank.tail_mk, Turing.ListBlank.head_mk, Turing.ListBlank.cons_mk]

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

/-- Move left from a known current symbol, including into the blank left tail. -/
theorem move_left_headD (left right : List Symbol) (current : Symbol)
    (transition : machine state current = some (nextState, .move .left)) :
    Turing.TM0.step machine (configuration state left (current :: right)) =
      some (configuration nextState left.tail (left.headD default :: current :: right)) := by
  cases left with
  | nil =>
    have trace := move_left [] right default current transition
    have padding := configuration_append_blank state [] (current :: right)
    simp only [List.nil_append] at padding
    rw [padding] at trace
    simpa using trace
  | cons symbol rest => simpa using move_left rest right symbol current transition

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
