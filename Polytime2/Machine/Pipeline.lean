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

import Polytime2.Machine.Basic
import Polytime2.Machine.CallingConvention
import Mathlib.Tactic.Linarith

/-! # Fixed finite pipelines

A pipeline hides controller injections and handovers behind stage contracts.
The number of stages and every local controller are fixed before runtime sizes.
-/

namespace Polytime2.MultiTape.Pipeline

-- tapeLevel: tape names; symbolLevel: alphabets; stateLevel: local controllers.
universe tapeLevel symbolLevel stateLevel
variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)] {count : ℕ}
variable {LocalState : Fin count → Type stateLevel}

abbrev State (LocalState : Fin count → Type stateLevel) := Option ((index : Fin count) × LocalState index)

def position (entries : ∀ index, LocalState index) (index : Fin (count + 1)) : State LocalState :=
  if active : index.val < count then some ⟨⟨index.val, active⟩, entries ⟨index.val, active⟩⟩ else none

def machine (components : ∀ index, Machine Alphabet (LocalState index))
    (entries : ∀ index, LocalState index) : Machine Alphabet (State LocalState) :=
  fun state symbols => match state with
  | none => none
  | some ⟨index, localState⟩ => match components index localState symbols with
    | some command => some (some ⟨index, command.1⟩, command.2)
    | none => some (position entries ⟨index.val + 1, by omega⟩, stationary symbols)

/-- Each stage establishes the next stage's representation. Controllers,
handover transitions, and the total transition count remain inside this rule. -/
theorem steps (components : ∀ index, Machine Alphabet (LocalState index))
    (entries exits : ∀ index, LocalState index)
    (representation : Fin (count + 1) → Tapes Alphabet → Prop) (allowance : ℕ)
    (halt : ∀ index symbols, components index (exits index) symbols = none)
    (runs : ∀ index tapes, representation ⟨index.val, by omega⟩ tapes →
      ∃ ticks final, ticks ≤ allowance ∧ Steps (components index) ticks
        (entries index, tapes) (exits index, final) ∧ representation ⟨index.val + 1, by omega⟩ final)
    (initial : Tapes Alphabet) (represented : representation 0 initial) :
    ∃ ticks final, ticks ≤ count * (allowance + 1) ∧
      Steps (machine components entries) ticks (position entries 0, initial) (none, final) ∧
      representation (Fin.last count) final := by
  have suffix : ∀ remaining (index : Fin (count + 1)), count - index.val = remaining →
      ∀ tapes, representation index tapes →
      ∃ ticks final, ticks ≤ remaining * (allowance + 1) ∧
        Steps (machine components entries) ticks (position entries index, tapes) (none, final) ∧
        representation (Fin.last count) final := by
    intro remaining
    induction remaining with
    | zero =>
      intro index equal tapes valid
      have finished : index = Fin.last count := Fin.ext (by have bounded := index.isLt; simp; omega)
      subst index
      refine ⟨0, tapes, by omega, ?_, valid⟩
      simpa [position] using Steps.zero (machine := machine components entries) (none, tapes)
    | succ remaining hypothesis =>
      intro index equal tapes valid
      have active : index.val < count := by omega
      let stage : Fin count := ⟨index.val, active⟩
      obtain ⟨stageTicks, middle, cost, trace, nextValid⟩ := runs stage tapes valid
      have lifted := trace.rename (fun state => some (⟨stage, state⟩ : (i : Fin count) × LocalState i))
        (target := machine components entries)
        (by intro state symbols next actions transition; simp [machine, transition])
      have handover : step (machine components entries) (some ⟨stage, exits stage⟩, middle) =
          some (position entries ⟨index.val + 1, by omega⟩, middle) := by
        simp [step, machine, halt, act_stationary, stage]
      obtain ⟨restTicks, final, restCost, restTrace, finalValid⟩ :=
        hypothesis ⟨index.val + 1, by omega⟩ (by change count - (index.val + 1) = remaining; omega) middle nextValid
      refine ⟨stageTicks + (restTicks + 1), final, ?_, ?_, finalValid⟩
      · nlinarith
      · have started : position entries index = some ⟨stage, entries stage⟩ := by simp [position, active, stage]
        rw [started]
        exact lifted.trans (.next handover restTrace)
  simpa using suffix count 0 (by simp) initial represented

/-- A fixed pipeline also preserves immutable inputs and blank surroundings
at every transition. Component heads return to zero before each handover. -/
theorem runs (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (components : ∀ index, Machine (CallingConvention.Alphabet TapeName) (LocalState index))
    (entries exits : ∀ index, LocalState index)
    (representation : Fin (count + 1) → Tapes (CallingConvention.Alphabet TapeName) → Prop)
    (allowance : ℕ)
    (halt : ∀ index symbols, components index (exits index) symbols = none)
    (execute : ∀ index tapes, representation ⟨index.val, by omega⟩ tapes →
      ∃ ticks final, ticks ≤ allowance ∧ CallingConvention.Runs width readOnly
        (components index) ticks (entries index) (fun _ => 0) tapes
        (exits index) (fun _ => 0) final ∧ representation ⟨index.val + 1, by omega⟩ final)
    (initial : Tapes (CallingConvention.Alphabet TapeName)) (represented : representation 0 initial) :
    ∃ ticks final, ticks ≤ count * (allowance + 1) ∧
      CallingConvention.Runs width readOnly (machine components entries) ticks
        (position entries 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      representation (Fin.last count) final := by
  have suffix : ∀ remaining (index : Fin (count + 1)), count - index.val = remaining →
      ∀ tapes, representation index tapes →
      ∃ ticks final, ticks ≤ remaining * (allowance + 1) ∧
        CallingConvention.Runs width readOnly (machine components entries) ticks
          (position entries index) (fun _ => 0) tapes none (fun _ => 0) final ∧
        representation (Fin.last count) final := by
    intro remaining
    induction remaining with
    | zero =>
      intro index equal tapes valid
      have finished : index = Fin.last count := Fin.ext (by have bounded := index.isLt; simp; omega)
      subst index
      refine ⟨0, tapes, by omega, ?_, valid⟩
      simpa [position] using CallingConvention.Runs.zero
        (machine := machine components entries) none (fun _ => 0) tapes
    | succ remaining hypothesis =>
      intro index equal tapes valid
      have active : index.val < count := by omega
      let stage : Fin count := ⟨index.val, active⟩
      obtain ⟨stageTicks, middle, cost, trace, nextValid⟩ := execute stage tapes valid
      have lifted := trace.rename (fun state => some (⟨stage, state⟩ : (i : Fin count) × LocalState i))
        (target := machine components entries)
        (by intro state symbols next actions transition; simp [machine, transition])
      have handover : CallingConvention.Runs width readOnly (machine components entries) 1
          (some ⟨stage, exits stage⟩) (fun _ => 0) middle
          (position entries ⟨index.val + 1, by omega⟩) (fun _ => 0) middle := by
        apply CallingConvention.Runs.next
          (nextState := position entries ⟨index.val + 1, by omega⟩)
          (actions := stationary (read middle))
          (by simp [machine, halt, stage]) (by intro name premise; rfl)
        simpa only [stationary, CallingConvention.displacement, add_zero, act_stationary] using
          CallingConvention.Runs.zero (machine := machine components entries)
            (position entries ⟨index.val + 1, by omega⟩) (fun _ => 0) middle
      obtain ⟨restTicks, final, restCost, restTrace, finalValid⟩ :=
        hypothesis ⟨index.val + 1, by omega⟩ (by change count - (index.val + 1) = remaining; omega) middle nextValid
      refine ⟨stageTicks + (1 + restTicks), final, ?_, ?_, finalValid⟩
      · nlinarith
      · have started : position entries index = some ⟨stage, entries stage⟩ := by simp [position, active, stage]
        rw [started]
        exact lifted.trans (handover.trans restTrace)
  simpa using suffix count 0 (by simp) initial represented

/-- Formatting distinct writable destinations needs only their preserved
regions and immutable source tapes. The finite pipeline establishes every
destination's selected word, independently of all old writable contents. -/
theorem updates_runs [DecidableEq TapeName]
    (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (components : ∀ index, Machine (CallingConvention.Alphabet TapeName) (LocalState index))
    (entries exits : ∀ index, LocalState index)
    (target : Fin count → TapeName) (distinct : Function.Injective target)
    (expected : Fin count → Turing.Tape Binary.Symbol) (allowance : ℕ)
    (halt : ∀ index symbols, components index (exits index) symbols = none)
    (initial : Tapes (CallingConvention.Alphabet TapeName))
    (regions : ∀ name, CallingConvention.Region (width name) 0 (initial name))
    (execute : ∀ index tapes,
      (∀ name, readOnly name = true → tapes name = initial name) →
      (∀ name, CallingConvention.Region (width name) 0 (tapes name)) →
      ∃ ticks, ticks ≤ allowance ∧ CallingConvention.Runs width readOnly (components index) ticks
        (entries index) (fun _ => 0) tapes (exits index) (fun _ => 0)
        (Function.update tapes (target index) (expected index))) :
    ∃ ticks final, ticks ≤ count * (allowance + 1) ∧
      CallingConvention.Runs width readOnly (machine components entries) ticks
        (position entries 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      ∀ index, final (target index) = expected index := by
  let representation : Fin (count + 1) → Tapes (CallingConvention.Alphabet TapeName) → Prop := fun stage tapes =>
    (∀ name, readOnly name = true → tapes name = initial name) ∧
      (∀ name, CallingConvention.Region (width name) 0 (tapes name)) ∧
      (∀ previous : Fin count, previous.val < stage.val → tapes (target previous) = expected previous)
  obtain ⟨ticks, final, cost, trace, finalValid⟩ := runs width readOnly components entries exits representation allowance halt
    (by
      intro stage tapes valid
      obtain ⟨immutable, currentRegions, prepared⟩ := valid
      obtain ⟨ticks, cost, trace⟩ := execute stage tapes immutable currentRegions
      refine ⟨ticks, _, cost, trace, ?_, ?_, ?_⟩
      · intro name readonly
        exact (trace.readOnly_tape name readonly).trans (immutable name readonly)
      · intro name
        exact trace.region name (currentRegions name)
      · intro previous before
        by_cases current : previous = stage
        · subst previous
          exact Function.update_self _ _ _
        · have earlier : previous.val < stage.val := by
            have unequal : previous.val ≠ stage.val := fun equal => current (Fin.ext equal)
            change previous.val < stage.val + 1 at before
            omega
          exact (Function.update_of_ne (fun equal => current (distinct equal)) _ _).trans (prepared previous earlier))
    initial ⟨(by intro name readonly; rfl), regions, (by intro previous before; change previous.val < 0 at before; omega)⟩
  exact ⟨ticks, final, cost, trace, fun index => finalValid.2.2 index index.isLt⟩

end Polytime2.MultiTape.Pipeline
