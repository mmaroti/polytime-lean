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


import Polytime2.Encoding

/-! # Standard TM0 initialization for marked-track inputs

The input word begins with its left boundary marker. A new default start state
moves right once and enters the simulator. Subsequent transitions are exactly
those of the supplied TM0 program, with its state tagged by `some`.
-/

namespace Polytime2.TM0Input

-- symbolLevel: the standard machine alphabet; stateLevel: its existing states.
universe symbolLevel stateLevel

variable {Symbol : Type symbolLevel} [Inhabited Symbol]
variable {State : Type stateLevel} [Inhabited State]

def machine (source : Turing.TM0.Machine Symbol State) (entry : State) :
    Turing.TM0.Machine Symbol (Option State)
  | none, _ => some (some entry, .move .right)
  | some state, symbol => (source state symbol).map fun command => (some command.1, command.2)

def embed (configuration : Turing.TM0.Cfg Symbol State) : Turing.TM0.Cfg Symbol (Option State) :=
  ⟨some configuration.q, configuration.Tape⟩

@[simp] theorem step_embed (source : Turing.TM0.Machine Symbol State) (entry : State)
    (configuration : Turing.TM0.Cfg Symbol State) :
    Turing.TM0.step (machine source entry) (embed configuration) =
      (Turing.TM0.step source configuration).map embed := by
  rcases configuration with ⟨state, tape⟩
  cases equation : source state tape.head with
  | none => simp [Turing.TM0.step, machine, embed, equation]
  | some command =>
    rcases command with ⟨next, instruction⟩
    cases instruction <;> simp [Turing.TM0.step, machine, embed, equation]

/-- Tagging controller states preserves the exact number of running transitions. -/
theorem steps (source : Turing.TM0.Machine Symbol State) (entry : State)
    {ticks : ℕ} {initial final : Turing.TM0.Cfg Symbol State}
    (trace : (fun current => current.bind (Turing.TM0.step source))^[ticks] (some initial) = some final) :
    (fun current => current.bind (Turing.TM0.step (machine source entry)))^[ticks]
      (some (embed initial)) = some (embed final) := by
  have commute : Function.Semiconj (Option.map embed)
      (fun current => current.bind (Turing.TM0.step source))
      (fun current => current.bind (Turing.TM0.step (machine source entry))) := by
    intro current
    cases current with
    | none => rfl
    | some configuration => simp
  have lifted := commute.iterate_right ticks (some initial)
  simpa only [trace, Option.map_some] using lifted.symm

/-- The standard `TM0.init` input convention costs one transition to reach the
prepared interval convention used by the simulator. -/
theorem startup_step {Row : Type symbolLevel}
    (source : Turing.TM0.Machine (Sweep.Alphabet Row) State) (entry : State) (rows : List Row) :
    Turing.TM0.step (machine source entry)
      (Turing.TM0.init (Sweep.leftMarker :: (rows.map Sweep.row ++ [Sweep.rightMarker]))) =
      some (embed ⟨entry, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]) ()⟩) := by
  have startState : (default : Option State) = none := rfl
  simp [Turing.TM0.step, machine, Turing.TM0.init, startState, Turing.Tape.mk₁, Turing.Tape.mk₂,
    Turing.Tape.move_right_mk', Sweep.tape, Turing.ListBlank.cons_mk, embed]

/-- Include startup in the counted trace, starting from `TM0.init` itself. -/
theorem initialized_steps {Row : Type symbolLevel}
    (source : Turing.TM0.Machine (Sweep.Alphabet Row) State) (entry : State)
    (rows : List Row) {ticks : ℕ} {final : Turing.TM0.Cfg (Sweep.Alphabet Row) State}
    (trace : (fun current => current.bind (Turing.TM0.step source))^[ticks]
      (some ⟨entry, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]) ()⟩) = some final) :
    (fun current => current.bind (Turing.TM0.step (machine source entry)))^[ticks + 1]
      (some (Turing.TM0.init (Sweep.leftMarker :: (rows.map Sweep.row ++ [Sweep.rightMarker])))) = some (embed final) := by
  rw [Function.iterate_succ_apply, Option.bind_some, startup_step]
  exact steps source entry trace

end Polytime2.TM0Input

namespace Polytime2.Simulation

open MultiTape

-- tapeLevel: source tape names; symbolLevel: their alphabets.
-- stateLevel: source controller; parameterLevel: runtime size names.
universe tapeLevel symbolLevel stateLevel parameterLevel

variable {TapeName : Type tapeLevel} [DecidableEq TapeName] [Fintype TapeName]
variable {Alphabet : TapeName → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]
variable [∀ name, Fintype (Alphabet name)] {State : Type stateLevel} [Fintype State]

/-- Polynomial certificate starting from Mathlib's standard `TM0.init`, including
its default start state and head position. Startup costs one extra transition. -/
theorem realizes_input {Parameter : Type parameterLevel} [Fintype Parameter]
    (names : List TapeName) (unique : names.Nodup) (complete : ∀ name, name ∈ names)
    {source : Machine Alphabet State} {sourceEntry sourceExit : State}
    {precondition : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {postcondition : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (certificate : Realizes source sourceEntry sourceExit precondition postcondition)
    (inputCapacity : MvPolynomial Parameter ℕ)
    (inputFits : ∀ assignment initial, precondition assignment initial →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name)) :
    let program := TM0Input.machine (SingleTape.compile (machine names source)) (.inl (entry names sourceEntry))
    ∃ timeBound rowBound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∃ ticks finalRows final, ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          postcondition assignment initial final ∧ Tracks.Represents finalRows final ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity) initial).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro program
  obtain ⟨timeBound, rowBound, runs⟩ := realizes_encoded names unique complete certificate inputCapacity inputFits
  refine ⟨timeBound + 1, rowBound, ?_⟩
  intro assignment initial valid
  obtain ⟨ticks, finalRows, final, time, space, correct, represented, trace, stopped⟩ := runs assignment initial valid
  refine ⟨ticks + 1, finalRows, final, ?_, space, correct, represented, ?_, ?_⟩
  · simp only [map_add, map_one]
    omega
  · exact TM0Input.initialized_steps _ _ _ trace
  · simp only [program, TM0Input.step_embed, stopped, Option.map_none]

end Polytime2.Simulation
