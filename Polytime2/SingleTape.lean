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


import Polytime2.Complexity
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-! # Exact realization of one-tape routines by Mathlib's TM0

Our transitions write and then optionally move. TM0 performs just one of those
operations per transition. A finite intermediate controller splits each source
transition into two TM0 transitions, including a stationary write when no move
is requested. This is the final translation layer for one-tape routines; it
alone does not simulate a collection of independent tapes.
-/

namespace Polytime2.SingleTape

open MultiTape

-- symbolLevel: tape alphabet; stateLevel: source controller.
-- parameterLevel: names of runtime sizes in polynomial certificates.
universe symbolLevel stateLevel parameterLevel

variable {Symbol : Type symbolLevel} [Inhabited Symbol]
variable {State : Type stateLevel} [Inhabited State]

abbrev Controller (State : Type stateLevel) := Sum State (State × Option Turing.Dir)

instance : Inhabited (Controller State) := ⟨.inl default⟩

instance [Fintype State] : Fintype (Controller State) := by
  letI : Fintype Turing.Dir := ⟨{.left, .right}, by intro direction; cases direction <;> simp⟩
  exact inferInstance

def compile (machine : Machine (fun _ : Unit => Symbol) State) :
    Turing.TM0.Machine Symbol (Controller State)
  | .inl state, symbol =>
    (machine state (fun _ => symbol)).map fun command =>
      (.inr (command.1, (command.2 ()).2), .write (command.2 ()).1)
  | .inr (state, none), symbol => some (.inl state, .write symbol)
  | .inr (state, some direction), _ => some (.inl state, .move direction)

def configuration (source : Configuration (fun _ : Unit => Symbol) State) :
    Turing.TM0.Cfg Symbol (Controller State) := ⟨.inl source.1, source.2 ()⟩

/-- One source write-and-move transition takes exactly two TM0 transitions. -/
theorem transition (machine : Machine (fun _ : Unit => Symbol) State)
    {initial final : Configuration (fun _ : Unit => Symbol) State}
    (source : step machine initial = some final) :
    (fun current => current.bind (Turing.TM0.step (compile machine)))^[2]
      (some (configuration initial)) = some (configuration final) := by
  rcases initial with ⟨state, tapes⟩
  cases equation : machine state (read tapes) with
  | none => simp [step, equation] at source
  | some command =>
    rcases command with ⟨next, actions⟩
    simp only [step, equation, Option.map_some, Option.some.injEq] at source
    subst final
    have symbols : (fun _ : Unit => (tapes ()).head) = read tapes := by
      funext name; cases name; rfl
    cases movement : (actions ()).2 with
    | none =>
      simp [Function.iterate_succ_apply, configuration, Turing.TM0.step, compile,
        symbols, equation, act, movement]
    | some direction =>
      simp [Function.iterate_succ_apply, configuration, Turing.TM0.step, compile,
        symbols, equation, act, movement]

/-- Exact counted simulation; the destination is a concrete TM0 configuration. -/
theorem steps (machine : Machine (fun _ : Unit => Symbol) State)
    {ticks : ℕ} {initial final : Configuration (fun _ : Unit => Symbol) State}
    (source : Steps machine ticks initial final) :
    (fun current => current.bind (Turing.TM0.step (compile machine)))^[2 * ticks]
      (some (configuration initial)) = some (configuration final) := by
  induction source with
  | zero => rfl
  | @next count initial middle final first rest hypothesis =>
    rw [Nat.mul_add, show 2 * 1 = 2 from rfl, Function.iterate_add_apply]
    rw [transition machine first, hypothesis]

/-- Source halting and TM0 halting agree at translated configurations. -/
theorem halt (machine : Machine (fun _ : Unit => Symbol) State)
    (source : Configuration (fun _ : Unit => Symbol) State)
    (stopped : step machine source = none) :
    Turing.TM0.step (compile machine) (configuration source) = none := by
  have symbols : (fun _ : Unit => (source.2 ()).head) = read source.2 := by
    funext name; cases name; rfl
  cases equation : machine source.1 (read source.2) with
  | none => simp [Turing.TM0.step, configuration, compile, symbols, equation]
  | some command => simp [step, equation] at stopped

/-- Every certified one-tape routine has a TM0 polynomial certificate with twice
its transition bound. The alphabet and both controller phases remain finite. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype Symbol] [Fintype State]
    {machine : Machine (fun _ : Unit => Symbol) State} {entry exit : State}
    {precondition : (Parameter → ℕ) → Tapes (fun _ : Unit => Symbol) → Prop}
    {postcondition : (Parameter → ℕ) → Tapes (fun _ : Unit => Symbol) →
      Tapes (fun _ : Unit => Symbol) → Prop}
    (certificate : MultiTape.Internal.Realizes machine entry exit precondition postcondition) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∃ ticks final, ticks ≤ MvPolynomial.eval assignment bound ∧
          (fun current => current.bind (Turing.TM0.step (compile machine)))^[ticks]
            (some (configuration (entry, initial))) = some (configuration (exit, final)) ∧
          Turing.TM0.step (compile machine) (configuration (exit, final)) = none ∧
          postcondition assignment initial final := by
  obtain ⟨stopped, bound, runs⟩ := certificate
  refine ⟨2 * bound, ?_⟩
  intro assignment initial valid
  obtain ⟨ticks, final, cost, trace, correct⟩ := runs assignment initial valid
  refine ⟨2 * ticks, final, ?_, steps machine trace, ?_, correct⟩
  · simpa only [map_mul, map_ofNat] using Nat.mul_le_mul_left 2 cost
  · exact halt machine (exit, final) (by simp [step, stopped])

end Polytime2.SingleTape
