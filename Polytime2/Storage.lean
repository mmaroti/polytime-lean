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

/-! # Storage bounds derived from counted execution

Bound the lengths of finite left and inclusive-right tape words. An empty
right word represents an implicit blank head. One write followed by one move
increases this bound by at most two cells per tape. Consequently polynomial
runtime and polynomial input storage give polynomial storage at every prefix
of execution, without a separate space estimate for each controller.
-/

namespace Polytime2.MultiTape

-- symbolLevel: a tape alphabet; tapeLevel: tape names; stateLevel: controllers.
universe symbolLevel tapeLevel stateLevel

/-- A finite representation around the current head, allowing trailing blanks. -/
def Fits {Symbol : Type symbolLevel} [Inhabited Symbol] (bound : ℕ) (tape : Turing.Tape Symbol) : Prop :=
  ∃ left right : List Symbol,
    tape = Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk right) ∧
      left.length + right.length ≤ bound

theorem Fits.write {Symbol : Type symbolLevel} [Inhabited Symbol] {bound : ℕ}
    {tape : Turing.Tape Symbol} (fits : Fits bound tape) (symbol : Symbol) :
    Fits (bound + 1) (tape.write symbol) := by
  obtain ⟨left, right, rfl, bounded⟩ := fits
  refine ⟨left, symbol :: right.tail, ?_, ?_⟩
  · simp [Turing.Tape.write_mk', Turing.ListBlank.cons_mk]
  · simp only [List.length_cons, List.length_tail]; omega

theorem Fits.move {Symbol : Type symbolLevel} [Inhabited Symbol] {bound : ℕ}
    {tape : Turing.Tape Symbol} (fits : Fits bound tape) (direction : Turing.Dir) :
    Fits (bound + 1) (tape.move direction) := by
  obtain ⟨left, right, rfl, bounded⟩ := fits
  cases direction with
  | left =>
    refine ⟨left.tail, left.headI :: right, ?_, ?_⟩
    · simp [Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    · simp only [List.length_cons, List.length_tail]; omega
  | right =>
    refine ⟨right.headI :: left, right.tail, ?_, ?_⟩
    · simp [Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    · simp only [List.length_cons, List.length_tail]; omega

theorem Fits.mono {Symbol : Type symbolLevel} [Inhabited Symbol] {small large : ℕ}
    {tape : Turing.Tape Symbol} (fits : Fits small tape) (bound : small ≤ large) : Fits large tape := by
  obtain ⟨left, right, representation, bounded⟩ := fits
  exact ⟨left, right, representation, bounded.trans bound⟩

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)] {State : Type stateLevel}

theorem act_fits (actions : Actions Alphabet) (tapes : Tapes Alphabet) (bound : TapeName → ℕ)
    (fits : ∀ name, Fits (bound name) (tapes name)) :
    ∀ name, Fits (bound name + 2) (act actions tapes name) := by
  intro name
  have written := (fits name).write (actions name).1
  cases direction : (actions name).2 with
  | none => simpa [act, direction] using written.mono (by omega : bound name + 1 ≤ bound name + 2)
  | some movement => simpa [act, direction, Nat.add_assoc] using written.move movement

/-- Apply this theorem to any execution prefix to bound its intermediate storage. -/
theorem Steps.fits {machine : Machine Alphabet State} {ticks : ℕ}
    {initial final : Configuration Alphabet State} (trace : Steps machine ticks initial final)
    (bound : TapeName → ℕ) (initialFits : ∀ name, Fits (bound name) (initial.2 name)) :
    ∀ name, Fits (bound name + 2 * ticks) (final.2 name) := by
  induction trace generalizing bound with
  | zero configuration => simpa using initialFits
  | @next count initial middle final transition rest hypothesis =>
    cases equation : machine initial.1 (read initial.2) with
    | none => simp [step, equation] at transition
    | some command =>
      simp only [step, equation, Option.map_some, Option.some.injEq] at transition
      subst middle
      have middleFits := act_fits command.2 initial.2 bound initialFits
      have finalFits := hypothesis (fun name => bound name + 2) middleFits
      intro name
      convert finalFits name using 1; omega

end Polytime2.MultiTape
