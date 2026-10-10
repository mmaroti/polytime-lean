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

/-! # Branching on finitely many scanned symbols

An arbitrary predicate on the scanned symbols is a fixed finite table when
the alphabets and tape set are finite. More expensive guards must first be
computed by a certified machine. Selection and the common exit each cost one
stationary transition; only the selected controller executes.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape names; symbolLevel: alphabets; firstLevel, secondLevel: controllers.
universe tapeLevel symbolLevel firstLevel secondLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {First : Type firstLevel} {Second : Type secondLevel}

def branchMachine (condition : Symbols Alphabet → Bool)
    (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (firstEntry : First) (secondEntry : Second) : Machine Alphabet (Sum Unit (Sum First Second))
  | .inl (), symbols => if condition symbols then
      some (.inr (.inl firstEntry), stationary symbols)
    else some (.inr (.inr secondEntry), stationary symbols)
  | .inr (.inl state), symbols =>
    (first state symbols).map fun command => (.inr (.inl command.1), command.2)
  | .inr (.inr state), symbols =>
    (second state symbols).map fun command => (.inr (.inr command.1), command.2)

theorem branch_steps_true (condition : Symbols Alphabet → Bool)
    (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (firstEntry : First) (secondEntry : Second) {firstExit : First}
    {ticks : ℕ} {initial final : Tapes Alphabet}
    (selected : condition (read initial) = true)
    (trace : Steps first ticks (firstEntry, initial) (firstExit, final))
    (halt : ∀ symbols, first firstExit symbols = none) :
    Steps (withExit (branchMachine condition first second firstEntry secondEntry)) (ticks + 2)
      (.inl (.inl ()), initial) (.inr (), final) := by
  have lifted := trace.rename (fun state => Sum.inr (Sum.inl state))
    (target := branchMachine condition first second firstEntry secondEntry)
    (by intro state symbols next actions transition; simp [branchMachine, transition])
  have choose : step (branchMachine condition first second firstEntry secondEntry)
      (.inl (), initial) = some (.inr (.inl firstEntry), initial) := by
    simp [step, branchMachine, selected]
  have stopped : step (branchMachine condition first second firstEntry secondEntry)
      (.inr (.inl firstExit), final) = none := by
    simp [step, branchMachine, halt]
  simpa [Nat.add_assoc] using withExit_steps _ (.next choose lifted) stopped

theorem branch_steps_false (condition : Symbols Alphabet → Bool)
    (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (firstEntry : First) (secondEntry : Second) {secondExit : Second}
    {ticks : ℕ} {initial final : Tapes Alphabet}
    (selected : condition (read initial) = false)
    (trace : Steps second ticks (secondEntry, initial) (secondExit, final))
    (halt : ∀ symbols, second secondExit symbols = none) :
    Steps (withExit (branchMachine condition first second firstEntry secondEntry)) (ticks + 2)
      (.inl (.inl ()), initial) (.inr (), final) := by
  have lifted := trace.rename (fun state => Sum.inr (Sum.inr state))
    (target := branchMachine condition first second firstEntry secondEntry)
    (by intro state symbols next actions transition; simp [branchMachine, transition])
  have choose : step (branchMachine condition first second firstEntry secondEntry)
      (.inl (), initial) = some (.inr (.inr secondEntry), initial) := by
    simp [step, branchMachine, selected]
  have stopped : step (branchMachine condition first second firstEntry secondEntry)
      (.inr (.inr secondExit), final) = none := by
    simp [step, branchMachine, halt]
  simpa [Nat.add_assoc] using withExit_steps _ (.next choose lifted) stopped

namespace Realizes

-- parameterLevel: runtime size names.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
variable [∀ name, Fintype (Alphabet name)] [Fintype First] [Fintype Second]

theorem branch (condition : Symbols Alphabet → Bool)
    {first : Machine Alphabet First} {second : Machine Alphabet Second}
    {firstEntry firstExit : First} {secondEntry secondExit : Second}
    {firstPre secondPre : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {firstPost secondPost : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (firstRealizes : Realizes first firstEntry firstExit firstPre firstPost)
    (secondRealizes : Realizes second secondEntry secondExit secondPre secondPost) :
    Realizes (withExit (branchMachine condition first second firstEntry secondEntry))
      (.inl (.inl ())) (.inr ())
      (fun assignment tapes => if condition (read tapes) then firstPre assignment tapes else secondPre assignment tapes)
      (fun assignment initial final => if condition (read initial) then
        firstPost assignment initial final else secondPost assignment initial final) := by
  obtain ⟨firstHalt, firstBound, firstRuns⟩ := firstRealizes
  obtain ⟨secondHalt, secondBound, secondRuns⟩ := secondRealizes
  refine ⟨by intro symbols; rfl, firstBound + secondBound + 2, ?_⟩
  intro assignment initial valid
  cases selected : condition (read initial) with
  | false =>
    obtain ⟨ticks, final, cost, trace, correct⟩ := secondRuns assignment initial (by simpa [selected] using valid)
    refine ⟨ticks + 2, final, ?_,
      branch_steps_false condition first second firstEntry secondEntry selected trace secondHalt, ?_⟩
    · simp only [map_add, map_ofNat]; omega
    · simpa [selected] using correct
  | true =>
    obtain ⟨ticks, final, cost, trace, correct⟩ := firstRuns assignment initial (by simpa [selected] using valid)
    refine ⟨ticks + 2, final, ?_,
      branch_steps_true condition first second firstEntry secondEntry selected trace firstHalt, ?_⟩
    · simp only [map_add, map_ofNat]; omega
    · simpa [selected] using correct

end Realizes
end Polytime2.MultiTape
