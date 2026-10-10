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

import Polytime2.Machine
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! # Polynomial certificates for finite multi-tape machines

The same machine and natural-coefficient polynomial work for all size
assignments and all tapes satisfying the mathematical precondition. No
behavior is required outside that precondition. Contracts describe complete
tapes, including head positions, scratch, and preservation obligations.
-/

namespace Polytime2.MultiTape

-- parameterLevel: size names; tapeLevel: tape names; symbolLevel: alphabets.
-- stateLevel, firstLevel, secondLevel: finite controller carriers.
universe parameterLevel tapeLevel symbolLevel stateLevel firstLevel secondLevel

variable {Parameter : Type parameterLevel}
variable {TapeName : Type tapeLevel}
variable {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}

/-- Finite-machine realization with an existential polynomial transition bound.
The postcondition may relate both the incoming and outgoing tapes. -/
def Realizes [Fintype Parameter] [Fintype TapeName]
    [∀ name, Fintype (Alphabet name)] [Fintype State]
    (machine : Machine Alphabet State) (entry exit : State)
    (precondition : (Parameter → ℕ) → Tapes Alphabet → Prop)
    (postcondition : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop) : Prop :=
  (∀ symbols, machine exit symbols = none) ∧
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∃ ticks final, ticks ≤ MvPolynomial.eval assignment bound ∧
          Steps machine ticks (entry, initial) (exit, final) ∧
          postcondition assignment initial final

namespace Realizes

variable [Fintype Parameter] [Fintype TapeName]
variable [∀ name, Fintype (Alphabet name)] [Fintype State]
variable {First : Type firstLevel} {Second : Type secondLevel}
variable [Fintype First] [Fintype Second]

/-- Sequential contracts compose without exposing their polynomial witnesses. -/
theorem sequence {first : Machine Alphabet First} {second : Machine Alphabet Second}
    {firstEntry firstExit : First} {secondEntry secondExit : Second}
    {firstPre secondPre : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {firstPost secondPost : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (firstRealizes : Realizes first firstEntry firstExit firstPre firstPost)
    (secondRealizes : Realizes second secondEntry secondExit secondPre secondPost)
    (compatible : ∀ assignment initial middle,
      firstPre assignment initial → firstPost assignment initial middle → secondPre assignment middle) :
    Realizes (MultiTape.sequence first second secondEntry) (.inl firstEntry) (.inr secondExit)
      firstPre (fun assignment initial final => ∃ middle,
        firstPost assignment initial middle ∧ secondPost assignment middle final) := by
  obtain ⟨firstHalt, firstBound, firstRuns⟩ := firstRealizes
  obtain ⟨secondHalt, secondBound, secondRuns⟩ := secondRealizes
  refine ⟨?_, firstBound + secondBound + 1, ?_⟩
  · intro symbols; simp [MultiTape.sequence, secondHalt]
  · intro assignment initial valid
    obtain ⟨firstTicks, middle, firstCost, firstTrace, firstCorrect⟩ := firstRuns assignment initial valid
    obtain ⟨secondTicks, final, secondCost, secondTrace, secondCorrect⟩ :=
      secondRuns assignment middle (compatible assignment initial middle valid firstCorrect)
    refine ⟨firstTicks + secondTicks + 1, final, ?_,
      sequence_steps first second secondEntry firstTrace firstHalt secondTrace,
      middle, firstCorrect, secondCorrect⟩
    simp only [map_add, map_one]
    omega

/-- Strengthen the hypothesis and weaken the conclusion without changing execution. -/
theorem consequence {machine : Machine Alphabet State} {entry exit : State}
    {precondition otherPre : (Parameter → ℕ) → Tapes Alphabet → Prop}
    {postcondition otherPost : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop}
    (realization : Realizes machine entry exit precondition postcondition)
    (input : ∀ assignment tapes, otherPre assignment tapes → precondition assignment tapes)
    (output : ∀ assignment initial final,
      otherPre assignment initial → postcondition assignment initial final → otherPost assignment initial final) :
    Realizes machine entry exit otherPre otherPost := by
  obtain ⟨halt, bound, runs⟩ := realization
  refine ⟨halt, bound, ?_⟩
  intro assignment initial valid
  obtain ⟨ticks, final, cost, trace, correct⟩ := runs assignment initial (input assignment initial valid)
  exact ⟨ticks, final, cost, trace, output assignment initial final valid correct⟩

end Realizes
end Polytime2.MultiTape
