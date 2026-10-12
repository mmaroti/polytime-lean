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
import Polytime2.Wiring

/-! # Mathematical maps realized by finite multi-tape machines

Logical values and hypotheses are separate from their tape representations.
Representations may hide scratch existentially. The machine and polynomial
witness are fixed before all runtime size assignments and represented inputs.
-/

namespace Polytime2.MultiTape

-- parameterLevel: size names; tapeLevel: tape roles; symbolLevel: alphabets.
-- stateLevel, firstLevel, secondLevel: controllers; inputLevel, middleLevel,
-- outputLevel: the mathematical carrier families at call boundaries.
universe parameterLevel tapeLevel symbolLevel stateLevel firstLevel secondLevel
universe inputLevel middleLevel outputLevel

variable {Parameter : Type parameterLevel}
variable {TapeName : Type tapeLevel}
variable {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}
variable {Input : (Parameter → ℕ) → Type inputLevel}
variable {Output : (Parameter → ℕ) → Type outputLevel}

/-- A mathematical map with an existential polynomial machine-time certificate. -/
def Computes [Fintype Parameter] [Fintype TapeName]
    [∀ name, Fintype (Alphabet name)] [Fintype State]
    (machine : Machine Alphabet State) (entry exit : State)
    (inputRepresentation : ∀ assignment, Input assignment → Tapes Alphabet → Prop)
    (outputRepresentation : ∀ assignment, Output assignment → Tapes Alphabet → Prop)
    (hypothesis : ∀ assignment, Input assignment → Prop)
    (compute : ∀ assignment, Input assignment → Output assignment) : Prop :=
  (∀ symbols, machine exit symbols = none) ∧
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment value initial, hypothesis assignment value →
        inputRepresentation assignment value initial →
        ∃ ticks final, ticks ≤ MvPolynomial.eval assignment bound ∧
          Steps machine ticks (entry, initial) (exit, final) ∧
          outputRepresentation assignment (compute assignment value) final

namespace Computes

variable [Fintype Parameter] [Fintype TapeName] [∀ name, Fintype (Alphabet name)]

/-- Rewrite the computed mathematical map only on inputs satisfying its hypothesis. -/
theorem congr [Fintype State]
    {machine : Machine Alphabet State} {entry exit : State}
    {inputRepresentation : ∀ assignment, Input assignment → Tapes Alphabet → Prop}
    {outputRepresentation : ∀ assignment, Output assignment → Tapes Alphabet → Prop}
    {hypothesis : ∀ assignment, Input assignment → Prop}
    {compute replacement : ∀ assignment, Input assignment → Output assignment}
    (certificate : Computes machine entry exit inputRepresentation outputRepresentation hypothesis compute)
    (agreement : ∀ assignment value, hypothesis assignment value →
      compute assignment value = replacement assignment value) :
    Computes machine entry exit inputRepresentation outputRepresentation hypothesis replacement := by
  obtain ⟨halt, bound, runs⟩ := certificate
  refine ⟨halt, bound, ?_⟩
  intro assignment value initial valid represented
  simpa only [agreement assignment value valid] using runs assignment value initial valid represented

/-- Change boundary representations and strengthen the mathematical hypothesis. -/
theorem adapt [Fintype State]
    {machine : Machine Alphabet State} {entry exit : State}
    {inputRepresentation adaptedInput : ∀ assignment, Input assignment → Tapes Alphabet → Prop}
    {outputRepresentation adaptedOutput : ∀ assignment, Output assignment → Tapes Alphabet → Prop}
    {hypothesis adaptedHypothesis : ∀ assignment, Input assignment → Prop}
    {compute : ∀ assignment, Input assignment → Output assignment}
    (certificate : Computes machine entry exit inputRepresentation outputRepresentation hypothesis compute)
    (valid : ∀ assignment value, adaptedHypothesis assignment value → hypothesis assignment value)
    (representedInput : ∀ assignment value tapes, adaptedInput assignment value tapes → inputRepresentation assignment value tapes)
    (representedOutput : ∀ assignment value tapes, outputRepresentation assignment value tapes → adaptedOutput assignment value tapes) :
    Computes machine entry exit adaptedInput adaptedOutput adaptedHypothesis compute := by
  obtain ⟨halt, bound, runs⟩ := certificate
  refine ⟨halt, bound, ?_⟩
  intro assignment value initial good represented
  obtain ⟨ticks, final, cost, trace, encoded⟩ := runs assignment value initial (valid _ _ good) (representedInput _ _ _ represented)
  exact ⟨ticks, final, cost, trace, representedOutput _ _ _ encoded⟩

-- sourceLevel: the component's finite tape names.
universe sourceLevel

/-- Wiring a mathematical contract hides the component's controller and preserves
all unwired tapes through the underlying exact-cost wiring theorem. -/
theorem wire {Source : Type sourceLevel} [Fintype Source] [Fintype State]
    (wiring : Source ↪ TapeName)
    {component : Machine (fun name => Alphabet (wiring name)) State} {entry exit : State}
    {inputRepresentation : ∀ assignment, Input assignment → Tapes (fun name => Alphabet (wiring name)) → Prop}
    {outputRepresentation : ∀ assignment, Output assignment → Tapes (fun name => Alphabet (wiring name)) → Prop}
    {hypothesis : ∀ assignment, Input assignment → Prop}
    {compute : ∀ assignment, Input assignment → Output assignment}
    (certificate : Computes component entry exit inputRepresentation outputRepresentation hypothesis compute) :
    Computes (MultiTape.wire wiring component) entry exit
      (fun assignment value tapes => inputRepresentation assignment value (fun name => tapes (wiring name)))
      (fun assignment value tapes => outputRepresentation assignment value (fun name => tapes (wiring name)))
      hypothesis compute := by
  obtain ⟨halt, bound, runs⟩ := certificate
  refine ⟨by intro symbols; simp [MultiTape.wire, halt], bound, ?_⟩
  intro assignment value initial good represented
  obtain ⟨ticks, final, cost, trace, encoded⟩ := runs assignment value _ good represented
  refine ⟨ticks, install wiring final initial, cost, wire_steps wiring _ trace initial (by intro name; rfl), ?_⟩
  simpa only [install_at] using encoded

variable {Middle : (Parameter → ℕ) → Type middleLevel}
variable {First : Type firstLevel} {Second : Type secondLevel}
variable [Fintype First] [Fintype Second]

/-- Compose mathematical maps without exposing their polynomial witnesses. -/
theorem sequence
    {first : Machine Alphabet First} {second : Machine Alphabet Second}
    {firstEntry firstExit : First} {secondEntry secondExit : Second}
    {inputRepresentation : ∀ assignment, Input assignment → Tapes Alphabet → Prop}
    {middleRepresentation : ∀ assignment, Middle assignment → Tapes Alphabet → Prop}
    {outputRepresentation : ∀ assignment, Output assignment → Tapes Alphabet → Prop}
    {firstHypothesis : ∀ assignment, Input assignment → Prop}
    {secondHypothesis : ∀ assignment, Middle assignment → Prop}
    {firstMap : ∀ assignment, Input assignment → Middle assignment}
    {secondMap : ∀ assignment, Middle assignment → Output assignment}
    (firstCertificate : Computes first firstEntry firstExit
      inputRepresentation middleRepresentation firstHypothesis firstMap)
    (secondCertificate : Computes second secondEntry secondExit
      middleRepresentation outputRepresentation secondHypothesis secondMap)
    (compatible : ∀ assignment value,
      firstHypothesis assignment value → secondHypothesis assignment (firstMap assignment value)) :
    Computes (MultiTape.sequence first second secondEntry) (.inl firstEntry) (.inr secondExit)
      inputRepresentation outputRepresentation firstHypothesis
      (fun assignment value => secondMap assignment (firstMap assignment value)) := by
  obtain ⟨firstHalt, firstBound, firstRuns⟩ := firstCertificate
  obtain ⟨secondHalt, secondBound, secondRuns⟩ := secondCertificate
  refine ⟨by intro symbols; simp [MultiTape.sequence, secondHalt], firstBound + secondBound + 1, ?_⟩
  intro assignment value initial valid represented
  obtain ⟨firstTicks, middle, firstCost, firstTrace, middleEncoded⟩ :=
    firstRuns assignment value initial valid represented
  obtain ⟨secondTicks, final, secondCost, secondTrace, finalEncoded⟩ :=
    secondRuns assignment (firstMap assignment value) middle (compatible assignment value valid) middleEncoded
  refine ⟨firstTicks + secondTicks + 1, final, ?_,
    sequence_steps _ _ secondEntry firstTrace firstHalt secondTrace, finalEncoded⟩
  simp only [map_add, map_one]
  omega

end Computes
end Polytime2.MultiTape
