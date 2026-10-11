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

import Polytime.Size
import Polytime.Tape

/-! # Mathematical contracts with finite polynomial-time tape realizations

Representations relate mathematical values to tapes; scratch contents may be
existential. A caller environment is shared by input and output representations
and can record surrounding data, reserved regions, and entry/exit conventions.
No behavior is required outside the hypothesis and input representation.
-/

namespace Polytime.Realization

-- symbolLevel: tape symbols; environmentLevel: caller context.
-- inputLevel and outputLevel: mathematical input and output carriers.
universe symbolLevel environmentLevel inputLevel outputLevel intermediateLevel
-- adaptedEnvironmentLevel, adaptedInputLevel, adaptedOutputLevel: client carriers after changing representations.
universe adaptedEnvironmentLevel adaptedInputLevel adaptedOutputLevel

variable {ctx : SizeContext} {Symbol : Type symbolLevel} [Inhabited Symbol]
variable {Environment : SizeAssignment ctx → Type environmentLevel}
variable {Input : SizeAssignment ctx → Type inputLevel} {Output : SizeAssignment ctx → Type outputLevel}

/-- One finite machine and polynomial work for every size assignment, caller
context, and input satisfying its mathematical hypothesis. -/
def Realizes [Fintype Symbol]
    (inputRepresentation : ∀ assignment, Environment assignment → Input assignment → Turing.Tape Symbol → Prop)
    (outputRepresentation : ∀ assignment, Environment assignment → Output assignment → Turing.Tape Symbol → Prop)
    (hypothesis : ∀ assignment, Input assignment → Prop)
    (contract : ∀ assignment, Input assignment → Output assignment → Prop) : Prop :=
  ∃ (Controller : Type) (_finite : Fintype Controller) (inhabited : Inhabited Controller),
    let _controllerInhabited : Inhabited Controller := inhabited
    ∃ (entry exit : Controller) (machine : Turing.TM0.Machine Symbol Controller) (bound : SizePolynomial ctx),
      (∀ symbol, machine exit symbol = none) ∧
      ∀ assignment environment input initial,
        hypothesis assignment input → inputRepresentation assignment environment input initial →
        ∃ output final ticks, ticks ≤ bound.eval assignment ∧
          Tape.Steps machine ticks ⟨entry, initial⟩ ⟨exit, final⟩ ∧
          contract assignment input output ∧ outputRepresentation assignment environment output final

namespace Realizes

variable [Fintype Symbol]

noncomputable section Composition

variable {Intermediate : SizeAssignment ctx → Type intermediateLevel}
variable {inputRepresentation : ∀ assignment, Environment assignment → Input assignment → Turing.Tape Symbol → Prop}
variable {middleRepresentation : ∀ assignment, Environment assignment → Intermediate assignment → Turing.Tape Symbol → Prop}
variable {outputRepresentation : ∀ assignment, Environment assignment → Output assignment → Turing.Tape Symbol → Prop}
variable {firstHypothesis : ∀ assignment, Input assignment → Prop}
variable {secondHypothesis : ∀ assignment, Intermediate assignment → Prop}
variable {firstContract : ∀ assignment, Input assignment → Intermediate assignment → Prop}
variable {secondContract : ∀ assignment, Intermediate assignment → Output assignment → Prop}

/-- Compatible mathematical contracts compose; controller sums, handovers, and
polynomial addition stay inside this proof. -/
theorem sequence
    (first : Realizes inputRepresentation middleRepresentation firstHypothesis firstContract)
    (second : Realizes middleRepresentation outputRepresentation secondHypothesis secondContract)
    (compatible : ∀ assignment input middle,
      firstHypothesis assignment input → firstContract assignment input middle → secondHypothesis assignment middle) :
    Realizes inputRepresentation outputRepresentation firstHypothesis
      (fun assignment input output => ∃ middle,
        firstContract assignment input middle ∧ secondContract assignment middle output) := by
  obtain ⟨First, firstFinite, firstInhabited, firstEntry, firstExit, firstMachine, firstBound, firstHalt, firstRuns⟩ := first
  obtain ⟨Second, secondFinite, secondInhabited, secondEntry, secondExit, secondMachine, secondBound, secondHalt, secondRuns⟩ := second
  let firstControllerFinite : Fintype First := firstFinite
  let secondControllerFinite : Fintype Second := secondFinite
  let firstControllerInhabited : Inhabited First := firstInhabited
  let secondControllerInhabited : Inhabited Second := secondInhabited
  refine ⟨Sum First Second, inferInstance, inferInstance, .inl firstEntry, .inr secondExit,
    Tape.sequence firstMachine secondMachine secondEntry, firstBound + secondBound + 1, ?_, ?_⟩
  · intro symbol; simp [Tape.sequence, secondHalt]
  · intro assignment environment input initial valid represented
    obtain ⟨middle, middleTape, firstTicks, firstCost, firstTrace, firstCorrect, middleRepresented⟩ :=
      firstRuns assignment environment input initial valid represented
    obtain ⟨output, final, secondTicks, secondCost, secondTrace, secondCorrect, finalRepresented⟩ :=
      secondRuns assignment environment middle middleTape (compatible _ _ _ valid firstCorrect) middleRepresented
    refine ⟨output, final, firstTicks + (secondTicks + 1), ?_,
      Tape.sequence_steps secondEntry firstTrace firstHalt secondTrace, ⟨middle, firstCorrect, secondCorrect⟩, finalRepresented⟩
    simp only [SizePolynomial.eval_add, SizePolynomial.eval_one]
    omega

/-- Change only mathematical hypotheses and conclusions. -/
theorem consequence
    {hypothesis strongerHypothesis : ∀ assignment, Input assignment → Prop}
    {contract weakerContract : ∀ assignment, Input assignment → Output assignment → Prop}
    (realization : Realizes inputRepresentation outputRepresentation hypothesis contract)
    (input : ∀ assignment value, strongerHypothesis assignment value → hypothesis assignment value)
    (output : ∀ assignment initial final,
      strongerHypothesis assignment initial → contract assignment initial final → weakerContract assignment initial final) :
    Realizes inputRepresentation outputRepresentation strongerHypothesis weakerContract := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := realization
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment environment value initial valid represented
  obtain ⟨result, final, ticks, cost, trace, correct, finalRepresented⟩ :=
    runs assignment environment value initial (input _ _ valid) represented
  exact ⟨result, final, ticks, cost, trace, output _ _ _ valid correct, finalRepresented⟩

/-- Adapt a storage contract to a client's mathematical state. Metadata may
be carried in the preserved caller environment, without entering machine state. -/
theorem adapt
    {AdaptedEnvironment : SizeAssignment ctx → Type adaptedEnvironmentLevel}
    {AdaptedInput : SizeAssignment ctx → Type adaptedInputLevel}
    {AdaptedOutput : SizeAssignment ctx → Type adaptedOutputLevel}
    {hypothesis : ∀ assignment, Input assignment → Prop}
    {contract : ∀ assignment, Input assignment → Output assignment → Prop}
    (realization : Realizes inputRepresentation outputRepresentation hypothesis contract)
    (input : ∀ assignment, AdaptedInput assignment → Input assignment)
    (environment : ∀ assignment, AdaptedEnvironment assignment → AdaptedInput assignment → Environment assignment)
    (output : ∀ assignment, AdaptedInput assignment → Output assignment → AdaptedOutput assignment)
    (adaptedInputRepresentation : ∀ assignment,
      AdaptedEnvironment assignment → AdaptedInput assignment → Turing.Tape Symbol → Prop)
    (adaptedOutputRepresentation : ∀ assignment,
      AdaptedEnvironment assignment → AdaptedOutput assignment → Turing.Tape Symbol → Prop)
    (adaptedHypothesis : ∀ assignment, AdaptedInput assignment → Prop)
    (adaptedContract : ∀ assignment, AdaptedInput assignment → AdaptedOutput assignment → Prop)
    (valid : ∀ assignment value, adaptedHypothesis assignment value → hypothesis assignment (input assignment value))
    (representedInput : ∀ assignment caller value tape,
      adaptedInputRepresentation assignment caller value tape →
      inputRepresentation assignment (environment assignment caller value) (input assignment value) tape)
    (correct : ∀ assignment initial final, adaptedHypothesis assignment initial →
      contract assignment (input assignment initial) final →
      adaptedContract assignment initial (output assignment initial final))
    (representedOutput : ∀ assignment caller initial final tape, adaptedHypothesis assignment initial →
      contract assignment (input assignment initial) final →
      outputRepresentation assignment (environment assignment caller initial) final tape →
      adaptedOutputRepresentation assignment caller (output assignment initial final) tape) :
    Realizes adaptedInputRepresentation adaptedOutputRepresentation adaptedHypothesis adaptedContract := by
  obtain ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, runs⟩ := realization
  refine ⟨Controller, finite, inhabited, entry, exit, machine, bound, halt, ?_⟩
  intro assignment caller value initial good represented
  obtain ⟨result, final, ticks, cost, trace, resultCorrect, finalRepresented⟩ :=
    runs assignment (environment assignment caller value) (input assignment value) initial
      (valid assignment value good) (representedInput assignment caller value initial represented)
  exact ⟨output assignment value result, final, ticks, cost, trace,
    correct assignment value result good resultCorrect,
    representedOutput assignment caller value result final good resultCorrect finalRepresented⟩

end Composition
end Realizes
end Polytime.Realization
