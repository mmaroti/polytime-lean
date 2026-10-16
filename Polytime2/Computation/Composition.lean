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

import Polytime2.Computation.Arguments

/-! # Sequencing algorithms behind existential certificates -/

namespace Polytime2.Computation.Realizable

open MultiTape CallingConvention

-- carrierLevel: mathematical values; all physical names and states are finite types.
universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]
variable {firstComputation : Computation.{carrierLevel} Parameter InputName}
variable {secondComputation : Computation.{carrierLevel} Parameter Unit}

/-- Bind an intermediate result while retaining the original arguments.
This is the library's tape-wiring proof; application proofs use only this rule. -/
theorem letThen {continuation : Computation.{carrierLevel} Parameter (InputName ⊕ Unit)}
    (firstRealizable : firstComputation.Realizable)
    (continuationRealizable : continuation.Realizable)
    (inputEqual : ∀ name, continuation.inputDomains (.inl name) = firstComputation.inputDomains name)
    (resultEqual : continuation.inputDomains (.inr ()) = firstComputation.outputDomain)
    (compatible : ∀ sizes (arguments : firstComputation.Arguments sizes)
      (valid : firstComputation.precondition sizes arguments),
      continuation.precondition sizes (fun name => match name with
        | .inl original => (inputEqual original).symm ▸ arguments original
        | .inr _ => resultEqual.symm ▸ firstComputation.compute sizes ⟨arguments, valid⟩)) :
    (firstComputation.letThen continuation inputEqual resultEqual compatible).Realizable := by
  classical
  obtain ⟨firstScratchName, firstFiniteScratch, firstScratchDomains, firstState,
    firstFiniteStates, firstMachine, firstEntry, firstExit, firstCertificate⟩ := firstRealizable
  obtain ⟨secondScratchName, secondFiniteScratch, secondScratchDomains, secondState,
    secondFiniteStates, secondMachine, secondEntry, secondExit, secondCertificate⟩ := continuationRealizable
  let firstScratchFiniteInstance : Fintype firstScratchName := firstFiniteScratch
  let secondScratchFiniteInstance : Fintype secondScratchName := secondFiniteScratch
  let firstStateFiniteInstance : Fintype firstState := firstFiniteStates
  let secondStateFiniteInstance : Fintype secondState := secondFiniteStates
  let computation := firstComputation.letThen continuation inputEqual resultEqual compatible
  let ScratchName := firstScratchName ⊕ (Unit ⊕ secondScratchName)
  let scratchDomains : ScratchName → EncodedDomain Parameter
    | .inl name => firstScratchDomains name
    | .inr (.inl _) => firstComputation.outputDomain
    | .inr (.inr name) => secondScratchDomains name
  let firstWiring : Internal.TapeName firstComputation firstScratchName ↪ Internal.TapeName computation ScratchName :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => .inr (.inl argument)
      | .inr (.inr (.inl result)) => .inr (.inr (.inr (.inr (.inl result))))
      | .inr (.inr (.inr scratch)) => .inr (.inr (.inr (.inl scratch)))), by
      intro firstName secondName equal
      dsimp only [ScratchName] at equal
      rcases firstName with parameter | argument | result | scratch <;>
        rcases secondName with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let secondWiring : Internal.TapeName continuation secondScratchName ↪ Internal.TapeName computation ScratchName :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl (.inl argument)) => .inr (.inl argument)
      | .inr (.inl (.inr result)) => .inr (.inr (.inr (.inr (.inl result))))
      | .inr (.inr (.inl result)) => .inr (.inr (.inl result))
      | .inr (.inr (.inr scratch)) => .inr (.inr (.inr (.inr (.inr scratch))))), by
      intro firstName secondName equal
      dsimp only [ScratchName] at equal
      rcases firstName with parameter | (argument | middle) | result | scratch <;>
        rcases secondName with parameter' | (argument' | middle') | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let wiredFirst := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation ScratchName))
    firstWiring firstMachine
  let wiredSecond := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation ScratchName))
    secondWiring secondMachine
  refine ⟨ScratchName, inferInstance, scratchDomains, firstState ⊕ secondState, inferInstance,
    MultiTape.sequence wiredFirst wiredSecond secondEntry, .inl firstEntry, .inr secondExit, ?_⟩
  obtain ⟨firstBound, firstRuns⟩ := Internal.wiredRuns firstScratchDomains firstMachine firstEntry firstExit firstCertificate firstWiring
  obtain ⟨secondBound, secondRuns⟩ := Internal.wiredRuns secondScratchDomains secondMachine secondEntry secondExit secondCertificate secondWiring
  have firstHalt : ∀ symbols, wiredFirst firstExit symbols = none := by
    intro symbols
    simp [wiredFirst, MultiTape.wire, firstCertificate.2.2.1]
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_, firstBound + secondBound + 1, ?_⟩
  · intro symbols
    simp [MultiTape.sequence, wiredSecond, MultiTape.wire, secondCertificate.2.2.1]
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let middle := firstComputation.compute sizes ⟨arguments, valid⟩
  let secondArguments : continuation.Arguments sizes := fun name => match name with
    | .inl original => (inputEqual original).symm ▸ arguments original
    | .inr _ => resultEqual.symm ▸ middle
  have secondValid : continuation.precondition sizes secondArguments := compatible sizes arguments valid
  let width := fun name => (Internal.domains computation scratchDomains name).width sizes
  have firstWidths : ∀ name, width (firstWiring name) =
      (Internal.domains firstComputation firstScratchDomains name).width sizes := by
    intro name
    rcases name with parameter | argument | result | scratch <;> rfl
  have secondWidths : ∀ name, width (secondWiring name) =
      (Internal.domains continuation secondScratchDomains name).width sizes := by
    intro name
    rcases name with parameter | (argument | middleName) | result | scratch
    · rfl
    · exact congrArg (fun domain => domain.width sizes) (inputEqual argument).symm
    · cases middleName; exact congrArg (fun domain => domain.width sizes) resultEqual.symm
    · rfl
    · rfl
  obtain ⟨firstTicks, prepared, firstCost, firstTrace, middleEq, firstOutside, firstImmutable⟩ :=
    firstRuns sizes arguments valid width (Internal.readOnly computation) initial firstWidths
      (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
        first | rfl | contradiction) headers
      (fun name => represented.1 (Internal.inputTape computation name) rfl)
      (fun name => represented.region (firstWiring name))
  have encoding (source target : EncodedDomain.{0, carrierLevel} Parameter)
      (equal : target = source) (value : source.Carrier sizes) :
      encoded source sizes value = encoded target sizes (equal.symm ▸ value) := by
    cases equal
    rfl
  obtain ⟨secondTicks, final, secondCost, secondTrace, resultEq, secondOutside, secondImmutable⟩ :=
    secondRuns sizes secondArguments secondValid width (Internal.readOnly computation) prepared secondWidths
      (by intro name readonly; rcases name with parameter | (argument | middleName) | result | scratch <;>
        first | rfl | contradiction)
      (fun parameter => (firstTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter))
      (by
        intro name
        cases name with
        | inl original =>
          exact (firstTrace.readOnly_tape (Internal.inputTape computation original) rfl).trans
            ((represented.1 (Internal.inputTape computation original) rfl).trans
              (encoding _ _ (inputEqual original) (arguments original)))
        | inr result => cases result; exact middleEq.trans (encoding _ _ resultEqual middle))
      (fun name => firstTrace.region (secondWiring name) (represented.region (secondWiring name)))
  let output : Outputs (Internal.domains computation scratchDomains)
      (Internal.outputTapes computation ScratchName) sizes :=
    fun _ => continuation.compute sizes ⟨secondArguments, secondValid⟩
  refine ⟨firstTicks + secondTicks + 1, output, final, ?_,
    firstTrace.sequence wiredSecond secondEntry firstHalt secondTrace, ⟨valid, rfl⟩, ?_⟩
  · simp only [map_add, map_one]
    omega
  · intro name
    cases name
    exact resultEq

/-- The first result is a private intermediate tape, read-only during the
second call. Component scratch collections remain disjoint. -/
theorem followedBy (firstRealizable : firstComputation.Realizable)
    (secondRealizable : secondComputation.Realizable)
    (domainEqual : secondComputation.inputDomains () = firstComputation.outputDomain)
    (compatible : ∀ sizes (arguments : firstComputation.Arguments sizes)
      (valid : firstComputation.precondition sizes arguments),
      secondComputation.precondition sizes (fun _ =>
        domainEqual.symm ▸ firstComputation.compute sizes ⟨arguments, valid⟩)) :
    (firstComputation.followedBy secondComputation domainEqual compatible).Realizable := by
  let contextDomains : InputName ⊕ Unit → EncodedDomain.{0, carrierLevel} Parameter :=
    Sum.elim firstComputation.inputDomains (fun _ => firstComputation.outputDomain)
  let selection : Unit ↪ InputName ⊕ Unit := ⟨Sum.inr, Sum.inr_injective⟩
  have selectedEqual : ∀ name, contextDomains (selection name) = secondComputation.inputDomains name := by
    intro name
    cases name
    exact domainEqual.symm
  exact firstRealizable.letThen
    (secondRealizable.withArguments contextDomains selection selectedEqual)
    (fun _ => rfl) rfl compatible

end Polytime2.Computation.Realizable
