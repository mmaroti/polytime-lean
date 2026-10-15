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

import Polytime2.Computation.Realizable

/-! # Sequencing algorithms behind existential certificates -/

namespace Polytime2.Computation.Realizable

open MultiTape CallingConvention

-- carrierLevel: mathematical values; all physical names and states are finite types.
universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]
variable {firstComputation : Computation.{carrierLevel} Parameter InputName}
variable {secondComputation : Computation.{carrierLevel} Parameter Unit}

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
  classical
  obtain ⟨firstScratchName, firstFiniteScratch, firstScratchDomains, firstState,
    firstFiniteStates, firstMachine, firstEntry, firstExit, firstCertificate⟩ := firstRealizable
  obtain ⟨secondScratchName, secondFiniteScratch, secondScratchDomains, secondState,
    secondFiniteStates, secondMachine, secondEntry, secondExit, secondCertificate⟩ := secondRealizable
  let firstScratchFiniteInstance : Fintype firstScratchName := firstFiniteScratch
  let secondScratchFiniteInstance : Fintype secondScratchName := secondFiniteScratch
  let firstStateFiniteInstance : Fintype firstState := firstFiniteStates
  let secondStateFiniteInstance : Fintype secondState := secondFiniteStates
  let computation := firstComputation.followedBy secondComputation domainEqual compatible
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
  let secondWiring : Internal.TapeName secondComputation secondScratchName ↪ Internal.TapeName computation ScratchName :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => .inr (.inr (.inr (.inr (.inl argument))))
      | .inr (.inr (.inl result)) => .inr (.inr (.inl result))
      | .inr (.inr (.inr scratch)) => .inr (.inr (.inr (.inr (.inr scratch))))), by
      intro firstName secondName equal
      dsimp only [ScratchName] at equal
      rcases firstName with parameter | argument | result | scratch <;>
        rcases secondName with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let wiredFirst := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation ScratchName))
    firstWiring firstMachine
  let wiredSecond := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation ScratchName))
    secondWiring secondMachine
  refine ⟨ScratchName, inferInstance, scratchDomains, firstState ⊕ secondState, inferInstance,
    MultiTape.sequence wiredFirst wiredSecond secondEntry, .inl firstEntry, .inr secondExit, ?_⟩
  obtain ⟨firstBound, firstRuns⟩ := Internal.runs firstScratchDomains firstMachine firstEntry firstExit firstCertificate
  obtain ⟨secondBound, secondRuns⟩ := Internal.runs secondScratchDomains secondMachine secondEntry secondExit secondCertificate
  have firstHalt : ∀ symbols, wiredFirst firstExit symbols = none := by
    intro symbols
    simp [wiredFirst, MultiTape.wire, firstCertificate.2.1]
  refine ⟨(by intro parameter; rfl), ?_, firstBound + secondBound + 1, ?_⟩
  · intro symbols
    simp [MultiTape.sequence, wiredSecond, MultiTape.wire, secondCertificate.2.1]
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let middle := firstComputation.compute sizes ⟨arguments, valid⟩
  let secondArguments : secondComputation.Arguments sizes := fun _ => domainEqual.symm ▸ middle
  have secondValid : secondComputation.precondition sizes secondArguments :=
    compatible sizes arguments valid
  let width := fun name => (Internal.domains computation scratchDomains name).width sizes
  have firstWidths : ∀ name, width (firstWiring name) =
      (Internal.domains firstComputation firstScratchDomains name).width sizes := by
    intro name
    rcases name with parameter | argument | result | scratch <;> rfl
  have secondWidths : ∀ name, width (secondWiring name) =
      (Internal.domains secondComputation secondScratchDomains name).width sizes := by
    intro name
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument; exact congrArg (fun domain => domain.width sizes) domainEqual.symm
    · rfl
    · rfl
  obtain ⟨firstTicks, localMiddle, firstScratch, firstCost, firstTrace, middleEq, firstScratchEq⟩ :=
    firstRuns sizes arguments valid (fun name => initial (firstWiring name)) headers
      (fun name => represented.1 (Internal.inputTape computation name) rfl)
      (by intro name; rw [← firstWidths]; exact represented.region (firstWiring name))
  have liftedFirst := firstTrace.wire firstWiring width (Internal.readOnly computation) firstWidths
    (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
      first | rfl | contradiction) initial (fun _ => 0)
  have firstStart : install firstWiring (fun name => initial (firstWiring name)) initial = initial :=
    install_self firstWiring initial
  have firstPositions : install firstWiring (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) = fun _ => 0 :=
    install_self firstWiring (fun _ => (0 : ℤ))
  rw [firstStart, firstPositions] at liftedFirst
  let prepared := install firstWiring localMiddle initial
  have preparedMiddle : prepared (secondWiring (Internal.inputTape secondComputation ())) =
      encoded (secondComputation.inputDomains ()) sizes (secondArguments ()) := by
    change install firstWiring localMiddle initial (firstWiring (Internal.outputTape firstComputation)) = _
    rw [install_at, middleEq]
    have encoding (source target : EncodedDomain.{0, carrierLevel} Parameter)
        (equal : target = source) (value : source.Carrier sizes) :
        encoded source sizes value = encoded target sizes (equal.symm ▸ value) := by
      cases equal
      rfl
    exact encoding firstComputation.outputDomain (secondComputation.inputDomains ()) domainEqual middle
  obtain ⟨secondTicks, localFinal, secondScratch, secondCost, secondTrace, resultEq, secondScratchEq⟩ :=
    secondRuns sizes secondArguments secondValid (fun name => prepared (secondWiring name))
      (fun parameter => (liftedFirst.readOnly_tape (.inl parameter) rfl).trans (headers parameter))
      (by intro name; cases name; exact preparedMiddle)
      (by
        intro name
        rw [← secondWidths]
        exact liftedFirst.region (secondWiring name) (represented.region (secondWiring name)))
  have liftedSecond := secondTrace.wire secondWiring width (Internal.readOnly computation) secondWidths
    (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
      first | rfl | contradiction) prepared (fun _ => 0)
  have secondStart : install secondWiring (fun name => prepared (secondWiring name)) prepared = prepared :=
    install_self secondWiring prepared
  have secondPositions : install secondWiring (fun _ => (0 : ℤ)) (fun _ => (0 : ℤ)) = fun _ => 0 :=
    install_self secondWiring (fun _ => (0 : ℤ))
  rw [secondStart, secondPositions] at liftedSecond
  let final := install secondWiring localFinal prepared
  have preservedFirstScratch (name : firstScratchName) :
      final (firstWiring (Internal.scratchTape firstComputation name)) =
        encoded (firstScratchDomains name) sizes (firstScratch name) := by
    change install secondWiring localFinal prepared (firstWiring (Internal.scratchTape firstComputation name)) = _
    rw [install_outside secondWiring localFinal prepared (firstWiring (Internal.scratchTape firstComputation name)) (by
      rintro ⟨localName, equal⟩
      dsimp only [secondWiring, firstWiring, Internal.scratchTape, ScratchName] at equal
      rcases localName with parameter | argument | result | scratch <;> cases equal)]
    exact (install_at firstWiring localMiddle initial _).trans (firstScratchEq name)
  have preservedMiddle : final (firstWiring (Internal.outputTape firstComputation)) =
      encoded firstComputation.outputDomain sizes middle := by
    have equal : firstWiring (Internal.outputTape firstComputation) = secondWiring (Internal.inputTape secondComputation ()) := rfl
    change install secondWiring localFinal prepared (firstWiring (Internal.outputTape firstComputation)) = _
    rw [equal, install_at, secondTrace.readOnly_tape (Internal.inputTape secondComputation ()) rfl]
    change prepared (firstWiring (Internal.outputTape firstComputation)) = _
    exact (install_at firstWiring localMiddle initial _).trans middleEq
  let output : Outputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes :=
    fun name => match name with
      | ⟨.inl _, impossible⟩ => False.elim (Bool.noConfusion impossible)
      | ⟨.inr (.inl _), impossible⟩ => False.elim (Bool.noConfusion impossible)
      | ⟨.inr (.inr (.inl _)), _⟩ => secondComputation.compute sizes ⟨secondArguments, secondValid⟩
      | ⟨.inr (.inr (.inr (.inl scratch))), _⟩ => firstScratch scratch
      | ⟨.inr (.inr (.inr (.inr (.inl _)))), _⟩ => middle
      | ⟨.inr (.inr (.inr (.inr (.inr scratch)))), _⟩ => secondScratch scratch
  refine ⟨firstTicks + secondTicks + 1, output, final, ?_,
    liftedFirst.sequence wiredSecond secondEntry firstHalt liftedSecond, ⟨valid, rfl⟩, ?_⟩
  · simp only [map_add, map_one]
    omega
  · intro name writable
    rcases name with parameter | argument | result | scratch
    · contradiction
    · contradiction
    · cases result
      exact (install_at secondWiring localFinal prepared (Internal.outputTape secondComputation)).trans resultEq
    · rcases scratch with firstName | middleName | secondName
      · exact preservedFirstScratch firstName
      · cases middleName; exact preservedMiddle
      · exact (install_at secondWiring localFinal prepared (Internal.scratchTape secondComputation secondName)).trans
          (secondScratchEq secondName)

end Polytime2.Computation.Realizable
