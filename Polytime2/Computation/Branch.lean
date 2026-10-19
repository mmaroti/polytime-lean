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
import Polytime2.Computation.Composition

/-! # Conditional computations with validity required only in the selected branch -/

namespace Polytime2.Computation

open MultiTape CallingConvention

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- The final argument is a Boolean guard. Only the selected branch's
precondition is required. Both branches return the same encoded domain. -/
noncomputable def choose (first second : Computation.{0} Parameter InputName)
    (inputEqual : ∀ name, first.inputDomains name = second.inputDomains name)
    (outputEqual : second.outputDomain = first.outputDomain) :
    Computation Parameter (InputName ⊕ Unit) where
  inputDomains := Sum.elim first.inputDomains (fun _ => EncodedDomain.booleans)
  outputDomain := first.outputDomain
  precondition sizes arguments := match (arguments (.inr ()) : Bool) with
    | true => first.precondition sizes (fun name => arguments (.inl name))
    | false => second.precondition sizes (fun name => inputEqual name ▸ arguments (.inl name))
  compute sizes arguments := match selected : (arguments.val (.inr ()) : Bool) with
    | true => first.compute sizes ⟨(fun name => arguments.val (.inl name)),
        by simpa only [selected] using arguments.property⟩
    | false => outputEqual ▸ second.compute sizes
        ⟨(fun name => inputEqual name ▸ arguments.val (.inl name)),
          by simpa only [selected] using arguments.property⟩

namespace Realizable

/-- Unused branch scratch is never initialized or interpreted. Branch costs
and the two controller handovers remain inside the existential certificate. -/
theorem choose {first second : Computation.{0} Parameter InputName}
    (firstRealizable : first.Realizable) (secondRealizable : second.Realizable)
    (inputEqual : ∀ name, first.inputDomains name = second.inputDomains name)
    (outputEqual : second.outputDomain = first.outputDomain) :
    (first.choose second inputEqual outputEqual).Realizable := by
  classical
  obtain ⟨FirstScratch, finiteFirstScratch, firstScratch, FirstState,
    finiteFirstState, firstMachine, firstEntry, firstExit, firstCertificate⟩ := firstRealizable
  obtain ⟨SecondScratch, finiteSecondScratch, secondScratch, SecondState,
    finiteSecondState, secondMachine, secondEntry, secondExit, secondCertificate⟩ := secondRealizable
  let firstScratchFiniteInstance : Fintype FirstScratch := finiteFirstScratch
  let secondScratchFiniteInstance : Fintype SecondScratch := finiteSecondScratch
  let firstStateFiniteInstance : Fintype FirstState := finiteFirstState
  let secondStateFiniteInstance : Fintype SecondState := finiteSecondState
  let computation := first.choose second inputEqual outputEqual
  let Scratch := FirstScratch ⊕ SecondScratch
  let scratchDomains : Scratch → EncodedDomain Parameter := Sum.elim firstScratch secondScratch
  let firstWiring : Internal.TapeName first FirstScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => .inr (.inl (.inl argument))
      | .inr (.inr (.inl result)) => .inr (.inr (.inl result))
      | .inr (.inr (.inr scratch)) => .inr (.inr (.inr (.inl scratch)))), by
      intro firstName secondName equal
      dsimp only [Scratch] at equal
      rcases firstName with parameter | argument | result | scratch <;>
        rcases secondName with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let secondWiring : Internal.TapeName second SecondScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => .inr (.inl (.inl argument))
      | .inr (.inr (.inl result)) => .inr (.inr (.inl result))
      | .inr (.inr (.inr scratch)) => .inr (.inr (.inr (.inr scratch)))), by
      intro firstName secondName equal
      dsimp only [Scratch] at equal
      rcases firstName with parameter | argument | result | scratch <;>
        rcases secondName with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let wiredFirst := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch))
    firstWiring firstMachine
  let wiredSecond := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch))
    secondWiring secondMachine
  let condition : Symbols (Alphabet (Internal.TapeName computation Scratch)) → Bool :=
    fun symbols => decide (symbols (Internal.inputTape computation (.inr ())) = Binary.data true)
  let machine := MultiTape.withExit (MultiTape.branchMachine condition wiredFirst wiredSecond firstEntry secondEntry)
  refine ⟨Scratch, inferInstance, scratchDomains, _, inferInstance, machine, .inl (.inl ()), .inr (), ?_⟩
  obtain ⟨firstBound, firstRuns⟩ := Internal.wiredRuns firstScratch firstMachine firstEntry firstExit firstCertificate firstWiring
  obtain ⟨secondBound, secondRuns⟩ := Internal.wiredRuns secondScratch secondMachine secondEntry secondExit secondCertificate secondWiring
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; rfl),
    firstBound + secondBound + 2, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let width := fun name => (Internal.domains computation scratchDomains name).width sizes
  have guardCorrect : condition (read initial) = arguments (.inr ()) := by
    change decide ((initial (Internal.inputTape computation (.inr ()))).head = Binary.data true) = _
    rw [represented.1 (Internal.inputTape computation (.inr ())) rfl]
    change decide ((encoded EncodedDomain.booleans sizes (arguments (.inr ()))).head = Binary.data true) = _
    rw [encoded_booleans sizes (arguments (.inr ()))]
    cases arguments (.inr ()) <;> rfl
  have encoding (source target : EncodedDomain Parameter) (equal : source = target)
      (value : source.Carrier sizes) :
      encoded source sizes value = encoded target sizes (equal ▸ value) := by
    cases equal
    rfl
  cases selected : arguments (.inr ()) with
  | true =>
    have branchValid : first.precondition sizes (fun name => arguments (.inl name)) := by
      change computation.precondition sizes arguments at valid
      dsimp only [computation, Computation.choose] at valid
      simpa only [selected] using valid
    obtain ⟨ticks, final, cost, trace, correct, outside, immutable⟩ := firstRuns sizes
      (fun name => arguments (.inl name)) branchValid width (Internal.readOnly computation) initial
      (by intro name; rcases name with parameter | argument | result | scratch <;> rfl)
      (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
        first | rfl | contradiction) headers
      (fun name => represented.1 (Internal.inputTape computation (.inl name)) rfl)
      (fun name => represented.region (firstWiring name))
    have result : computation.compute sizes ⟨arguments, valid⟩ =
        first.compute sizes ⟨(fun name => arguments (.inl name)), branchValid⟩ := by
      dsimp only [computation, Computation.choose]
      split
      · rfl
      · rename_i branchEq
        exact False.elim (Bool.noConfusion (selected.symm.trans branchEq))
    refine ⟨ticks + 2, (fun _ => computation.compute sizes ⟨arguments, valid⟩), final, ?_,
      trace.branch_true condition wiredSecond secondEntry (guardCorrect.trans selected)
        (by intro symbols; simp [wiredFirst, MultiTape.wire, firstCertificate.2.2.1]),
      ⟨valid, rfl⟩, ?_⟩
    · simp only [map_add, map_ofNat]; omega
    · intro name; cases name
      exact correct.trans (congrArg (encoded first.outputDomain sizes) result.symm)
  | false =>
    have branchValid : second.precondition sizes
        (fun name => inputEqual name ▸ arguments (.inl name)) := by
      change computation.precondition sizes arguments at valid
      dsimp only [computation, Computation.choose] at valid
      simpa only [selected] using valid
    obtain ⟨ticks, final, cost, trace, correct, outside, immutable⟩ := secondRuns sizes
      (fun name => inputEqual name ▸ arguments (.inl name)) branchValid width (Internal.readOnly computation) initial
      (by
        intro name
        rcases name with parameter | argument | result | scratch
        · rfl
        · exact congrArg (fun domain => domain.width sizes) (inputEqual argument)
        · cases result; exact congrArg (fun domain => domain.width sizes) outputEqual.symm
        · rfl)
      (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
        first | rfl | contradiction) headers
      (fun name => (represented.1 (Internal.inputTape computation (.inl name)) rfl).trans
        (encoding _ _ (inputEqual name) (arguments (.inl name))))
      (fun name => represented.region (secondWiring name))
    have result : computation.compute sizes ⟨arguments, valid⟩ = outputEqual ▸
        second.compute sizes ⟨(fun name => inputEqual name ▸ arguments (.inl name)), branchValid⟩ := by
      dsimp only [computation, Computation.choose]
      split
      · rename_i branchEq
        exact False.elim (Bool.noConfusion (selected.symm.trans branchEq))
      · rfl
    refine ⟨ticks + 2, (fun _ => computation.compute sizes ⟨arguments, valid⟩), final, ?_,
      trace.branch_false condition wiredFirst firstEntry (guardCorrect.trans selected)
        (by intro symbols; simp [wiredSecond, MultiTape.wire, secondCertificate.2.2.1]),
      ⟨valid, rfl⟩, ?_⟩
    · simp only [map_add, map_ofNat]; omega
    · intro name; cases name
      exact correct.trans ((encoding _ _ outputEqual _).trans
        (congrArg (encoded first.outputDomain sizes) result.symm))

/-- Split a realizability proof by a certified Boolean test of the inputs. Only
the selected branch must satisfy its strengthened mathematical precondition. -/
theorem byCases (computation : Computation.{0} Parameter InputName)
    (condition : ∀ sizes, computation.Arguments sizes → Bool)
    (guardRealizable : (Computation.mk computation.inputDomains EncodedDomain.booleans
      computation.precondition (fun sizes arguments => condition sizes arguments.val)).Realizable)
    (whenTrue : (computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
      (fun _ _ valid => valid.1)).Realizable)
    (whenFalse : (computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = false)
      (fun _ _ valid => valid.1)).Realizable) : computation.Realizable := by
  have branches := whenTrue.choose whenFalse (fun _ => rfl) rfl
  have combined := guardRealizable.letThen branches (fun _ => rfl) rfl (by
    intro sizes arguments valid
    cases value : condition sizes arguments <;> simpa [Computation.choose, Computation.withPrecondition, value] using valid)
  exact combined.withSpecification computation.precondition computation.compute
    (by intros; assumption)
    (by
      intro sizes arguments valid
      simp only [Computation.letThen, Computation.choose, Computation.withPrecondition]
      split <;> rfl)

end Realizable
end Polytime2.Computation
