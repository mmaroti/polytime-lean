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
import Polytime2.TM0.CallingConventionDelimited

/-! # Public TM0 export of every realized mathematical computation

The external format lists unary sizes first, then encoded arguments, with a
separator after every block. A finite alphabet embeds the five external letters.
All controllers, scratch tapes, simulator tracks, and polynomial witnesses are
hidden by the export theorem; input preparation and extraction are included.
-/

namespace Polytime2.Computation

open MultiTape CallingConvention

-- carrierLevel: mathematical input and output values.
universe carrierLevel symbolLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Input ordering is fixed by the specialization, independently of all sizes. -/
noncomputable def inputRoles : List (Parameter ⊕ InputName) := by
  classical
  exact (Finset.univ : Finset Parameter).toList.map Sum.inl ++
    (Finset.univ : Finset InputName).toList.map Sum.inr

private theorem inputRoles_unique : (inputRoles (Parameter := Parameter) (InputName := InputName)).Nodup := by
  classical
  apply List.nodup_append.mpr
  refine ⟨(Finset.nodup_toList _).map Sum.inl_injective,
    (Finset.nodup_toList _).map Sum.inr_injective, ?_⟩
  intro first firstMember second secondMember equal
  obtain ⟨first, _, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨second, _, rfl⟩ := List.mem_map.mp secondMember
  cases equal

/-- Size values are unary blocks; each ordinary argument uses its domain codec. -/
noncomputable def inputBlocks (computation : Computation.{carrierLevel} Parameter InputName)
    (sizes : Parameter → ℕ) (arguments : computation.Arguments sizes) : List (List Bool) :=
  inputRoles.map (fun name => match name with
    | .inl parameter => List.replicate (sizes parameter) true
    | .inr argument => EncodedDomain.ArrayEncoding.bits
        ((computation.inputDomains argument).encode sizes (arguments argument)))

/-- Serialize only public mathematical inputs, with no scratch or track data. -/
noncomputable def serialize {Symbol : Type symbolLevel}
    (computation : Computation.{carrierLevel} Parameter InputName)
    (letters : DelimitedInput.Letter → Symbol) (sizes : Parameter → ℕ)
    (arguments : computation.Arguments sizes) : List Symbol :=
  DelimitedInput.serialize letters (computation.inputBlocks sizes arguments)

/-- Standard single-tape realization from delimited public inputs, with exact
canonical output and one uniform polynomial transition bound. -/
def TM0Realizable (computation : Computation.{carrierLevel} Parameter InputName) : Prop :=
    ∃ (Symbol : Type) (_finiteSymbols : Fintype Symbol) (inhabitedSymbols : Inhabited Symbol),
      let _symbolInhabited : Inhabited Symbol := inhabitedSymbols
      ∃ (letters : DelimitedInput.Letter ↪ Symbol)
        (Controller : Type) (_finiteControllers : Fintype Controller) (inhabitedControllers : Inhabited Controller),
        let _controllerInhabited : Inhabited Controller := inhabitedControllers
        ∃ (machine : Turing.TM0.Machine Symbol Controller) (bound : MvPolynomial Parameter ℕ),
          (∀ value, letters value ≠ default) ∧
          ∀ (sizes : Parameter → ℕ) (arguments : computation.Arguments sizes)
            (valid : computation.precondition sizes arguments),
            ∃ ticks finalState, ticks ≤ MvPolynomial.eval sizes bound ∧
              let output := (EncodedDomain.ArrayEncoding.bits
                (computation.outputDomain.encode sizes (computation.compute sizes ⟨arguments, valid⟩))).map
                  (letters ∘ Sum.inl)
              (fun current => current.bind (Turing.TM0.step machine))^[ticks]
                (some (Turing.TM0.init (computation.serialize letters sizes arguments))) =
                some ⟨finalState, Turing.Tape.mk₁ output⟩ ∧
              Turing.TM0.step machine ⟨finalState, Turing.Tape.mk₁ output⟩ = none

namespace Realizable.Internal

private def roleTape (computation : Computation.{carrierLevel} Parameter InputName)
    (ScratchName : Type) : Parameter ⊕ InputName → TapeName computation ScratchName :=
  Sum.elim Sum.inl (inputTape computation)

private theorem roleTape_injective (computation : Computation.{carrierLevel} Parameter InputName)
    (ScratchName : Type) : Function.Injective (roleTape computation ScratchName) := by
  intro first second equal
  cases first <;> cases second <;> simp_all [roleTape]

end Realizable.Internal

namespace Realizable

/-- Any realized computation has a finite TM0 implementation from delimited
input to canonical binary output. One machine and one polynomial work for every
public size assignment and admissible input. Output begins at the final head;
all other tape cells are blank. No internal implementation witnesses are needed.
-/
theorem tm0 {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable) :
    computation.TM0Realizable := by
  classical
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    source, sourceEntry, sourceExit, certificate⟩ := realizable
  let scratchFiniteInstance : Fintype ScratchName := finiteScratch
  let stateFiniteInstance : Fintype State := finiteStates
  let SourceTape := Internal.TapeName computation ScratchName
  let inputNames : List SourceTape := inputRoles.map (Internal.roleTape computation ScratchName)
  have unique : inputNames.Nodup := inputRoles_unique.map (Internal.roleTape_injective computation ScratchName)
  have complete : ∀ name, name ∈ inputNames ↔ Internal.readOnly computation name = true := by
    intro name
    constructor
    · intro member
      obtain ⟨role, _, equal⟩ := List.mem_map.mp member
      subst name
      cases role <;> rfl
    · intro immutable
      rcases name with parameter | argument | result | scratch
      · exact List.mem_map.mpr ⟨.inl parameter, by simp [inputRoles], rfl⟩
      · exact List.mem_map.mpr ⟨.inr argument, by simp [inputRoles], rfl⟩
      · contradiction
      · contradiction
  let names := (Finset.univ : Finset SourceTape).toList
  let resultTape : SourceTape := Internal.outputTape computation
  let simulate := MultiTape.sequence (Simulation.machine names source) (CallingConvention.extract resultTape) 0
  let combined := MultiTape.sequence (DelimitedInput.machine resultTape inputNames) simulate
    (.inl (Simulation.entry names sourceEntry))
  let program := TM0Input.machine (SingleTape.compile combined) (.inl (.inl (DelimitedInput.entry inputNames)))
  obtain ⟨bound, execute⟩ := certificate.tm0_delimited inputNames unique complete ()
  refine ⟨Sweep.Alphabet (DelimitedInput.Row SourceTape), inferInstance, inferInstance,
    DelimitedInput.letters resultTape, _, inferInstance, inferInstance, program, bound,
    DelimitedInput.letters_nonblank resultTape, ?_⟩
  intro sizes arguments valid
  let input : Inputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes :=
    fun name => match name with
      | ⟨.inl _, _⟩ => PUnit.unit
      | ⟨.inr (.inl argument), _⟩ => arguments argument
      | ⟨.inr (.inr _), impossible⟩ => False.elim (Bool.noConfusion impossible)
  obtain ⟨ticks, output, cost, correct, trace, stopped⟩ := execute sizes input valid
    (by intro parameter; exact encoded_unary parameter sizes)
  obtain ⟨_outputValid, equality⟩ := correct
  have blocks : inputNames.map (CallingConvention.inputBits (Internal.domains computation scratchDomains)
      (Internal.readOnly computation) sizes input) = computation.inputBlocks sizes arguments := by
    simp only [inputNames, inputBlocks, List.map_map]
    apply List.map_congr_left
    intro role member
    cases role with
    | inl parameter =>
      simp [Internal.roleTape, CallingConvention.inputBits, Internal.domains, Internal.readOnly,
        EncodedDomain.unary, EncodedDomain.ArrayEncoding.bits, input]
    | inr argument => rfl
  have result : output () = computation.compute sizes ⟨arguments, valid⟩ := equality
  rw [result] at trace stopped
  rw [blocks] at trace
  refine ⟨ticks, some (.inl (.inr (.inr 7))), cost, ?_, ?_⟩
  · exact trace
  · exact stopped

end Realizable
end Polytime2.Computation
