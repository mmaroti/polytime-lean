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

/-! # Internal transport from existing finite tape layouts

This adapter belongs to foundational realization proofs. Application proofs
must reuse `Computation.Realizable` through its mathematical construction rules.
-/

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

-- carrierLevel: mathematical values; source tapes and controllers are finite types.
universe carrierLevel
variable {Parameter InputName SourceTape State ScratchName : Type}
variable [Fintype Parameter] [Fintype InputName]
variable [Fintype State] [Fintype ScratchName]

/-- Pull mathematical inputs back along a static, domain-compatible layout. -/
def pullInputs (computation : Computation.{carrierLevel} Parameter InputName)
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool)
    (layout : SourceTape ↪ TapeName computation ScratchName)
    (values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      (sourceDomains name).Carrier sizes)
    (readonly : ∀ name, sourceReadOnly name = readOnly computation (layout name))
    (sizes : Parameter → ℕ)
    (input : Inputs (domains computation scratchDomains) (readOnly computation) sizes) :
    Inputs sourceDomains sourceReadOnly sizes :=
  fun name => values name.val sizes
    (input ⟨layout name.val, (readonly name.val).symm.trans name.property⟩)

/-- An injective layout and carrier equivalences package a primitive without
exporting its machine or scratch names. Unused caller scratch stays arbitrary. -/
theorem ofLayout [Fintype SourceTape] {SourceOutputName : Type} (computation : Computation.{carrierLevel} Parameter InputName)
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (sourceSizes : Parameter ↪ SourceTape)
    (sourceOutputTapes : SourceOutputName ↪ SourceTape)
    (machine : Machine (Alphabet SourceTape) State) (entry exit : State)
    (sourceHypothesis : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes → Prop)
    (sourceContract : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes →
      Outputs sourceDomains sourceOutputTapes sizes → Prop)
    (certificate : CallingConvention.Realizes sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
      machine entry exit sourceHypothesis sourceContract)
    (layout : SourceTape ↪ TapeName computation ScratchName)
    (values : ∀ name sizes, (domains computation scratchDomains (layout name)).Carrier sizes ≃
      (sourceDomains name).Carrier sizes)
    (widths : ∀ name sizes, (domains computation scratchDomains (layout name)).width sizes =
      (sourceDomains name).width sizes)
    (encodings : ∀ name sizes value,
      encoded (domains computation scratchDomains (layout name)) sizes value =
        encoded (sourceDomains name) sizes (values name sizes value))
    (readonly : ∀ name, sourceReadOnly name = readOnly computation (layout name))
    (sizeLayout : ∀ parameter, layout (sourceSizes parameter) = .inl parameter)
    (resultName : SourceOutputName)
    (resultLayout : layout (sourceOutputTapes resultName) = outputTape computation)
    (valid : ∀ sizes input,
      computation.precondition sizes (arguments computation scratchDomains sizes input) →
      sourceHypothesis sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input))
    (correct : ∀ sizes input (good : computation.precondition sizes
        (arguments computation scratchDomains sizes input)) output,
      sourceContract sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input) output →
      encoded (sourceDomains (sourceOutputTapes resultName)) sizes (output resultName) =
        encoded computation.outputDomain sizes
          (computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩)) :
    computation.Realizable := by
  classical
  refine ⟨ScratchName, inferInstance, scratchDomains, State, inferInstance,
    MultiTape.wire (Alphabet := Alphabet (TapeName computation ScratchName)) layout
      machine, entry, exit, ?_⟩
  obtain ⟨bound, execute⟩ := certificate.wired_runs layout
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [MultiTape.wire, certificate.2.2.1]), bound, ?_⟩
  intro sizes input initial good represented headers
  let localInput := pullInputs computation scratchDomains sourceDomains sourceReadOnly
    layout values readonly sizes input
  obtain ⟨ticks, sourceOutput, final, cost, trace, result, canonical, outside, immutable⟩ :=
    execute sizes localInput (fun name => (domains computation scratchDomains name).width sizes)
      (readOnly computation) initial (fun name => widths name sizes)
      (fun name premise => (readonly name).trans premise) (valid sizes input good)
      (by
        intro name immutable
        exact (represented.1 (layout name) ((readonly name).symm.trans immutable)).trans
          (encodings name sizes (input ⟨layout name, (readonly name).symm.trans immutable⟩)))
      (by intro name writable; exact represented.region (layout name))
      (by
        intro parameter
        change initial (layout (sourceSizes parameter)) = unary (sizes parameter)
        rw [sizeLayout]
        exact headers parameter)
  have resultEq : final (outputTape computation) = encoded computation.outputDomain sizes
      (computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩) := by
    rw [← resultLayout]
    exact (canonical resultName).trans (correct sizes input good sourceOutput result)
  let output : Outputs (domains computation scratchDomains)
      (outputTapes computation ScratchName) sizes :=
    fun _ => computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩
  refine ⟨ticks, output, final, cost, trace, ⟨good, rfl⟩, ?_⟩
  intro name
  cases name
  exact resultEq

/-- Domain equality supplies carrier transport, widths, and encodings together. -/
theorem ofDomainLayout [Fintype SourceTape] {SourceOutputName : Type}
    (computation : Computation.{carrierLevel} Parameter InputName)
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (sourceSizes : Parameter ↪ SourceTape)
    (sourceOutputTapes : SourceOutputName ↪ SourceTape)
    (machine : Machine (Alphabet SourceTape) State) (entry exit : State)
    (sourceHypothesis : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes → Prop)
    (sourceContract : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes →
      Outputs sourceDomains sourceOutputTapes sizes → Prop)
    (certificate : CallingConvention.Realizes sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
      machine entry exit sourceHypothesis sourceContract)
    (layout : SourceTape ↪ TapeName computation ScratchName)
    (sameDomain : ∀ name, domains computation scratchDomains (layout name) = sourceDomains name)
    (readonly : ∀ name, sourceReadOnly name = readOnly computation (layout name))
    (sizeLayout : ∀ parameter, layout (sourceSizes parameter) = .inl parameter)
    (resultName : SourceOutputName)
    (resultLayout : layout (sourceOutputTapes resultName) = outputTape computation) :
    let values := fun name sizes => Equiv.cast
      (congrArg (fun domain => domain.Carrier sizes) (sameDomain name))
    (∀ sizes input, computation.precondition sizes (arguments computation scratchDomains sizes input) →
      sourceHypothesis sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input)) →
    (∀ sizes input (good : computation.precondition sizes (arguments computation scratchDomains sizes input)) output,
      sourceContract sizes (pullInputs computation scratchDomains sourceDomains sourceReadOnly
        layout values readonly sizes input) output →
      encoded (sourceDomains (sourceOutputTapes resultName)) sizes (output resultName) =
        encoded computation.outputDomain sizes
          (computation.compute sizes ⟨arguments computation scratchDomains sizes input, good⟩)) →
    computation.Realizable := by
  intro values valid correct
  refine ofLayout computation scratchDomains sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
    machine entry exit sourceHypothesis sourceContract certificate layout values
    (fun name sizes => congrArg (fun domain => domain.width sizes) (sameDomain name)) ?_
    readonly sizeLayout resultName resultLayout valid correct
  intro name sizes value
  have transport {first second : EncodedDomain.{0, carrierLevel} Parameter} (same : first = second)
      (value : first.Carrier sizes) : encoded first sizes value = encoded second sizes
        (Equiv.cast (congrArg (fun domain => domain.Carrier sizes) same) value) := by
    subst second
    rfl
  exact transport (sameDomain name) value

/-- Named size, argument, and result roles; all other tapes are private. -/
abbrev PublicTape (Parameter InputName : Type) := Parameter ⊕ (InputName ⊕ Unit)

abbrev PrivateTape (placement : PublicTape Parameter InputName ↪ SourceTape) :=
  {name : SourceTape // name ∉ Set.range placement}

/-- Completing a public placement allocates exactly the remaining source tapes.
The associativity maps and complement equivalence come from Mathlib. -/
noncomputable def namedCompletion (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) :
    TapeName computation (PrivateTape placement) ≃ SourceTape := by
  classical
  exact (Equiv.sumAssoc Parameter InputName (Unit ⊕ PrivateTape placement)).symm.trans
    ((Equiv.sumAssoc (Parameter ⊕ InputName) Unit (PrivateTape placement)).symm.trans
      ((Equiv.sumCongr (Equiv.sumAssoc Parameter InputName Unit) (Equiv.refl _)).trans
        ((Equiv.sumCongr (Equiv.ofInjective placement placement.injective) (Equiv.refl _)).trans
          (Equiv.Set.sumCompl (Set.range placement)))))

abbrev publicTape (computation : Computation.{carrierLevel} Parameter InputName) {Private : Type} :
    PublicTape Parameter InputName → TapeName computation Private := by
  intro role
  cases role with
  | inl parameter => exact .inl parameter
  | inr role => cases role with
    | inl name => exact inputTape computation name
    | inr _ => exact outputTape computation

@[simp] theorem namedCompletion_public (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) (role : PublicTape Parameter InputName) :
    namedCompletion computation placement (publicTape computation role) = placement role := by
  rcases role with parameter | name | result <;> rfl

@[simp] theorem namedCompletion_private (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) (name : PrivateTape placement) :
    namedCompletion computation placement (scratchTape computation name) = name.val := rfl

noncomputable def namedLayout (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) :
    SourceTape ↪ TapeName computation (PrivateTape placement) :=
  (namedCompletion computation placement).symm.toEmbedding

@[simp] theorem namedLayout_public (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) (role : PublicTape Parameter InputName) :
    namedLayout computation placement (placement role) = publicTape computation role := by
  change (namedCompletion computation placement).symm (placement role) = _
  rw [← namedCompletion_public computation placement role, Equiv.symm_apply_apply]

noncomputable abbrev publicDomains (computation : Computation.{carrierLevel} Parameter InputName) :
    PublicTape Parameter InputName → EncodedDomain.{0, carrierLevel} Parameter :=
  Sum.elim EncodedDomain.unary (Sum.elim computation.inputDomains (fun _ => computation.outputDomain))

abbrev publicReadOnly : PublicTape Parameter InputName → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => false))

/-- Public domain equalities determine the entire completed layout. Private
codec widths and encodings are inherited directly from the source domains. -/
theorem namedDomains (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (publicEqual : ∀ role, publicDomains computation role = sourceDomains (placement role))
    (name : SourceTape) :
    domains computation (fun scratch => sourceDomains scratch.val)
      (namedLayout computation placement name) = sourceDomains name := by
  have forward (target : TapeName computation (PrivateTape placement)) :
      domains computation (fun scratch => sourceDomains scratch.val) target =
        sourceDomains (namedCompletion computation placement target) := by
    rcases target with parameter | argument | result | scratch
    · exact publicEqual (.inl parameter)
    · exact publicEqual (.inr (.inl argument))
    · cases result; exact publicEqual (.inr (.inr ()))
    · rfl
  simpa only [namedLayout, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using
    forward ((namedCompletion computation placement).symm name)

/-- Read-only public roles and writable private tapes determine the mask. -/
theorem namedReadOnly (computation : Computation.{carrierLevel} Parameter InputName)
    (placement : PublicTape Parameter InputName ↪ SourceTape) (sourceReadOnly : SourceTape → Bool)
    (publicReadonly : ∀ role, sourceReadOnly (placement role) = publicReadOnly role)
    (privateWritable : ∀ name, name ∉ Set.range placement → sourceReadOnly name = false)
    (name : SourceTape) :
    sourceReadOnly name = readOnly computation (namedLayout computation placement name) := by
  obtain ⟨target, rfl⟩ := (namedCompletion computation placement).surjective name
  change sourceReadOnly (namedCompletion computation placement target) =
    readOnly computation ((namedCompletion computation placement).symm
      (namedCompletion computation placement target))
  rw [Equiv.symm_apply_apply]
  rcases target with parameter | argument | result | scratch
  · exact publicReadonly (.inl parameter)
  · exact publicReadonly (.inr (.inl argument))
  · cases result; exact publicReadonly (.inr (.inr ()))
  · exact privateWritable scratch.val scratch.property

/-- Mathematical arguments selected by the named public input roles. -/
noncomputable def namedArguments (computation : Computation.{carrierLevel} Parameter InputName)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (placement : PublicTape Parameter InputName ↪ SourceTape)
    (publicEqual : ∀ role, publicDomains computation role = sourceDomains (placement role))
    (publicReadonly : ∀ role, sourceReadOnly (placement role) = publicReadOnly role)
    (sizes : Parameter → ℕ) (input : Inputs sourceDomains sourceReadOnly sizes) :
    computation.Arguments sizes := fun name =>
  (Equiv.cast (congrArg (fun domain => domain.Carrier sizes)
    (show computation.inputDomains name = sourceDomains (placement (.inr (.inl name))) from
      publicEqual (.inr (.inl name))))).symm
    (input ⟨placement (.inr (.inl name)), (publicReadonly (.inr (.inl name))).trans rfl⟩)

private theorem namedArguments_pullInputs (computation : Computation.{carrierLevel} Parameter InputName)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (placement : PublicTape Parameter InputName ↪ SourceTape)
    (publicEqual : ∀ role, publicDomains computation role = sourceDomains (placement role))
    (publicReadonly : ∀ role, sourceReadOnly (placement role) = publicReadOnly role)
    (privateWritable : ∀ name, name ∉ Set.range placement → sourceReadOnly name = false)
    (sizes : Parameter → ℕ) (input : Inputs (domains computation
      (fun name : PrivateTape placement => sourceDomains name.val)) (readOnly computation) sizes) :
    namedArguments computation sourceDomains sourceReadOnly placement publicEqual publicReadonly sizes
      (pullInputs computation (fun name : PrivateTape placement => sourceDomains name.val) sourceDomains sourceReadOnly
        (namedLayout computation placement)
        (fun name sizes => Equiv.cast (congrArg (fun domain => domain.Carrier sizes)
          (namedDomains computation placement sourceDomains publicEqual name)))
        (namedReadOnly computation placement sourceReadOnly publicReadonly privateWritable) sizes input) =
      arguments computation (fun name : PrivateTape placement => sourceDomains name.val) sizes input := by
  funext name
  have congruent (first second : {name : TapeName computation (PrivateTape placement) //
      readOnly computation name = true}) (equal : first.val = second.val) :
      HEq (input first) (input second) := by
    have same : first = second := Subtype.ext equal
    subst second
    rfl
  dsimp only [namedArguments, pullInputs, arguments]
  apply eq_of_heq
  exact (cast_heq _ _).trans ((cast_heq _ _).trans
    (congruent _ _ (namedLayout_public computation placement (.inr (.inl name)))))

/-- Place named public roles and allocate all other tapes privately. Callers
prove only public domain compatibility and the primitive's read-only mask;
width, encoding, allocation, and wiring proofs are shared. -/
theorem ofNamedLayout [Fintype SourceTape] {SourceOutputName : Type}
    (computation : Computation.{carrierLevel} Parameter InputName)
    (sourceDomains : SourceTape → EncodedDomain.{0, carrierLevel} Parameter)
    (sourceReadOnly : SourceTape → Bool) (sourceSizes : Parameter ↪ SourceTape)
    (sourceOutputTapes : SourceOutputName ↪ SourceTape)
    (machine : Machine (Alphabet SourceTape) State) (entry exit : State)
    (sourceHypothesis : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes → Prop)
    (sourceContract : ∀ sizes, Inputs sourceDomains sourceReadOnly sizes →
      Outputs sourceDomains sourceOutputTapes sizes → Prop)
    (certificate : CallingConvention.Realizes sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
      machine entry exit sourceHypothesis sourceContract)
    (placement : PublicTape Parameter InputName ↪ SourceTape)
    (publicEqual : ∀ role, publicDomains computation role = sourceDomains (placement role))
    (publicReadonly : ∀ role, sourceReadOnly (placement role) = publicReadOnly role)
    (privateWritable : ∀ name, name ∉ Set.range placement → sourceReadOnly name = false)
    (sizeNames : ∀ parameter, placement (.inl parameter) = sourceSizes parameter)
    (resultName : SourceOutputName)
    (resultPlace : placement (.inr (.inr ())) = sourceOutputTapes resultName) :
    (∀ sizes input, computation.precondition sizes
        (namedArguments computation sourceDomains sourceReadOnly placement publicEqual publicReadonly sizes input) →
      sourceHypothesis sizes input) →
    (∀ sizes input (good : computation.precondition sizes
        (namedArguments computation sourceDomains sourceReadOnly placement publicEqual publicReadonly sizes input)) output,
      sourceContract sizes input output →
      encoded (sourceDomains (sourceOutputTapes resultName)) sizes (output resultName) =
        encoded computation.outputDomain sizes (computation.compute sizes ⟨namedArguments computation sourceDomains
          sourceReadOnly placement publicEqual publicReadonly sizes input, good⟩)) →
    computation.Realizable := by
  classical
  intro valid correct
  let scratchDomains := fun name : PrivateTape placement => sourceDomains name.val
  let layout := namedLayout computation placement
  let sameDomain := namedDomains computation placement sourceDomains publicEqual
  let readonly := namedReadOnly computation placement sourceReadOnly publicReadonly privateWritable
  refine ofDomainLayout computation scratchDomains sourceDomains sourceReadOnly sourceSizes sourceOutputTapes
    machine entry exit sourceHypothesis sourceContract certificate layout sameDomain readonly ?_
    resultName ?_ ?_ ?_
  · intro parameter
    rw [← sizeNames]
    exact namedLayout_public computation placement (.inl parameter)
  · rw [← resultPlace]
    exact namedLayout_public computation placement (.inr (.inr ()))
  · intro sizes input good
    apply valid sizes _
    have argumentMatch := namedArguments_pullInputs computation sourceDomains sourceReadOnly placement
      publicEqual publicReadonly privateWritable sizes input
    exact argumentMatch.symm ▸ good
  · intro sizes input good output result
    have argumentMatch := namedArguments_pullInputs computation sourceDomains sourceReadOnly placement
      publicEqual publicReadonly privateWritable sizes input
    have compatible := argumentMatch.symm ▸ good
    have equality := correct sizes _ compatible output result
    simpa only [argumentMatch] using equality

end Polytime2.Computation.Realizable.Internal
