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

import Polytime2.Computation.ComputedSizes
import Polytime2.Computation.ComputedSizeRun
import Polytime2.Computation.SizePreparation
import Polytime2.Primitives.Blank

/-! # Certified polynomial reparameterization

This is the fixed-assignment case of size preparation. The source's arguments
and results keep their canonical bits, and source scratch keeps its exact
substituted widths. Only the private header compiler needs larger capacities.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

universe carrierLevel

open CallingConvention

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

@[simp] theorem encoded_substitute (domain : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : domain.Carrier (SizeSubstitution.assignment substitution sizes)) :
    encoded (domain.substitute substitution) sizes value =
      encoded domain (SizeSubstitution.assignment substitution sizes) value := by
  exact congrArg tape (substitute_encode_bits domain substitution sizes value)

end Polytime2.EncodedDomain

namespace Polytime2.Computation

universe carrierLevel

variable {Parameter NewParameter InputName : Type}
variable [Fintype Parameter] [Fintype NewParameter] [Fintype InputName]

/-- Substitute caller polynomials for every public size of a computation. -/
noncomputable def substitute (computation : Computation.{carrierLevel} NewParameter InputName)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) : Computation Parameter InputName where
  inputDomains name := (computation.inputDomains name).substitute substitution
  outputDomain := computation.outputDomain.substitute substitution
  precondition sizes := computation.precondition (SizeSubstitution.assignment substitution sizes)
  compute sizes := computation.compute (SizeSubstitution.assignment substitution sizes)

namespace Realizable

open MultiTape CallingConvention Internal

/-- Polynomial assignments are prepared privately using the same unary-producer
compiler as value-dependent assignments. No additional public size tapes appear. -/
theorem substitute {computation : Computation.{carrierLevel} NewParameter InputName}
    (realizable : computation.Realizable) (substitution : NewParameter → MvPolynomial Parameter ℕ) :
    (computation.substitute substitution).Realizable := by
  classical
  obtain ⟨SourceScratch, sourceScratchFinite, sourceScratchDomains, SourceState, sourceStateFinite,
    source, sourceEntry, sourceExit, sourceCertificate⟩ := realizable
  let _sourceScratchFinite := sourceScratchFinite
  let _sourceStateFinite := sourceStateFinite
  obtain ⟨HeaderScratch, headerScratchFinite, HeaderState, headerStateFinite, headerMachine,
    headerEntry, headerExit, headerCapacity, headerBound, headerHalt, prepareHeaders⟩ :=
    Internal.preparesSizes (Parameter := Parameter) (InputName := Empty) Empty.elim (fun _ _ => True)
      substitution (fun parameter sizes _ => Fin.last (MvPolynomial.eval sizes (substitution parameter)))
      (fun parameter => polynomialUnarySize_realizable (substitution parameter))
  let _ : ∀ parameter, Fintype (HeaderScratch parameter) := headerScratchFinite
  let _headerStateFinite := headerStateFinite
  let HeaderBlock := Σ parameter : NewParameter, Unit ⊕ HeaderScratch parameter
  let maximum := headerCapacity + ∑ parameter, substitution parameter
  let target := computation.substitute substitution
  apply Realizable.withComputedWidth target maximum
  let extended := target.withUnaryWidth maximum
  let Scratch := HeaderBlock ⊕ SourceScratch
  let scratch : Scratch → EncodedDomain Parameter :=
    Sum.elim (fun _ => (EncodedDomain.unaryOfLength maximum : EncodedDomain.{0, carrierLevel} Parameter))
      (fun name => (sourceScratchDomains name).substitute substitution)
  let headerTape (block : HeaderBlock) : TapeName extended Scratch := scratchTape extended (.inl block)
  let headerEmbedding : HeaderBlock ↪ TapeName extended Scratch :=
    ⟨headerTape, by intro first second equal; cases equal; rfl⟩
  let resetTargets := (Fintype.equivFin HeaderBlock).symm.toEmbedding.trans headerEmbedding
  let capacityTape : TapeName extended Scratch := inputTape extended (.inr ())
  have separate (index) : capacityTape ≠ resetTargets index := by
    simp [capacityTape, resetTargets, headerEmbedding, headerTape, inputTape, scratchTape]
  let reset := Blank.prepare capacityTape resetTargets separate
  let headerWiring : SizePreparationTape Parameter Empty NewParameter HeaderScratch ↪ TapeName extended Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => .inl parameter
      | .inr (.inl impossible) => impossible.elim
      | .inr (.inr block) => headerTape block), by
      intro first second equal
      rcases first with parameter | impossible | block <;>
        rcases second with parameter' | impossible' | block'
      all_goals first
        | exact impossible.elim
        | exact impossible'.elim
        | (dsimp only [headerTape, scratchTape] at equal; cases equal <;> rfl)⟩
  let sourceWiring : TapeName computation SourceScratch ↪ TapeName extended Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => headerTape ⟨parameter, .inl ()⟩
      | .inr (.inl argument) => inputTape extended (.inl argument)
      | .inr (.inr (.inl _)) => outputTape extended
      | .inr (.inr (.inr name)) => scratchTape extended (.inr name)), by
      intro first second equal
      rcases first with parameter | argument | result | name <;>
        rcases second with parameter' | argument' | result' | name'
      all_goals first
        | (cases result; cases result'; rfl)
        | (dsimp only [headerTape, inputTape, outputTape, scratchTape] at equal; cases equal <;> rfl)⟩
  let headers : Machine (Alphabet (TapeName extended Scratch)) HeaderState := MultiTape.wire headerWiring headerMachine
  let startup := MultiTape.sequence reset headers headerEntry
  let call : Machine (Alphabet (TapeName extended Scratch)) SourceState := MultiTape.wire sourceWiring source
  let algorithm := MultiTape.sequence startup call sourceEntry
  obtain ⟨sourceBound, execute⟩ := Internal.boundedWiredRuns sourceScratchDomains source sourceEntry sourceExit
    sourceCertificate sourceWiring substitution
  refine ⟨Scratch, inferInstance, scratch, _, inferInstance, algorithm,
    .inl (.inl (Pipeline.position (fun _ : Fin (Fintype.card HeaderBlock) => (Sum.inl () : SymbolScan.State Unit)) 0)),
    .inr sourceExit, ?_⟩
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
    Fintype.card HeaderBlock * (2 * maximum + 3) + headerBound + sourceBound + 2, ?_⟩
  · intro symbols; simp [algorithm, MultiTape.sequence, call, MultiTape.wire, sourceCertificate.2.2.1]
  intro sizes input initial valid represented sizeHeaders
  let arguments := Internal.arguments extended scratch sizes input
  let width := fun role => (Internal.domains extended scratch role).width sizes
  let readonly : TapeName extended Scratch → Bool := Internal.readOnly extended
  have capacityHeader : initial capacityTape = unary (MvPolynomial.eval sizes maximum) := by
    have encodedHeader := represented.1 capacityTape rfl
    change initial capacityTape = encoded (EncodedDomain.unaryOfLength maximum) sizes (arguments (.inr ())) at encodedHeader
    rw [show arguments (.inr ()) = PUnit.unit from @Subsingleton.elim PUnit.{carrierLevel + 1} inferInstance _ _,
      EncodedDomain.encoded_unaryOfLength] at encodedHeader
    exact encodedHeader
  obtain ⟨resetTicks, resetFinal, resetCost, resetTrace, resetValues⟩ := Blank.prepare_runs capacityTape resetTargets separate
    width readonly (MvPolynomial.eval sizes maximum) rfl (fun _ => rfl) (fun _ => rfl)
    initial capacityHeader represented.region
  have privateBlank (block : HeaderBlock) : resetFinal (headerTape block) = buffer [] := by
    have cleared := resetValues (Fintype.equivFin HeaderBlock block)
    change resetFinal (headerTape ((Fintype.equivFin HeaderBlock).symm
      (Fintype.equivFin HeaderBlock block))) = buffer [] at cleared
    have same : (Fintype.equivFin HeaderBlock).symm
        (Fintype.equivFin HeaderBlock block) = block :=
      (Fintype.equivFin HeaderBlock).symm_apply_apply block
    rw [same] at cleared
    exact cleared
  have headerWidths : ∀ role, width (headerWiring role) =
      sizePreparationWidths (Empty.elim : Empty → EncodedDomain Parameter) HeaderScratch sizes
        (MvPolynomial.eval sizes maximum) role := by
    rintro (parameter | impossible | block)
    · simp [width, domains, EncodedDomain.unary, EncodedDomain.ofCodec, sizePreparationWidths, headerWiring]
    · exact impossible.elim
    · rfl
  have headerFits : MvPolynomial.eval sizes headerCapacity ≤ MvPolynomial.eval sizes maximum := by
    simp only [maximum, map_add]; omega
  obtain ⟨headerTicks, headerFinal, headerCost, headerTrace, ready⟩ := prepareHeaders sizes (fun impossible => impossible.elim) trivial
    (MvPolynomial.eval sizes maximum) headerFits (fun role => resetFinal (headerWiring role))
    (fun parameter => (resetTrace.readOnly_tape (.inl parameter) rfl).trans (sizeHeaders parameter))
    (fun impossible => impossible.elim) (fun parameter block => privateBlank ⟨parameter, block⟩)
    (by intro role; rw [← headerWidths]; exact resetTrace.region _ (represented.region _))
  obtain ⟨middle, headersLifted, located, outside, preserved⟩ := headerTrace.wire_restoring headerWiring width readonly headerWidths
    (by rintro (parameter | impossible | block) premise; rfl; exact impossible.elim; contradiction)
    resetFinal (fun _ => rfl)
  have startupTrace := resetTrace.sequence headers headerEntry (by intro symbols; rfl) headersLifted
  let actual := SizeSubstitution.assignment substitution sizes
  let sourceArguments : computation.Arguments actual := fun name => arguments (.inl name)
  have actualHeader (parameter : NewParameter) : middle (headerTape ⟨parameter, .inl ()⟩) = unary (actual parameter) :=
    (located (.inr (.inr ⟨parameter, .inl ()⟩))).trans (ready parameter)
  have widths : ∀ role, (domains computation sourceScratchDomains role).width actual ≤ width (sourceWiring role) := by
    rintro (parameter | argument | result | name)
    · change MvPolynomial.eval actual (MvPolynomial.X parameter) ≤ MvPolynomial.eval sizes maximum
      simp only [MvPolynomial.eval_X]
      change MvPolynomial.eval sizes (substitution parameter) ≤ _
      have small := Finset.single_le_sum (fun other _ => Nat.zero_le (MvPolynomial.eval sizes (substitution other)))
        (Finset.mem_univ parameter)
      simpa only [maximum, map_add, map_sum] using small.trans (Nat.le_add_left _ _)
    · simp [width, domains, sourceWiring, target, extended, Computation.withUnaryWidth, Computation.substitute,
        EncodedDomain.substitute, EncodedDomain.ofCodec, actual]
    · simp [width, domains, sourceWiring, target, extended, Computation.withUnaryWidth, Computation.substitute,
        EncodedDomain.substitute, EncodedDomain.ofCodec, actual]
    · simp [width, domains, sourceWiring, scratch, EncodedDomain.substitute, EncodedDomain.ofCodec, actual]
  have canonicalInput (name : InputName) : middle (inputTape extended (.inl name)) =
      encoded (computation.inputDomains name) actual (sourceArguments name) := by
    have canonical := represented.1 (inputTape extended (.inl name)) rfl
    change initial (inputTape extended (.inl name)) = encoded ((computation.inputDomains name).substitute substitution)
      sizes (sourceArguments name) at canonical
    exact (startupTrace.readOnly_tape _ rfl).trans (canonical.trans (EncodedDomain.encoded_substitute _ _ _ _))
  obtain ⟨sourceTicks, final, sourceCost, sourceTrace, correct, sourceOutside, sourcePreserved⟩ := execute sizes actual
    (fun _ => le_rfl) sourceArguments valid width readonly middle widths
    (by rintro (parameter | argument | result | name) premise; contradiction; rfl; contradiction; contradiction)
    actualHeader canonicalInput (by
      rintro (parameter | argument | result | name)
      · change Region (EncodedDomain.unary parameter |>.width actual) 0
          (middle (headerTape ⟨parameter, .inl ()⟩))
        rw [actualHeader]
        have region := encoded_region (EncodedDomain.unary parameter : EncodedDomain.{0, carrierLevel} NewParameter) actual PUnit.unit
        simpa only [encoded_unary] using region
      · change Region ((computation.inputDomains argument).width actual) 0
          (middle (inputTape extended (.inl argument)))
        rw [canonicalInput]
        exact encoded_region _ _ _
      · have region := startupTrace.region (outputTape extended) (represented.region _)
        simpa [width, domains, target, extended, Computation.withUnaryWidth, Computation.substitute, EncodedDomain.substitute,
          EncodedDomain.ofCodec, actual, sourceWiring] using region
      · have region := startupTrace.region (scratchTape extended (.inr name)) (represented.region _)
        simpa [width, domains, scratch, EncodedDomain.substitute, EncodedDomain.ofCodec, actual, sourceWiring] using region)
  have combined := startupTrace.sequence call sourceEntry
    (by intro symbols; simp [MultiTape.sequence, headers, MultiTape.wire, headerHalt]) sourceTrace
  refine ⟨resetTicks + headerTicks + 1 + sourceTicks + 1,
    (fun _ => extended.compute sizes ⟨arguments, valid⟩), final, ?_, combined, ⟨valid, rfl⟩, ?_⟩
  · simp only [map_add, map_mul, map_natCast, Nat.cast_id, map_ofNat]
    omega
  · intro name; cases name
    exact correct.trans (EncodedDomain.encoded_substitute computation.outputDomain substitution sizes _).symm

end Realizable
end Polytime2.Computation
