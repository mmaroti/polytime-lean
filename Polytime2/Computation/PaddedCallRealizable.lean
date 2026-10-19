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

import Polytime2.Computation.PaddedCall
import Polytime2.Computation.SizePreparation
import Polytime2.Computation.RecordArguments
import Polytime2.Primitives.Blank
import Polytime2.Arithmetic.CounterOperations

/-! # Certified calls supplied with bounded unary sizes and padded input data -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

noncomputable def paddedCallInputs (computation : Computation NewParameter Unit)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) : NewParameter ⊕ Unit → EncodedDomain Parameter :=
  Sum.elim (fun parameter => boundedUnary (bounds parameter))
    (fun _ => bitVectors (SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial))

def paddedCallAssignment (computation : Computation NewParameter Unit)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (paddedCallInputs computation bounds name).Carrier sizes) : NewParameter → ℕ :=
  fun parameter => (arguments (.inl parameter)).val

/-- The binary argument is accepted when it is exactly a padded admissible
callee input. The chosen witness is only a mathematical specification. -/
noncomputable def paddedCall (computation : Computation NewParameter Unit)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) : Computation Parameter (NewParameter ⊕ Unit) where
  inputDomains := paddedCallInputs computation bounds
  outputDomain := bitVectors (SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial)
  precondition sizes arguments := ∃ value : (computation.inputDomains ()).Carrier
      (paddedCallAssignment computation bounds sizes arguments),
    ((computation.inputDomains ()).encode (paddedCallAssignment computation bounds sizes arguments) value).setWidth
      (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial)) =
        arguments (.inr ()) ∧
    computation.precondition (paddedCallAssignment computation bounds sizes arguments) (fun _ => value)
  compute sizes arguments :=
    (computation.outputDomain.encode (paddedCallAssignment computation bounds sizes arguments.val)
      (computation.compute (paddedCallAssignment computation bounds sizes arguments.val)
        ⟨(fun _ => Classical.choose arguments.property), (Classical.choose_spec arguments.property).2⟩)).setWidth
      (MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial))

namespace Realizable

open MultiTape CallingConvention Internal

/-- Preparing actual headers and invoking the padded routine is a external
composition rule, with all private capacities and execution witnesses hidden. -/
theorem paddedCall {computation : Computation NewParameter Unit}
    (realizable : computation.Realizable) (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    (computation.paddedCall bounds).Realizable := by
  classical
  let inputs := paddedCallInputs computation bounds
  have producers (parameter : NewParameter) :
      (Computation.mk inputs (boundedUnary (bounds parameter)) (fun _ _ => True)
        (fun _ arguments => arguments.val (.inl parameter))).Realizable := by
    exact (copy_realizable (boundedUnary (bounds parameter))).withArguments inputs
      ⟨(fun _ : Unit => .inl parameter), by intro first second equal; cases first; cases second; rfl⟩
      (by intro name; cases name; rfl)
  obtain ⟨HeaderScratch, headerScratchFinite, HeaderState, headerStateFinite, headerMachine,
    headerEntry, headerExit, headerCapacity, headerBound, headerHalt, prepareHeaders⟩ :=
    preparesSizes inputs (fun _ _ => True) bounds (fun parameter _ arguments => arguments.val (.inl parameter)) producers
  let _ : ∀ parameter, Fintype (HeaderScratch parameter) := headerScratchFinite
  let _headerStateFinite := headerStateFinite
  obtain ⟨CoreScratch, coreScratchFinite, CoreState, coreStateFinite, coreMachine,
    coreEntry, coreExit, coreCapacity, coreBound, coreHalt, execute⟩ :=
    preparesPaddedCall computation realizable bounds
  let _coreScratchFinite := coreScratchFinite
  let _coreStateFinite := coreStateFinite
  let HeaderBlock := Σ parameter : NewParameter, Unit ⊕ HeaderScratch parameter
  let Scratch := HeaderBlock ⊕ CoreScratch
  let target := computation.paddedCall bounds
  let outputCapacity := SizeSubstitution.polynomial bounds computation.outputDomain.widthPolynomial
  let inputCapacity := SizeSubstitution.polynomial bounds (computation.inputDomains ()).widthPolynomial
  let maximum := headerCapacity + coreCapacity
  apply Realizable.withComputedWidth target outputCapacity
  apply Realizable.withComputedWidth (target.withUnaryWidth outputCapacity) maximum
  let extended := (target.withUnaryWidth outputCapacity).withUnaryWidth maximum
  let scratch : Scratch → EncodedDomain Parameter := fun _ => bitVectors maximum
  let headerTape (name : HeaderBlock) : TapeName extended Scratch := scratchTape extended (.inl name)
  let coreTape (name : CoreScratch) : TapeName extended Scratch := scratchTape extended (.inr name)
  let capacityTape : TapeName extended Scratch := inputTape extended (.inr ())
  let outputCapacityTape : TapeName extended Scratch := inputTape extended (.inl (.inr ()))
  let originalTape (name : NewParameter ⊕ Unit) : TapeName extended Scratch := inputTape extended (.inl (.inl name))
  let scratchEmbedding : Scratch ↪ TapeName extended Scratch :=
    ⟨scratchTape extended, by intro first second equal; cases equal; rfl⟩
  let resetTargets := (Fintype.equivFin Scratch).symm.toEmbedding.trans scratchEmbedding
  have separate index : capacityTape ≠ resetTargets index := by
    simp [capacityTape, resetTargets, scratchEmbedding, inputTape, scratchTape]
  let reset := Blank.prepare capacityTape resetTargets separate
  let headerWiring : SizePreparationTape Parameter (NewParameter ⊕ Unit) NewParameter HeaderScratch ↪ TapeName extended Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => originalTape argument
      | .inr (.inr name) => headerTape name), by
      intro first second equal
      rcases first with parameter | argument | name <;>
        rcases second with parameter' | argument' | name'
      all_goals cases equal <;> rfl⟩
  let coreWiring : PaddedCallTape NewParameter CoreScratch ↪ TapeName extended Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => headerTape ⟨parameter, .inl ()⟩
      | .inr (.inl name) => if name = 0 then outputCapacityTape
          else if name = 1 then originalTape (.inr ()) else outputTape extended
      | .inr (.inr name) => coreTape name), by
      intro first second equal
      rcases first with parameter | external | name <;>
        rcases second with parameter' | external' | name'
      all_goals try fin_cases external
      all_goals try fin_cases external'
      all_goals first
        | rfl
        | (dsimp [headerTape, outputCapacityTape, originalTape, coreTape, inputTape, outputTape, scratchTape] at equal
           cases equal <;> rfl)⟩
  let headers : Machine (Alphabet (TapeName extended Scratch)) HeaderState := MultiTape.wire headerWiring headerMachine
  let startup := MultiTape.sequence reset headers headerEntry
  let call : Machine (Alphabet (TapeName extended Scratch)) CoreState := MultiTape.wire coreWiring coreMachine
  let algorithm := MultiTape.sequence startup call coreEntry
  refine ⟨Scratch, inferInstance, scratch, _, inferInstance, algorithm,
    .inl (.inl (Pipeline.position (fun _ : Fin (Fintype.card Scratch) => (Sum.inl () : SymbolScan.State Unit)) 0)),
    .inr coreExit, ?_⟩
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
    Fintype.card Scratch * (2 * maximum + 3) + headerBound + coreBound + 2, ?_⟩
  · intro symbols; simp [algorithm, MultiTape.sequence, call, MultiTape.wire, coreHalt]
  intro sizes input initial valid represented sizeHeaders
  let arguments := Internal.arguments extended scratch sizes input
  let originalArguments : target.Arguments sizes := fun name => arguments (.inl (.inl name))
  let actual := paddedCallAssignment computation bounds sizes originalArguments
  let value := Classical.choose valid
  have valueSpec := Classical.choose_spec valid
  let sourceArguments : computation.Arguments actual := fun _ => value
  let width := fun role => (domains extended scratch role).width sizes
  let readonly : TapeName extended Scratch → Bool := readOnly extended
  have capacityHeader : initial capacityTape = unary (MvPolynomial.eval sizes maximum) := by
    have ready := represented.1 capacityTape rfl
    change initial capacityTape = encoded (unaryOfLength maximum) sizes (arguments (.inr ())) at ready
    rw [show arguments (.inr ()) = PUnit.unit from @Subsingleton.elim PUnit.{1} inferInstance _ _,
      encoded_unaryOfLength] at ready
    exact ready
  have outputHeader : initial outputCapacityTape = unary (MvPolynomial.eval sizes outputCapacity) := by
    have ready := represented.1 outputCapacityTape rfl
    change initial outputCapacityTape = encoded (unaryOfLength outputCapacity) sizes (arguments (.inl (.inr ()))) at ready
    rw [show arguments (.inl (.inr ())) = PUnit.unit from @Subsingleton.elim PUnit.{1} inferInstance _ _,
      encoded_unaryOfLength] at ready
    exact ready
  obtain ⟨resetTicks, resetFinal, resetCost, resetTrace, resetValues⟩ := Blank.prepare_runs capacityTape resetTargets separate
    width readonly (MvPolynomial.eval sizes maximum) rfl (fun _ => rfl) (fun _ => rfl)
    initial capacityHeader represented.region
  have privateBlank (name : Scratch) : resetFinal (scratchTape extended name) = buffer [] := by
    have cleared := resetValues (Fintype.equivFin Scratch name)
    change resetFinal (scratchTape extended ((Fintype.equivFin Scratch).symm
      (Fintype.equivFin Scratch name))) = buffer [] at cleared
    have same := (Fintype.equivFin Scratch).symm_apply_apply name
    rw [same] at cleared
    exact cleared
  have headerWidths : ∀ role, width (headerWiring role) =
      sizePreparationWidths inputs HeaderScratch sizes (MvPolynomial.eval sizes maximum) role := by
    rintro (parameter | argument | name)
    · simp [width, domains, EncodedDomain.unary, EncodedDomain.ofCodec, sizePreparationWidths, headerWiring]
    · rfl
    · rfl
  have headerFits : MvPolynomial.eval sizes headerCapacity ≤ MvPolynomial.eval sizes maximum := by
    simp only [maximum, map_add]; omega
  obtain ⟨headerTicks, headerFinal, headerCost, headerTrace, ready⟩ := prepareHeaders sizes originalArguments trivial
    (MvPolynomial.eval sizes maximum) headerFits (fun role => resetFinal (headerWiring role))
    (fun parameter => (resetTrace.readOnly_tape (.inl parameter) rfl).trans (sizeHeaders parameter))
    (by intro name; exact (resetTrace.readOnly_tape (originalTape name) rfl).trans (represented.1 (originalTape name) rfl))
    (fun parameter block => privateBlank (.inl ⟨parameter, block⟩))
    (by intro role; rw [← headerWidths]; exact resetTrace.region _ (represented.region _))
  obtain ⟨middle, headersLifted, located, outside, preserved⟩ := headerTrace.wire_restoring headerWiring width readonly headerWidths
    (by rintro (parameter | argument | name) premise; rfl; rfl; contradiction)
    resetFinal (fun _ => rfl)
  have startupTrace := resetTrace.sequence headers headerEntry (by intro symbols; rfl) headersLifted
  have coreFresh (name : CoreScratch) : middle (coreTape name) = buffer [] := by
    apply (outside _ ?_).trans (privateBlank (.inr name))
    rintro ⟨role, equal⟩
    rcases role with parameter | argument | block <;>
      dsimp [headerWiring, coreTape, headerTape, originalTape, scratchTape, inputTape] at equal <;> cases equal
  have actualHeader (parameter) : middle (headerTape ⟨parameter, .inl ()⟩) = unary (actual parameter) :=
    (located (.inr (.inr ⟨parameter, .inl ()⟩))).trans (ready parameter)
  have bounded parameter : actual parameter ≤ MvPolynomial.eval sizes (bounds parameter) :=
    Nat.le_of_lt_succ (originalArguments (.inl parameter)).isLt
  have coreFits : MvPolynomial.eval sizes coreCapacity ≤ MvPolynomial.eval sizes maximum := by
    simp only [maximum, map_add]; omega
  have coreRegions : ∀ role, Region (paddedCallWidths bounds inputCapacity outputCapacity sizes
      (MvPolynomial.eval sizes maximum) role) 0 (middle (coreWiring role)) := by
    rintro (parameter | external | name)
    · change Region (MvPolynomial.eval sizes (bounds parameter)) 0 (middle (headerTape ⟨parameter, .inl ()⟩))
      rw [actualHeader]
      have region := encoded_region (EncodedDomain.unary parameter : EncodedDomain.{0, 0} NewParameter) actual PUnit.unit
      rw [encoded_unary] at region
      have small : Region (actual parameter) 0 (unary (actual parameter)) := by
        simpa [EncodedDomain.unary, EncodedDomain.ofCodec] using region
      intro position beyond
      exact small position (by have le := bounded parameter; omega)
    · fin_cases external
      · exact startupTrace.region outputCapacityTape (represented.region _)
      · exact startupTrace.region (originalTape (.inr ())) (represented.region _)
      · exact startupTrace.region (outputTape extended) (represented.region _)
    · change Region _ 0 (middle (coreTape name))
      rw [coreFresh]; exact blank_region _
  obtain ⟨coreTicks, coreFinal, coreCost, coreTrace, correct⟩ := execute sizes actual bounded
    sourceArguments valueSpec.2 (MvPolynomial.eval sizes maximum) coreFits
    (fun role => middle (coreWiring role)) actualHeader
    ((startupTrace.readOnly_tape outputCapacityTape rfl).trans outputHeader)
    (by
      have original := (startupTrace.readOnly_tape (originalTape (.inr ())) rfl).trans
        (represented.1 (originalTape (.inr ())) rfl)
      change middle (originalTape (.inr ())) = encoded (bitVectors inputCapacity) sizes
        (originalArguments (.inr ())) at original
      change middle (originalTape (.inr ())) = buffer (Binary.word (ArrayEncoding.bits _))
      have payloadEq : ((computation.inputDomains ()).encode actual value).setWidth
          (MvPolynomial.eval sizes inputCapacity) = originalArguments (.inr ()) := valueSpec.1
      rw [← payloadEq] at original
      exact original)
    coreFresh coreRegions
  have enlarged := coreTrace.regions (fun role => width (coreWiring role)) (fun _ => 0) (by
    rintro (parameter | external | name) writable
    · contradiction
    · fin_cases external
      · contradiction
      · contradiction
      · exact ⟨by omega, by simp only [zero_add]; rfl⟩
    · exact ⟨by omega, by simp only [zero_add]; rfl⟩)
  simp only [add_zero] at enlarged
  obtain ⟨final, lifted, finalLocated, finalOutside, finalPreserved⟩ := enlarged.wire_restoring coreWiring width readonly
    (fun _ => rfl) (by
      rintro (parameter | external | name) premise
      · rfl
      · fin_cases external <;> first | rfl | contradiction
      · contradiction) middle (fun _ => rfl)
  have combined := startupTrace.sequence call coreEntry
    (by intro symbols; simp [MultiTape.sequence, headers, MultiTape.wire, headerHalt]) lifted
  refine ⟨resetTicks + headerTicks + 1 + coreTicks + 1,
    (fun _ => extended.compute sizes ⟨arguments, valid⟩), final, ?_, combined, ⟨valid, rfl⟩, ?_⟩
  · simp only [map_add, map_mul, map_natCast, Nat.cast_id, map_ofNat]
    omega
  · intro name; cases name
    exact (finalLocated (.inr (.inl 2))).trans correct

end Realizable
end Polytime2.Computation
