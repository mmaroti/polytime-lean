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

import Polytime2.Computation.ComputedFrame
import Polytime2.Computation.ComputedCall

/-! # Computed-size calls retaining host-domain inputs and outputs

A host value determines bounded runtime counts. Extend its size assignment,
call a computation on the unchanged host payload, and retain the computed
sizes only when the result depends on them. Host-only results can discard the
internal frame without changing their canonical bits or polynomial widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {HostParameter PayloadParameter : Type}
variable [Fintype HostParameter] [Fintype PayloadParameter]

/-- Attach the counts read from a host value to that same value. -/
noncomputable def computedHostFrame
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter)
    (counts : ∀ sizes, payload.Carrier sizes → (computedSizeDomain bounds).Carrier sizes) :=
  (extendedSizeFrame bounds payload).onResults (fun _ : Unit => payload) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => counts sizes (arguments.val ()) | true => arguments.val ()) (by intros; trivial)

/-- Only the scalar count readers need certificates; payload retention and
frame construction are shared. -/
theorem computedHostFrame_realizable
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter)
    (counts : ∀ sizes, payload.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (readers : ∀ name, (unaryMap payload (EncodedDomain.boundedUnary (bounds name))
      (fun _ _ => True) (fun sizes value => counts sizes value.val name)).Realizable) :
    (computedHostFrame bounds payload counts).Realizable := by
  apply (extendedSizeFrame_realizable bounds payload).onResults _ _ _ (by intros; trivial)
  intro choice
  cases choice
  · apply Realizable.namedRecordOutputs
    exact readers
  · exact Realizable.argument _ () _

/-- Supply a callee's renamed argument domains from one unchanged host record.
The only admissibility condition is the callee's mathematical precondition. -/
noncomputable def withRenamedRecordArgument {Parameter : Type} [Fintype Parameter]
    {count : ℕ} (computation : Computation Parameter (Fin count))
    (fields : Fin count → EncodedDomain HostParameter) (names : HostParameter → Parameter)
    (inputEqual : ∀ name, computation.inputDomains name = (fields name).renameParameters names) :=
  computation.onResults (fun _ : Unit => (EncodedDomain.record count fields).renameParameters names)
    (fun sizes arguments => computation.precondition sizes (fun name =>
      cast (congrArg (fun domain => domain.Carrier sizes) (inputEqual name).symm) (arguments () name)))
    (fun name sizes arguments =>
      cast (congrArg (fun domain => domain.Carrier sizes) (inputEqual name).symm) (arguments.val () name))
    (by intro sizes arguments; exact arguments.property)

/-- Renamed record projections share their codec and parameter transport proof. -/
theorem Realizable.withRenamedRecordArgument {Parameter : Type} [Fintype Parameter]
    {count : ℕ} {computation : Computation Parameter (Fin count)}
    (realizable : computation.Realizable)
    (fields : Fin count → EncodedDomain HostParameter) (names : HostParameter → Parameter)
    (inputEqual : ∀ name, computation.inputDomains name = (fields name).renameParameters names) :
    (computation.withRenamedRecordArgument fields names inputEqual).Realizable := by
  rcases computation with ⟨domains, output, allowed, value⟩
  have domainsEqual : domains = fun name => (fields name).renameParameters names := funext inputEqual
  subst domains
  let computation := Computation.mk (fun name => (fields name).renameParameters names) output allowed value
  apply realizable.onResults _ _ _ (by intro sizes arguments; exact arguments.property)
  intro name
  have projected := (recordProjectionAtNames_realizable count fields name names).followedBy
    (copy_realizable (computation.inputDomains name)) (inputEqual name) (by intros; trivial)
  exact projected.withPrecondition _ (by intros; trivial)

/-- Call at counts read from a host input. The precondition is exactly the
callee's admissibility at those actual counts, and the result retains them. -/
noncomputable def atComputedHostInput
    (computation : Computation (HostParameter ⊕ PayloadParameter) Unit)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter)
    (counts : ∀ sizes, payload.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = payload.renameParameters Sum.inl) :
    Computation HostParameter Unit where
  inputDomains _ := payload
  outputDomain := atComputedSizeDomain (extendedSizeBounds bounds) computation.outputDomain
  precondition sizes arguments := computation.precondition
    (computedSizeAssignment (extendedSizeBounds bounds) sizes (extendedSizeValues bounds sizes (counts sizes (arguments ()))))
    (fun _ => cast (congrArg (fun domain => domain.Carrier
      (computedSizeAssignment (extendedSizeBounds bounds) sizes
        (extendedSizeValues bounds sizes (counts sizes (arguments ()))))) inputEqual.symm) (arguments ()))
  compute sizes arguments := ⟨extendedSizeValues bounds sizes (counts sizes (arguments.val ())),
    computation.compute
      (computedSizeAssignment (extendedSizeBounds bounds) sizes (extendedSizeValues bounds sizes (counts sizes (arguments.val ()))))
      ⟨fun _ => cast (congrArg (fun domain => domain.Carrier
        (computedSizeAssignment (extendedSizeBounds bounds) sizes
          (extendedSizeValues bounds sizes (counts sizes (arguments.val ()))))) inputEqual.symm)
        (arguments.val ()), arguments.property⟩⟩

/-- Count reading, frame preparation and execution all enter the shared call
certificate, including calls whose payload depends on the chosen counts. -/
theorem Realizable.atComputedHostInput
    {computation : Computation (HostParameter ⊕ PayloadParameter) Unit}
    (realizable : computation.Realizable)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter)
    (counts : ∀ sizes, payload.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = payload.renameParameters Sum.inl)
    (readers : ∀ name, (unaryMap payload (EncodedDomain.boundedUnary (bounds name))
      (fun _ _ => True) (fun sizes value => counts sizes value.val name)).Realizable) :
    (computation.atComputedHostInput bounds payload counts inputEqual).Realizable := by
  rcases computation with ⟨domains, output, allowed, value⟩
  have domainsEqual : domains = fun _ => payload.renameParameters Sum.inl := by
    funext name
    cases name
    exact inputEqual
  subst domains
  let computation := Computation.mk (fun _ : Unit => payload.renameParameters Sum.inl) output allowed value
  let target := computation.atComputedHostInput bounds payload counts inputEqual
  have frame := (computedHostFrame_realizable bounds payload counts readers).withPrecondition
    target.precondition (by intros; trivial)
  have called := frame.followedBy (realizable.atComputedUnarySizes (extendedSizeBounds bounds))
    (by
      change atComputedSizeDomain _ (computation.inputDomains ()) = atComputedSizeDomain _ _
      rw [inputEqual]) (by intro sizes arguments valid; exact valid)
  exact called.withSpecification target.precondition target.compute (by intros; assumption) (by intros; rfl)

/-- A call whose payload uses only the retained host sizes can discard its
computed-size header. Counts and payloads are ordinary mathematical values;
only the internal frame stores the extra sizes. -/
private theorem computedHostOutput_realizable {InputName : Type} [Fintype InputName]
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (payload : EncodedDomain HostParameter)
    (inputs : InputName → EncodedDomain HostParameter)
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop)
    (counts : ∀ sizes, {arguments // allowed sizes arguments} →
      (computedSizeDomain bounds).Carrier sizes)
    (values : ∀ sizes, {arguments // allowed sizes arguments} → payload.Carrier sizes)
    (realizable : (Computation.mk inputs
      (atComputedSizeDomain (extendedSizeBounds bounds)
        (payload.renameParameters (Sum.inl : HostParameter → HostParameter ⊕ PayloadParameter)))
      allowed (fun sizes arguments => ⟨extendedSizeValues bounds sizes (counts sizes arguments),
        values sizes arguments⟩)).Realizable) :
    (Computation.mk inputs payload allowed values).Realizable := by
  let index := computedSizeDomain (extendedSizeBounds bounds)
  have viewed := realizable.withEncodedOutput (index.prod payload)
    (fun sizes arguments => (extendedSizeValues bounds sizes (counts sizes arguments), values sizes arguments))
    (by
      intro sizes
      change MvPolynomial.eval sizes (index.widthPolynomial + payload.widthPolynomial) =
        MvPolynomial.eval sizes (index.widthPolynomial +
          SizeSubstitution.polynomial (extendedSizeBounds bounds)
            (payload.renameParameters (Sum.inl : HostParameter → HostParameter ⊕ PayloadParameter)).widthPolynomial)
      rw [extendedSize_payloadWidth]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      exact (extendedSizeFrame_encode_bits bounds payload sizes
        (counts sizes arguments) (values sizes arguments)).symm)
  exact viewed.snd

@[irreducible] private noncomputable def computedHostResult
    (computation : Computation (HostParameter ⊕ PayloadParameter) Unit)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (input output : EncodedDomain HostParameter)
    (counts : ∀ sizes, input.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = input.renameParameters Sum.inl)
    (outputEqual : computation.outputDomain = output.renameParameters Sum.inl)
    (sizes : HostParameter → ℕ)
    (arguments : {arguments // (computation.atComputedHostInput bounds input counts inputEqual).precondition sizes arguments}) :
    output.Carrier sizes :=
  cast (congrArg (fun domain => domain.Carrier
    (computedSizeAssignment (extendedSizeBounds bounds) sizes
      (extendedSizeValues bounds sizes (counts sizes (arguments.val ()))))) outputEqual)
    ((computation.atComputedHostInput bounds input counts inputEqual).compute sizes arguments).2

/-- Call at runtime counts and return a host-sized result directly. The size
header remains internal when the result's carrier uses only host parameters. -/
noncomputable def atComputedHostSizes
    (computation : Computation (HostParameter ⊕ PayloadParameter) Unit)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (input output : EncodedDomain HostParameter)
    (counts : ∀ sizes, input.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = input.renameParameters Sum.inl)
    (outputEqual : computation.outputDomain = output.renameParameters Sum.inl) :
    Computation HostParameter Unit where
  inputDomains _ := input
  outputDomain := output
  precondition := (computation.atComputedHostInput bounds input counts inputEqual).precondition
  compute := computedHostResult computation bounds input output counts inputEqual outputEqual

/-- Evaluate a host-result call without unfolding its reduction boundary. -/
theorem atComputedHostSizes_compute
    (computation : Computation (HostParameter ⊕ PayloadParameter) Unit)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (input output : EncodedDomain HostParameter)
    (counts : ∀ sizes, input.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = input.renameParameters Sum.inl)
    (outputEqual : computation.outputDomain = output.renameParameters Sum.inl)
    (sizes : HostParameter → ℕ)
    (arguments : {arguments // (computation.atComputedHostInput bounds input counts inputEqual).precondition sizes arguments}) :
    (computation.atComputedHostSizes bounds input output counts inputEqual outputEqual).compute sizes arguments =
      cast (congrArg (fun domain => domain.Carrier
        (computedSizeAssignment (extendedSizeBounds bounds) sizes
          (extendedSizeValues bounds sizes (counts sizes (arguments.val ()))))) outputEqual)
        ((computation.atComputedHostInput bounds input counts inputEqual).compute sizes arguments).2 := by
  unfold atComputedHostSizes computedHostResult
  rfl

/-- The fixed host result needs no caller-side frame construction, padding
proof, or projection of the computed-size header. -/
theorem Realizable.atComputedHostSizes
    {computation : Computation (HostParameter ⊕ PayloadParameter) Unit}
    (realizable : computation.Realizable)
    (bounds : PayloadParameter → MvPolynomial HostParameter ℕ)
    (input output : EncodedDomain HostParameter)
    (counts : ∀ sizes, input.Carrier sizes → (computedSizeDomain bounds).Carrier sizes)
    (inputEqual : computation.inputDomains () = input.renameParameters Sum.inl)
    (outputEqual : computation.outputDomain = output.renameParameters Sum.inl)
    (readers : ∀ name, (unaryMap input (EncodedDomain.boundedUnary (bounds name))
      (fun _ _ => True) (fun sizes value => counts sizes value.val name)).Realizable) :
    (computation.atComputedHostSizes bounds input output counts inputEqual outputEqual).Realizable := by
  rcases computation with ⟨domains, result, allowed, value⟩
  change result = output.renameParameters Sum.inl at outputEqual
  subst result
  let computation := Computation.mk domains (output.renameParameters Sum.inl) allowed value
  unfold Computation.atComputedHostSizes
  apply computedHostOutput_realizable bounds output _ _
    (fun sizes arguments => counts sizes (arguments.val ()))
    (computedHostResult computation bounds input output counts inputEqual rfl)
  unfold computedHostResult
  exact realizable.atComputedHostInput bounds input counts inputEqual readers

end Polytime2.Computation
