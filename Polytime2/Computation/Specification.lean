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
import Polytime2.Encoding.BinaryEncoding

/-! # Mathematical decision specifications and implementation certificates

State the predicate on ordinary mathematical arguments first. The public
answer has the shared controlled reduction boundary; a private implementation
need only establish the predicate's Boolean correctness on admissible inputs.
-/

namespace Polytime2.Computation

universe carrierLevel modelLevel

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Equal mathematical arguments give equal answers, independently of their
admissibility proofs and without unfolding the answer function. -/
theorem compute_congr (computation : Computation.{carrierLevel} Parameter InputName) (sizes : Parameter → ℕ)
    (first second : {arguments : computation.Arguments sizes // computation.precondition sizes arguments})
    (same : ∀ name, first.val name = second.val name) :
    computation.compute sizes first = computation.compute sizes second :=
  congrArg (computation.compute sizes) (Subtype.ext (funext same))

/-- Decide a mathematical predicate on admissible inputs. Its polynomial-time
implementation is supplied separately by `Realizable.decision`. -/
noncomputable def decision (inputs : InputName → EncodedDomain Parameter)
    (allowed : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop)
    (predicate : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop) :
    Computation Parameter InputName := by
  classical
  exact specification inputs EncodedDomain.booleans allowed
    (fun sizes arguments => decide (predicate sizes arguments.val))

/-- The public decision contract avoids unfolding its answer or implementation. -/
theorem decision_correct (inputs : InputName → EncodedDomain Parameter)
    (allowed predicate : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop)
    (sizes : Parameter → ℕ) (arguments : {arguments // allowed sizes arguments}) :
    (decision inputs allowed predicate).compute sizes arguments = true ↔ predicate sizes arguments.val := by
  classical
  have evaluated := specification_compute inputs EncodedDomain.booleans allowed
    (fun sizes arguments => decide (predicate sizes arguments.val)) sizes arguments
  exact (congrArg (fun result : Bool => result = true) evaluated).to_iff.trans decide_eq_true_iff

/-- Certify a mathematical decision by any Boolean implementation with the same
inputs and admissibility. Correctness is an iff, with no codec or tape proof. -/
theorem Realizable.decision
    {inputs : InputName → EncodedDomain Parameter}
    {allowed : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop}
    {implementation : ∀ sizes, {arguments // allowed sizes arguments} → Bool}
    (ready : (Computation.mk inputs EncodedDomain.booleans allowed implementation).Realizable)
    (predicate : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop)
    (correct : ∀ sizes arguments valid,
      implementation sizes ⟨arguments, valid⟩ = true ↔ predicate sizes arguments) :
    (decision inputs allowed predicate).Realizable := by
  classical
  apply ready.specification
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using correct sizes arguments valid

/-- Specify a bounded or dependent output through an ordinary mathematical
observation. Existence supplies only the output bound or refinement proof.
Use `Realizable.specificationBy` when the observation determines the output. -/
noncomputable def specificationBy
    (inputs : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (output : EncodedDomain.{0, carrierLevel} Parameter)
    (allowed : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop)
    {Model : (Parameter → ℕ) → Type modelLevel}
    (observe : ∀ sizes, output.Carrier sizes → Model sizes)
    (value : ∀ sizes, {arguments // allowed sizes arguments} → Model sizes)
    (fits : ∀ sizes arguments, ∃ result, observe sizes result = value sizes arguments) :
    Computation Parameter InputName :=
  specification inputs output allowed (fun sizes arguments => Classical.choose (fits sizes arguments))

/-- The public mathematical observation is independent of the witness used to
establish that the answer fits the exact output domain. -/
theorem specificationBy_correct
    (inputs : InputName → EncodedDomain.{0, carrierLevel} Parameter)
    (output : EncodedDomain.{0, carrierLevel} Parameter)
    (allowed : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop)
    {Model : (Parameter → ℕ) → Type modelLevel}
    (observe : ∀ sizes, output.Carrier sizes → Model sizes)
    (value : ∀ sizes, {arguments // allowed sizes arguments} → Model sizes)
    (fits : ∀ sizes arguments, ∃ result, observe sizes result = value sizes arguments)
    (sizes : Parameter → ℕ) (arguments : {arguments // allowed sizes arguments}) :
    observe sizes ((specificationBy inputs output allowed observe value fits).compute sizes arguments) =
      value sizes arguments := by
  have evaluated := specification_compute inputs output allowed
    (fun sizes arguments => Classical.choose (fits sizes arguments)) sizes arguments
  exact (congrArg (observe sizes) evaluated).trans (Classical.choose_spec (fits sizes arguments))

/-- Certify an observed mathematical answer without reconstructing its bounded
carrier. Injectivity makes agreement of observations sufficient for exact
output equality, so the original machine and canonical bits are reused. -/
theorem Realizable.specificationBy
    {inputs : InputName → EncodedDomain.{0, carrierLevel} Parameter}
    {output : EncodedDomain.{0, carrierLevel} Parameter}
    {allowed : ∀ sizes, ((name : InputName) → (inputs name).Carrier sizes) → Prop}
    {implementation : ∀ sizes, {arguments // allowed sizes arguments} → output.Carrier sizes}
    (ready : (Computation.mk inputs output allowed implementation).Realizable)
    {Model : (Parameter → ℕ) → Type modelLevel}
    (observe : ∀ sizes, output.Carrier sizes → Model sizes)
    (value : ∀ sizes, {arguments // allowed sizes arguments} → Model sizes)
    (fits : ∀ sizes arguments, ∃ result, observe sizes result = value sizes arguments)
    (injective : ∀ sizes, Function.Injective (observe sizes))
    (correct : ∀ sizes arguments valid,
      observe sizes (implementation sizes ⟨arguments, valid⟩) = value sizes ⟨arguments, valid⟩) :
    (specificationBy inputs output allowed observe value fits).Realizable := by
  apply ready.specification
  intro sizes arguments valid
  apply injective sizes
  exact (correct sizes arguments valid).trans
    (Classical.choose_spec (fits sizes ⟨arguments, valid⟩)).symm

end Polytime2.Computation
