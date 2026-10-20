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

import Polytime2.Examples.SMP.PreparedCoordinates
import Polytime2.Examples.SMP.ConversionData
import Polytime2.Arrays.PackingCount
import Polytime2.Computation.ComputedSizes

/-! # Certified exact sort sizes and original-dimension polynomial bounds

Sort counts are evaluated from coordinate images as proper unary data. The
fixed catalogue sets the number of size fields, while the input sets their
values. Each multiplicity is bounded by the original coordinate count.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]
variable {HostParameter : Type} [Fintype HostParameter]

noncomputable def sizeBounds (coordinates generators : MvPolynomial HostParameter ℕ) :
    Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) → MvPolynomial HostParameter ℕ :=
  Sum.elim (fun _ => coordinates) (fun _ => generators)

omit [Fintype HostParameter] in
theorem sizes_le_bounds (coordinates generators : MvPolynomial HostParameter ℕ) (hostSizes : HostParameter → ℕ)
    (input : Fin (MvPolynomial.eval hostSizes generators) → Fin (MvPolynomial.eval hostSizes coordinates) → Carrier)
    (parameter : Multisorted.Parameter (Nat.card (SICatalogue L Carrier))) :
    sizes (L := L) input parameter ≤ MvPolynomial.eval hostSizes (sizeBounds (L := L) (Carrier := Carrier) coordinates generators parameter) := by
  cases parameter with
  | inl sort => exact sort_size_le (L := L) input sort
  | inr singleton => cases singleton; rfl

omit [Fintype HostParameter] in
/-- Any consumer polynomial at prepared sizes is majorized by a polynomial in
the original dimensions; the catalogue size remains specialization data. -/
theorem consumerPolynomial_bound (coordinates generators : MvPolynomial HostParameter ℕ) (hostSizes : HostParameter → ℕ)
    (input : Fin (MvPolynomial.eval hostSizes generators) → Fin (MvPolynomial.eval hostSizes coordinates) → Carrier)
    (polynomial : MvPolynomial (Multisorted.Parameter (Nat.card (SICatalogue L Carrier))) ℕ) :
    MvPolynomial.eval (sizes (L := L) input) polynomial ≤
      MvPolynomial.eval hostSizes (SizeSubstitution.polynomial
        (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) polynomial) :=
  SizeSubstitution.eval_le _ _ hostSizes _ (sizes_le_bounds coordinates generators hostSizes input)

/-- Evaluate all exact sort multiplicities and retain the generator count. -/
noncomputable def sizeComputation (coordinates generators : MvPolynomial HostParameter ℕ) :
    Computation HostParameter Unit where
  inputDomains _ := (subalgebraDomain L Carrier).constant.arrayOfLength coordinates
  outputDomain := computedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
  precondition _ _ := True
  compute hostSizes arguments parameter :=
    match parameter with
    | .inl sort => (packingCount coordinates).compute hostSizes
        ⟨(fun _ => (catalogueFlags coordinates (entry sort)).compute hostSizes arguments), trivial⟩
    | .inr _ => Fin.last (MvPolynomial.eval hostSizes generators)

theorem sizeComputation_realizable (coordinates generators : MvPolynomial HostParameter ℕ) :
    (sizeComputation (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  classical
  let computation := sizeComputation (L := L) (Carrier := Carrier) coordinates generators
  let bounds := sizeBounds (L := L) (Carrier := Carrier) coordinates generators
  let names := Multisorted.Parameter (Nat.card (SICatalogue L Carrier))
  have fieldReady parameter : (Computation.mk computation.inputDomains (EncodedDomain.boundedUnary (bounds parameter))
      computation.precondition (fun hostSizes arguments => computation.compute hostSizes arguments parameter)).Realizable := by
    cases parameter with
    | inl sort =>
      exact (catalogueFlags_realizable coordinates (entry sort)).followedBy
        (packingCount_realizable coordinates) rfl (by intros; trivial)
    | inr singleton =>
      cases singleton
      exact (polynomialUnarySize_realizable generators).onResults computation.inputDomains computation.precondition
        (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  let enumeration := Fintype.equivFin names
  have fields := Realizable.recordOutputs computation.inputDomains (Fintype.card names)
    (fun position => EncodedDomain.boundedUnary (bounds (enumeration.symm position))) computation.precondition
    (fun position hostSizes arguments => computation.compute hostSizes arguments (enumeration.symm position))
    (fun position => fieldReady (enumeration.symm position))
  exact fields.withEncodedOutput computation.outputDomain computation.compute (fun _ => rfl) (by intros; rfl)

/-- On the actual generated coordinate images, the certified sizes are exactly
the mathematical dimensions used by the exact multisorted product. -/
theorem sizeComputation_exact (coordinates generators : MvPolynomial HostParameter ℕ) (hostSizes : HostParameter → ℕ)
    (input : Fin (MvPolynomial.eval hostSizes generators) → Fin (MvPolynomial.eval hostSizes coordinates) → Carrier) :
    computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) hostSizes
      ((sizeComputation (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
        ⟨(fun _ => images (L := L) input), trivial⟩) = sizes (L := L) input := by
  funext parameter
  cases parameter with
  | inl sort => rfl
  | inr singleton => cases singleton; rfl

end Polytime2.SMP.Prepared
