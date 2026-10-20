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

import Polytime2.Examples.SMP.PreparedOutcome

/-! # Certified prepared consumers at the original SMP dimensions -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation EncodedDomain

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

section Consumer

variable (output : EncodedDomain.{0, 0} (Multisorted.Parameter (Nat.card (SICatalogue L Carrier))))
variable (allowed : ∀ sizes, (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))).Carrier sizes → Prop)
variable (operation : ∀ sizes, {value // allowed sizes value} → output.Carrier sizes)

/-- Consumer results retain actual rejection coordinates or exact sizes and
ordinary mathematical output. -/
noncomputable def consumerDomain (coordinates generators : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (unaryIndex coordinates).sum
    (atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) output)

noncomputable def consumeOutcome (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  sumCases (unaryIndex coordinates)
    (atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)
      (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))))
    (consumerDomain (L := L) (Carrier := Carrier) output coordinates generators)
    (fun _ _ => True)
    (fun sizes frame => allowed
      (computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) sizes frame.1) frame.2)
    (fun _ value => Sum.inl value.val)
    (fun sizes value => Sum.inr
      (((unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))
        output allowed operation).atComputedUnarySizes
          (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)).compute sizes
            ⟨(fun _ => value.val), value.property⟩))

theorem consumeOutcome_realizable
    (consumerReady : (unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))) output allowed operation).Realizable)
    (coordinates generators : MvPolynomial Parameter ℕ) : (consumeOutcome output allowed operation coordinates generators).Realizable := by
  apply sumCases_realizable
  · exact sumInl_realizable _ _
  · exact (consumerReady.atComputedUnarySizes
      (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)).followedBy
        (sumInr_realizable _ _) rfl (by intros; trivial)

/- A consumer may impose any precondition implied by mathematical preparation.
This hypothesis is about its ordinary input, independently of this producer. -/
variable (acceptsPrepared : ∀ sizes value,
  Multisorted.IsPrepared (L := L) (fun sort => catalogueMonolith L Carrier (entry sort))
    (graph (L := L) (Carrier := Carrier)) (Nat.card Carrier * Nat.card Carrier) value.1 value.2 →
      allowed sizes value)

include acceptsPrepared in
theorem prepareConsumerCompatible (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    (consumeOutcome output allowed operation coordinates generators).precondition hostSizes
      (fun _ => (prepare (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
        ⟨arguments, trivial⟩) := by
  change Sum.elim (fun _ => True)
    (fun frame => allowed
      (computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) hostSizes frame.1) frame.2)
    ((prepare (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩)
  rcases prepare_specification coordinates generators hostSizes arguments with rejected | accepted
  · obtain ⟨coordinate, equal, outside, nonmember⟩ := rejected
    rw [equal]
    trivial
  · obtain ⟨frame, equal, counts, prepared, membership⟩ := accepted
    rw [equal]
    exact acceptsPrepared _ frame.2 prepared

/-- Preparation followed by an arbitrary prepared consumer remains a single
computation at the original dimensions, retaining explicit rejection. -/
noncomputable def prepareAndConsume (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (prepare (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (consumeOutcome output allowed operation coordinates generators) rfl (by
      intro sizes arguments valid
      exact prepareConsumerCompatible output allowed operation acceptsPrepared coordinates generators sizes arguments)

/-- The computed-size compiler uses the original-coordinate bounds for every
sort count. Its certificate includes all frame preparation and result transport.
-/
theorem prepareAndConsume_realizable
    (consumerReady : (unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))) output allowed operation).Realizable)
    (coordinates generators : MvPolynomial Parameter ℕ) :
    (prepareAndConsume output allowed operation acceptsPrepared coordinates generators).Realizable :=
  (prepare_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (consumeOutcome_realizable output allowed operation consumerReady coordinates generators) rfl (by
      intro sizes arguments valid
      exact prepareConsumerCompatible output allowed operation acceptsPrepared coordinates generators sizes arguments)

theorem prepareAndConsume_tm0
    (consumerReady : (unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))) output allowed operation).Realizable) :
    (prepareAndConsume output allowed operation acceptsPrepared
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (prepareAndConsume_realizable output allowed operation acceptsPrepared consumerReady _ _).tm0

end Consumer

end Polytime2.SMP.Prepared
