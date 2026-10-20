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

/-- Results preserve the rejection alternative; accepted results retain the
same exact size assignment together with the consumer's own mathematical data. -/
noncomputable def consumerAlternatives (coordinates generators : MvPolynomial Parameter ℕ) : Fin 2 → EncodedDomain Parameter :=
  ![boundedUnary coordinates,
    atComputedSizeDomain (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) output]

noncomputable def consumerPreconditions (coordinates generators : MvPolynomial Parameter ℕ) :
    ∀ index sizes, (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators index).Carrier sizes → Prop := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact fun _ _ => True
  · intro remaining
    refine Fin.cases ?_ ?_ remaining
    · exact fun sizes frame => allowed
        (computedSizeAssignment (sizeBounds (L := L) (Carrier := Carrier) coordinates generators) sizes frame.1) frame.2
    · intro impossible
      exact Fin.elim0 impossible

noncomputable def consumerBranches (coordinates generators : MvPolynomial Parameter ℕ) :
    ∀ index sizes, {value // consumerPreconditions allowed coordinates generators index sizes value} →
      (variant 2 (consumerAlternatives (L := L) (Carrier := Carrier) output coordinates generators)).Carrier sizes := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact fun _ value => ⟨0, value.val⟩
  · intro remaining
    refine Fin.cases ?_ ?_ remaining
    · exact fun sizes value => ⟨1, ((unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier)))
        output allowed operation).atComputedUnarySizes (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)).compute sizes
          ⟨(fun _ => value.val), value.property⟩⟩
    · intro impossible
      exact Fin.elim0 impossible

noncomputable def consumeOutcome (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  variantCases 2 (preparationAlternatives (L := L) (Carrier := Carrier) coordinates generators)
    (variant 2 (consumerAlternatives (L := L) (Carrier := Carrier) output coordinates generators))
    (consumerPreconditions allowed coordinates generators) (consumerBranches output allowed operation coordinates generators)

theorem consumeOutcome_realizable
    (consumerReady : (unaryMap (Multisorted.preparedDomain (enumeration (L := L) (Carrier := Carrier))) output allowed operation).Realizable)
    (coordinates generators : MvPolynomial Parameter ℕ) : (consumeOutcome output allowed operation coordinates generators).Realizable := by
  apply variantCases_realizable
  intro index
  fin_cases index
  · exact variantInjection_realizable 2 (consumerAlternatives (L := L) (Carrier := Carrier) output coordinates generators) 0
  · exact (consumerReady.atComputedUnarySizes
      (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)).followedBy
        (variantInjection_realizable 2 (consumerAlternatives (L := L) (Carrier := Carrier) output coordinates generators) 1)
        rfl (by intros; trivial)

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
  change consumerPreconditions allowed coordinates generators
    ((prepare (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩).1
    hostSizes ((prepare (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes ⟨arguments, trivial⟩).2
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
