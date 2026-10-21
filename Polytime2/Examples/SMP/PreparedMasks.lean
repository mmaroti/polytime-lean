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

import Polytime2.Examples.SMP.PreparedFrame
import Polytime2.Examples.SMP.PreparedDependencies
import Polytime2.Arrays.ProductMap
import Polytime2.Arithmetic.BitComparison

/-! # Certified dependency masks from packed source coordinates -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP.Prepared

open FirstOrder FirstOrder.Language CoordinateReduction
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

abbrev WorkParameter := Parameter ⊕ Multisorted.Parameter (Nat.card (SICatalogue L Carrier))

/-- Compare source labels and apply the specialization's fixed dependency-sort
lookup. There is no runtime algebra or catalogue search. -/
noncomputable def labelComparison (coordinates : MvPolynomial Parameter ℕ)
    (parent child : SortIndex (L := L) (Carrier := Carrier)) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Bool :=
  (bitsEqualAtNames (coordinates + 1)
    (Sum.inl : Parameter → WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))).followedBy
      (booleanOperation (fun flags : Unit → Bool =>
        @decide (entry child ∈ dependencySorts (entry parent)) (Classical.propDecidable _) && flags ()))
      rfl (by intros; trivial)

theorem labelComparison_realizable (coordinates : MvPolynomial Parameter ℕ)
    (parent child : SortIndex (L := L) (Carrier := Carrier)) :
    (labelComparison coordinates parent child).Realizable :=
  (bitsEqualAtNames_realizable _ _).followedBy (booleanOperation_realizable _) rfl (by intros; trivial)

/-- The rectangular dependency block for one fixed pair of sorts. Counts are
read from the shared frame; only the actual source-label arrays are compared. -/
noncomputable def dependencyMatrix (coordinates generators : MvPolynomial Parameter ℕ)
    (parent child : SortIndex (L := L) (Carrier := Carrier)) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Unit :=
  (arrayProductMap
    ((EncodedDomain.bitVectors (coordinates + 1)).renameParameters
      (Sum.inl : Parameter → WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)))
    EncodedDomain.booleans (.inr (.inl parent)) (.inr (.inl child))
    (fun current first second => (labelComparison coordinates parent child).compute current
      ⟨(fun choice => if choice then second else first), trivial⟩)).onResults
      (fun _ => (packedDomain (L := L) (Carrier := Carrier) coordinates generators).renameParameters Sum.inl)
      (fun current arguments => (arguments () parent).2.1.val = current (.inr (.inl parent)) ∧
        (arguments () child).2.1.val = current (.inr (.inl child)))
      (fun choice current arguments => match choice with
      | false => (readPackedSources coordinates generators parent).compute current
          ⟨arguments.val, arguments.property.1⟩
      | true => (readPackedSources coordinates generators child).compute current
          ⟨arguments.val, arguments.property.2⟩)
      (by intros; trivial)

theorem dependencyMatrix_realizable (coordinates generators : MvPolynomial Parameter ℕ)
    (parent child : SortIndex (L := L) (Carrier := Carrier)) :
    (dependencyMatrix coordinates generators parent child).Realizable := by
  let labels := (EncodedDomain.bitVectors (coordinates + 1)).renameParameters
    (Sum.inl : Parameter → WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  let comparison := labelComparison coordinates parent child
  have step := (labelComparison_realizable coordinates parent child).withSpecification (fun _ _ => True)
    (fun current arguments => comparison.compute current
      ⟨(fun choice => if choice then arguments.val true else arguments.val false), trivial⟩)
    (by intros; trivial) (by intros; rfl)
  apply (arrayProductMap_realizable labels EncodedDomain.booleans (.inr (.inl parent)) (.inr (.inl child))
    (fun current first second => comparison.compute current
      ⟨(fun choice => if choice then second else first), trivial⟩) step).onResults
  intro choice
  cases choice
  · exact (readPackedSources_realizable coordinates generators parent).withSpecification _ _
      (by intro current arguments valid; exact valid.1) (by intros; rfl)
  · exact (readPackedSources_realizable coordinates generators child).withSpecification _ _
      (by intro current arguments valid; exact valid.2) (by intros; rfl)

/-- Every runtime block is the exact mathematical dependency relation. The
source labels used by the machine are the same stable selection as the values. -/
theorem dependencyMatrix_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes)
    (parent child : SortIndex (L := L) (Carrier := Carrier))
    (parentPosition : Fin (sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl parent)))
    (childPosition : Fin (sizes (L := L) (conversionGenerators coordinates generators hostSizes arguments) (.inl child))) :
    let frame := (packedFrame (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩
    let current := computedSizeAssignment
      (extendedSizeBounds (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)) hostSizes frame.1
    (dependencyMatrix coordinates generators parent child).compute current
      ⟨(fun _ => frame.2), ⟨rfl, rfl⟩⟩ parentPosition childPosition =
        Multisorted.DependencyEncoding.equivalence _
          (dependencies (L := L) (conversionGenerators coordinates generators hostSizes arguments))
          parent parentPosition child childPosition := by
  let converted := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
    hostSizes ⟨arguments, trivial⟩
  let first := ((packSources coordinates generators (entry parent)).compute hostSizes
    ⟨(fun _ => converted), trivial⟩).2 parentPosition
  let second := ((packSources coordinates generators (entry child)).compute hostSizes
    ⟨(fun _ => converted), trivial⟩).2 childPosition
  have firstCorrect := packSources_correct coordinates generators hostSizes arguments parent parentPosition
  have secondCorrect := packSources_correct coordinates generators hostSizes arguments child childPosition
  rw [dependencies_lookup]
  apply Bool.eq_iff_iff.mpr
  change (@decide (entry child ∈ dependencySorts (entry parent)) (Classical.propDecidable _) &&
      decide (first = second)) = true ↔ _
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← BitVec.toNat_inj, Fin.ext_iff]
  rw [show first.toNat = _ from firstCorrect, show second.toNat = _ from secondCorrect]
  constructor
  · rintro ⟨member, equal⟩
    exact ⟨equal.symm, member⟩
  · rintro ⟨equal, member⟩
    exact ⟨member, equal.symm⟩

/-- Assemble every rectangular block into the one public dependency-mask
domain. All original source labels remain private conversion data. -/
private noncomputable def dependencyMasksRaw (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) Unit where
  inputDomains _ := (packedDomain (L := L) (Carrier := Carrier) coordinates generators).renameParameters Sum.inl
  outputDomain := (Multisorted.DependencyEncoding.maskDomain (Nat.card (SICatalogue L Carrier))).renameParameters
    (Sum.inr : Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) →
      WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter))
  precondition current arguments := ∀ sort, (arguments () sort).2.1.val = current (.inr (.inl sort))
  compute current arguments := fun parent position child childPosition =>
    (dependencyMatrix coordinates generators parent child).compute current
      ⟨arguments.val, ⟨arguments.property parent, arguments.property child⟩⟩ position childPosition

private theorem dependencyMasksRaw_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (dependencyMasksRaw (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let computation := dependencyMasksRaw (L := L) (Carrier := Carrier) coordinates generators
  let sorts := SortIndex (L := L) (Carrier := Carrier)
  let matrix (parent child : sorts) : EncodedDomain
      (WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)) :=
    (EncodedDomain.booleans.array (.inr (.inl child))).array (.inr (.inl parent))
  have blockReady parent child : (Computation.mk computation.inputDomains (matrix parent child)
      computation.precondition (fun current arguments =>
        (dependencyMatrix coordinates generators parent child).compute current
          ⟨arguments.val, ⟨arguments.property parent, arguments.property child⟩⟩)).Realizable :=
    (dependencyMatrix_realizable coordinates generators parent child).withSpecification _ _
      (by intro current arguments valid; exact ⟨valid parent, valid child⟩) (by intros; rfl)
  have rowReady parent := Realizable.recordOutputs computation.inputDomains (Nat.card (SICatalogue L Carrier))
    (matrix parent) computation.precondition
    (fun child current arguments position childPosition => computation.compute current arguments parent position child childPosition)
    (blockReady parent)
  have blocks := Realizable.recordOutputs computation.inputDomains (Nat.card (SICatalogue L Carrier))
    (fun parent => EncodedDomain.record (Nat.card (SICatalogue L Carrier)) (matrix parent))
    computation.precondition
    (fun parent current arguments child position childPosition => computation.compute current arguments parent position child childPosition)
    rowReady
  apply blocks.reinterpretOutput computation.outputDomain
    (fun _ blocks parent position child childPosition => blocks parent child position childPosition)
  · intro current
    simp only [computation, dependencyMasksRaw, EncodedDomain.renameParameters_width,
      EncodedDomain.width, Multisorted.DependencyEncoding.maskDomain]
    rw [EncodedDomain.reindex_widthPolynomial]
    simp [matrix, EncodedDomain.booleans, Function.comp_def]
  · intro current value
    simp only [computation, dependencyMasksRaw, EncodedDomain.renameParameters_bits, Multisorted.DependencyEncoding.maskDomain]
    rw [EncodedDomain.reindex_encode_bits]
    simp only [EncodedDomain.bits_record_encode, matrix, EncodedDomain.array_encode_bits,
      EncodedDomain.ArrayEncoding.bits_encode, EncodedDomain.booleans, EncodedDomain.fixed_encode_bits]
    rfl

/-- Dependency sets are exposed through the same characteristic-bit encoding. -/
noncomputable def dependencySets (coordinates generators : MvPolynomial Parameter ℕ) :=
  (dependencyMasksRaw (L := L) (Carrier := Carrier) coordinates generators).reindexDomains
    (dependencyMasksRaw (L := L) (Carrier := Carrier) coordinates generators).inputDomains
    ((Multisorted.dependencyDomain (Nat.card (SICatalogue L Carrier))).renameParameters
      (Sum.inr : Multisorted.Parameter (Nat.card (SICatalogue L Carrier)) →
        WorkParameter (L := L) (Carrier := Carrier) (Parameter := Parameter)))
    (fun _ _ => Equiv.refl _) (fun _ => Multisorted.DependencyEncoding.equivalence _)

theorem dependencySets_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (dependencySets (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (dependencyMasksRaw_realizable coordinates generators).reindexDomains _ _ _ _
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; rfl)

/-- The assembled runtime masks are the complete dependency data of the exact
multisorted mathematical preparation. -/
theorem dependencySets_correct (coordinates generators : MvPolynomial Parameter ℕ)
    (hostSizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments hostSizes) :
    let frame := (packedFrame (L := L) (Carrier := Carrier) coordinates generators).compute hostSizes
      ⟨(fun _ => (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute
        hostSizes ⟨arguments, trivial⟩), trivial⟩
    let current := computedSizeAssignment
      (extendedSizeBounds (sizeBounds (L := L) (Carrier := Carrier) coordinates generators)) hostSizes frame.1
    (dependencySets (L := L) (Carrier := Carrier) coordinates generators).compute current
      ⟨(fun _ => frame.2), (by intro sort; rfl)⟩ =
        dependencies (L := L) (conversionGenerators coordinates generators hostSizes arguments) := by
  apply (Multisorted.DependencyEncoding.equivalence _).injective
  change Multisorted.DependencyEncoding.equivalence _
    ((Multisorted.DependencyEncoding.equivalence _).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext parent position child childPosition
  exact dependencyMatrix_correct coordinates generators hostSizes arguments parent child position childPosition

end Polytime2.SMP.Prepared
