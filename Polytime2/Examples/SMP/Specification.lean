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

import Polytime2.Examples.SMP.Rejection
import Polytime2.Examples.SMP.DistinctDependencies
import Polytime2.Examples.SMP.MonolithOperations

/-! # Public correctness contract for SMP monolith preparation

The catalogue, quotient maps, monoliths, and dependency maps are fixed
specialization lookups. Runtime output stores ordered padded values, exact
sort counts, and an explicit rejected-coordinate index or accepted sentinel.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open CoordinateReduction

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier : Type}
variable [L.Structure Carrier] [Finite Carrier]

/-- The structural guarantees of the prepared heterogeneous generated relation.
This proposition reuses the actual mathematical factors and maps, without a
second representation of algebras, homomorphisms, or certificates. -/
noncomputable def IsMonolithPrepared {count : ℕ} {Generator : Type}
    (input : Generator → Fin count → Carrier) : Prop :=
  Function.Injective (embedding (L := L) input) ∧
  IsSubdirect (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor (L := L) input factor)) ∧
  (∀ factor : FactorIndex (L := L) input, IsSubdirectlyIrreducible L (Factor (L := L) input factor)) ∧
  Nonempty (Substructure.closure L (Set.range input) ≃[L]
    Substructure.closure L (Set.range (generators (L := L) input))) ∧
  Nat.card (FactorIndex (L := L) input) ≤ count * Nat.card (SICatalogue L Carrier) ∧
  ∀ factor : FactorIndex (L := L) input,
    IsLeast {relation : Congruence L (SICarrier L Carrier (factorEntry input factor)) | relation.val ≠ ⊥}
      (catalogueMonolith L Carrier (factorEntry input factor)) ∧
    (Nat.card (Congruence L (Factor (L := L) input factor)) = 2 → dependencySet input factor = ∅) ∧
    Nonempty (Quotient (catalogueMonolith L Carrier (factorEntry input factor)).val ≃[L]
      projectedDependencies input factor) ∧
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      ((fun dependency : dependencySet input factor => tuple dependency.val), tuple factor)) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor (L := L) input factor)) =
      {tuple | tuple.1 = (projectedMonolithEquiv input factor
        (quotientMap (catalogueMonolith L Carrier (factorEntry input factor)) tuple.2) :
          ∀ dependency : dependencySet input factor, Factor (L := L) input dependency.val)} ∧
    (fun tuple : (∀ factor, Factor (L := L) input factor) =>
      fun dependency : dependencySet input factor => tuple dependency.val) ''
        (Substructure.closure L (Set.range (generators (L := L) input)) : Set (∀ factor, Factor (L := L) input factor)) =
      Set.range (distinctMonolithPrefix input factor) ∧
    Nat.card (dependencySet input factor) ≤ Nat.card Carrier * Nat.card Carrier ∧
    ∀ dependency : dependencySet input factor, factorKey input dependency.val < factorKey input factor

theorem isMonolithPrepared {count : ℕ} {Generator : Type} (input : Generator → Fin count → Carrier) :
    IsMonolithPrepared (L := L) input := by
  refine ⟨embedding_injective input, generators_subdirect input, factors_si input,
    ⟨reductionEquiv input⟩, factor_count_bound input, ?_⟩
  intro factor
  exact ⟨catalogueMonolith_least L Carrier (factorEntry input factor), simple_dependencySet_empty input factor,
    ⟨projectedMonolithEquiv input factor⟩, distinct_dependency_graph input factor,
    distinct_dependency_prefix input factor, dependencySet_bound input factor, dependencySet_earlier input factor⟩

variable {Parameter : Type} [Fintype Parameter]

/-- A result is either an explicit coordinate-image obstruction or an accepted
monolith-prepared instance preserving the original membership question. -/
noncomputable def PreparationOutcome (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (output : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).outputDomain.Carrier sizes) : Prop :=
    let input := conversionGenerators (L := L) coordinates generators sizes arguments
    let target := conversionTarget coordinates generators sizes arguments
    (∃ coordinate : Fin (MvPolynomial.eval sizes coordinates), output.2.toNat = coordinate.val ∧
      target coordinate ∉ images (L := L) input coordinate ∧ target ∉ Substructure.closure L (Set.range input)) ∨
    (output.2.toNat = MvPolynomial.eval sizes coordinates ∧
      ∃ valid : ∀ coordinate, target coordinate ∈ images (L := L) input coordinate,
        IsMonolithPrepared (L := L) input ∧
        (CoordinateReduction.target (L := L) input target valid ∈ Substructure.closure L
          (Set.range (CoordinateReduction.generators (L := L) input)) ↔
            target ∈ Substructure.closure L (Set.range input)) ∧
        (∑ rank : Fin (Nat.card (SICatalogue L Carrier)), (output.1.2.2 rank).toNat) =
          Nat.card (FactorIndex (L := L) input))

theorem conversionResult_outcome (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    PreparationOutcome coordinates generators sizes arguments
      ((conversionResult (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩) := by
  dsimp only [PreparationOutcome]
  rw [conversionResult_compute]
  let selected := (rejectionCoordinate (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩
  by_cases before : selected.toNat < MvPolynomial.eval sizes coordinates
  · left
    obtain ⟨coordinate, equal, outside⟩ := rejectionCoordinate_witness coordinates generators sizes arguments before
    exact ⟨coordinate, equal.symm, outside, rejectionCoordinate_found coordinates generators sizes arguments before⟩
  · right
    have sentinel : selected.toNat = MvPolynomial.eval sizes coordinates :=
      le_antisymm (rejectionCoordinate_bound coordinates generators sizes arguments) (Nat.le_of_not_gt before)
    have valid := (rejectionCoordinate_sentinel coordinates generators sizes arguments).mp sentinel
    exact ⟨sentinel, valid, isMonolithPrepared _, conversion_membership coordinates generators sizes arguments valid,
      orderedConversion_total_count coordinates generators sizes arguments⟩

/-- The accepted output contains exactly the transformed generators and target,
with precisely the active slots and exact per-sort counts used by the contract. -/
noncomputable def PreparedDataAgrees (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
    (output : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).outputDomain.Carrier sizes) : Prop :=
    let input := conversionGenerators (L := L) coordinates generators sizes arguments
    let target := conversionTarget coordinates generators sizes arguments
    (∀ generator (factor : FactorIndex (L := L) input),
      ((output.1.2.1 (catalogueRank (factorEntry input factor)) factor.1).2 generator) =
        some ⟨factorEntry input factor, CoordinateReduction.generators (L := L) input generator factor⟩) ∧
    (∀ factor : FactorIndex (L := L) input,
      (output.1.2.1 (catalogueRank (factorEntry input factor)) factor.1).1 =
        some ⟨factorEntry input factor, CoordinateReduction.target (L := L) input target valid factor⟩) ∧
    (∀ rank coordinate, (output.1.2.1 rank coordinate).1.isSome = true ↔
      images (L := L) input coordinate = ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) ∧
    (∀ rank, (output.1.2.2 rank).toNat =
      Nat.card {coordinate : Fin (MvPolynomial.eval sizes coordinates) //
        images (L := L) input coordinate = ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1})

theorem conversionResult_agrees (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate) :
    PreparedDataAgrees coordinates generators sizes arguments valid
      ((conversionResult (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩) := by
  dsimp only [PreparedDataAgrees]
  rw [conversionResult_compute]
  refine ⟨orderedConversion_generator coordinates generators sizes arguments,
    orderedConversion_target coordinates generators sizes arguments valid,
    orderedConversion_active coordinates generators sizes arguments valid, ?_⟩
  intro rank
  rw [orderedConversion_count, Computation.count_flags_card]
  simp only [decide_eq_true_eq]

/-- Dense sort-local positions have exactly the ranges recorded in the actual
output counts; these counts are data, not additional size parameters. -/
noncomputable def conversionResult_denseCorrespondence
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (conversionResult (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate) :
    FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments) ≃
      Σ rank : Fin (Nat.card (SICatalogue L Carrier)),
        Fin ((((conversionResult (L := L) (Carrier := Carrier) coordinates generators).compute sizes
          ⟨arguments, trivial⟩).1.2.2 rank).toNat) :=
  (denseSlotEquiv (conversionGenerators coordinates generators sizes arguments)).trans
    (Equiv.sigmaCongrRight (fun rank => finCongr
      ((conversionResult_agrees coordinates generators sizes arguments valid).2.2.2 rank).symm))

/-- The implementation and its structural and output contracts share one public
computation; standalone TM0 export includes all input and output handling. -/
theorem conversionResult_polynomial_time :
    (conversionResult (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).Realizable ∧
    (conversionResult (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  ⟨conversionResult_realizable _ _, conversionResult_tm0⟩

end Polytime2.SMP
