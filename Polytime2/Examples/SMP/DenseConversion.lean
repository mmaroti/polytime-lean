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

import Polytime2.Examples.SMP.Specification
import Polytime2.Examples.SMP.Positions

/-! # Returning certified dense position tables with the prepared SMP data -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Organize converted records and build positions from the same stored images. -/
noncomputable def organizeDense (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := (collectRejection (L := L) (Carrier := Carrier) coordinates generators).outputDomain.prod
    (convertedPositionTables (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  precondition _ _ := True
  compute sizes arguments :=
    ((collectRejection (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨(fun _ => (organizeConversion coordinates generators).compute sizes ⟨arguments.val, trivial⟩), trivial⟩,
      (convertedPositionTables (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments.val, trivial⟩)

theorem organizeDense_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (organizeDense (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  have core := (organizeConversion_realizable (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (collectRejection_realizable coordinates generators) rfl (by intros; trivial)
  exact Realizable.pairOutputs _ _ _ (fun _ _ => True) _ _ core
    (convertedPositionTables_realizable coordinates generators)

/-- Closure computation is performed once; the output retains all previous
prepared data and the polynomial-capacity runtime position tables. -/
noncomputable def denseConversion (coordinates generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).followedBy
    (organizeDense coordinates generators) rfl (by intros; trivial)

theorem denseConversion_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  (convertAllCoordinates_realizable coordinates generators).followedBy
    (organizeDense_realizable coordinates generators) rfl (by intros; trivial)

/-- Adding position tables preserves the complete previously proved result. -/
theorem denseConversion_core (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    ((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩).1 =
      (conversionResult (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩ := by
  rfl

/-- Each stored position is the exact number of earlier coordinates of its sort. -/
theorem denseConversion_position (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (rank : Fin (Nat.card (SICatalogue L Carrier))) (coordinate : Fin (MvPolynomial.eval sizes coordinates)) :
    ((((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2 rank) coordinate).toNat =
      ((List.ofFn (fun index => @decide
        (CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) index =
          ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) (Classical.propDecidable _))).take coordinate.val).count true :=
  cataloguePositions_correct coordinates (catalogueRank.symm rank) sizes _ coordinate

/-- Runtime position entries equal the canonical dense order indices. -/
theorem denseConversion_position_dense (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (rank : Fin (Nat.card (SICatalogue L Carrier))) (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (active : CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate =
      ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) :
    ((((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2 rank) coordinate).toNat =
      (CoordinateReduction.denseSortEquiv (conversionGenerators coordinates generators sizes arguments)
        (catalogueRank.symm rank) ⟨coordinate, active⟩).val := by
  classical
  rw [denseConversion_position]
  let input := conversionGenerators (L := L) coordinates generators sizes arguments
  let entry : SICatalogue L Carrier := catalogueRank.symm rank
  let flags : Fin (MvPolynomial.eval sizes coordinates) → Bool := fun index =>
    decide (CoordinateReduction.images (L := L) input index = entry.1)
  let correspondence : {index : Fin (MvPolynomial.eval sizes coordinates) // flags index = true} ≃o
      {index : Fin (MvPolynomial.eval sizes coordinates) // CoordinateReduction.images (L := L) input index = entry.1} :=
    { toEquiv := Equiv.subtypeEquiv (Equiv.refl _) (by intro index; simp [flags])
      map_rel_iff' := by intros; rfl }
  exact prefix_count_orderIndex flags ⟨coordinate, by simpa [flags] using active⟩
    (correspondence.trans (CoordinateReduction.denseSortEquiv input entry))

/-- Active positions fit the actual stored sort count, rather than merely the
polynomial output capacity. -/
theorem denseConversion_position_lt (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
    (rank : Fin (Nat.card (SICatalogue L Carrier))) (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (active : CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate =
      ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) :
    ((((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩).2 rank) coordinate).toNat <
      (((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes
        ⟨arguments, trivial⟩).1.1.2.2 rank).toNat := by
  rw [denseConversion_position_dense coordinates generators sizes arguments rank coordinate active, denseConversion_core]
  rw [(conversionResult_agrees coordinates generators sizes arguments valid).2.2.2 rank]
  exact (CoordinateReduction.denseSortEquiv (conversionGenerators coordinates generators sizes arguments)
    (catalogueRank.symm rank) ⟨coordinate, active⟩).isLt

/-- The final contract ties the structural outcome and every stored data field to
the mathematical instance, including the runtime dense-position correspondence. -/
noncomputable def DenseOutputCorrect (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (output : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).outputDomain.Carrier sizes) : Prop :=
  PreparationOutcome coordinates generators sizes arguments output.1 ∧
  (∀ valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate,
    PreparedDataAgrees coordinates generators sizes arguments valid output.1) ∧
  Monotone (fun rank : Fin (Nat.card (SICatalogue L Carrier)) =>
    Nat.card (Congruence L (SICarrier L Carrier (catalogueRank.symm rank)))) ∧
  ∀ rank coordinate,
    (output.2 rank coordinate).toNat =
      ((List.ofFn (fun index => @decide
        (CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) index =
          ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1) (Classical.propDecidable _))).take coordinate.val).count true ∧
    ∀ active : CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate =
        ((catalogueRank (L := L) (Carrier := Carrier)).symm rank).1,
      (output.2 rank coordinate).toNat =
        (CoordinateReduction.denseSortEquiv (conversionGenerators coordinates generators sizes arguments)
          (catalogueRank.symm rank) ⟨coordinate, active⟩).val

theorem denseConversion_correct (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (denseConversion (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    DenseOutputCorrect coordinates generators sizes arguments
      ((denseConversion (L := L) (Carrier := Carrier) coordinates generators).compute sizes ⟨arguments, trivial⟩) := by
  unfold DenseOutputCorrect
  rw [denseConversion_core]
  refine ⟨conversionResult_outcome coordinates generators sizes arguments,
    (fun valid => conversionResult_agrees coordinates generators sizes arguments valid), catalogue_order_monotone, ?_⟩
  intro rank coordinate
  exact ⟨denseConversion_position coordinates generators sizes arguments rank coordinate,
    denseConversion_position_dense coordinates generators sizes arguments rank coordinate⟩

theorem denseConversion_tm0 :
    (denseConversion (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (denseConversion_realizable _ _).tm0

/-- For each finite specialized algebra, one finite algorithm implements the full
conversion in polynomial time in exactly the coordinate and generator counts. -/
theorem denseConversion_implements :
    let computation := denseConversion (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)
    computation.Realizable ∧ computation.TM0Realizable ∧
      ∀ sizes (arguments : computation.Arguments sizes),
        DenseOutputCorrect (MvPolynomial.X 0) (MvPolynomial.X 1) sizes arguments
          (computation.compute sizes ⟨arguments, trivial⟩) :=
  ⟨denseConversion_realizable _ _, denseConversion_tm0, denseConversion_correct _ _⟩

end Polytime2.SMP
