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

import Polytime2.Examples.SMP.CoordinatePreparation
import Polytime2.Examples.SMP.CoordinateReduction
import Polytime2.Computation.PackedArguments
import Polytime2.TM0.Computation

/-! # Polynomial-time conversion of every coordinate to padded SI blocks -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- A column-major input stores a generator column and target at each coordinate.
All capacities depend only on the two declared dimension polynomials. -/
noncomputable def convertAllCoordinates (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := ((coordinateConversion (L := L) (Carrier := Carrier) generators).withPairArgument.inputDomains ()).arrayOfLength coordinates
  outputDomain := (coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain.arrayOfLength coordinates
  precondition _ _ := True
  compute sizes arguments := fun index =>
    (coordinateConversion (L := L) (Carrier := Carrier) generators).withPairArgument.compute sizes
      ⟨(fun _ => arguments.val () index), trivial⟩

/-- The runtime-width array transformer handles the whole instance without a
specialized controller or access to realization witnesses. -/
theorem convertAllCoordinates_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let conversion := (coordinateConversion (L := L) (Carrier := Carrier) generators).withPairArgument
  have step := (coordinateConversion_realizable (L := L) (Carrier := Carrier) generators).withPairArgument
  have normalized := step.withSpecification (fun _ _ => True)
    (fun sizes arguments => conversion.compute sizes ⟨(fun _ => arguments.val ()), trivial⟩)
    (by intros; trivial) (by
      intro sizes arguments valid
      change conversion.compute sizes _ = conversion.compute sizes _
      congr 1)
  exact mapArray_realizable (conversion.inputDomains ()) conversion.outputDomain coordinates
    (fun sizes value => conversion.compute sizes ⟨(fun _ => value), trivial⟩) normalized

/-- A standalone finite TM0 program has just the coordinate and generator
counts as public sizes; preparation, simulation, and extraction are included. -/
theorem conversion_tm0 :
    (convertAllCoordinates (L := L) (Carrier := Carrier)
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) (MvPolynomial.X 1)).TM0Realizable :=
  (convertAllCoordinates_realizable _ _).tm0

/-- The mathematical generator rows of the column-major runtime input. -/
noncomputable def conversionGenerators (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    Fin (MvPolynomial.eval sizes generators) → Fin (MvPolynomial.eval sizes coordinates) → Carrier :=
  fun generator coordinate => (arguments () coordinate).1 generator

/-- Output blocks contain exactly the quotient values of the proved global
subdirect embedding, rather than an unrelated finite-table specification. -/
theorem convertAllCoordinates_generator_blocks
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (generator : Fin (MvPolynomial.eval sizes generators)) :
    ((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ coordinate).2.2 generator =
      some (quotientBlock (CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
        (CoordinateReduction.restricted (L := L) (conversionGenerators coordinates generators sizes arguments) generator coordinate)) :=
  by
    let input := conversionGenerators (L := L) coordinates generators sizes arguments
    change checkedQuotientBlock (CoordinateReduction.images (L := L) input coordinate) (input generator coordinate) = _
    exact checkedQuotientBlock_of_mem _ (CoordinateReduction.restricted (L := L) input generator coordinate)

/-- Selecting any active output slot gives the corresponding generated row of
the mathematical multidomain instance, with its actual catalogue tag. -/
theorem convertAllCoordinates_generator_factor
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (generator : Fin (MvPolynomial.eval sizes generators))
    (factor : CoordinateReduction.FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments)) :
    Option.map (fun block => block (CoordinateReduction.factorEntry _ factor))
      (((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
        ⟨arguments, trivial⟩ factor.1).2.2 generator) =
      some (some ⟨CoordinateReduction.factorEntry _ factor,
        CoordinateReduction.generators (L := L) (conversionGenerators coordinates generators sizes arguments) generator factor⟩) := by
  rw [convertAllCoordinates_generator_blocks]
  exact congrArg some (quotientBlock_entry (CoordinateReduction.factorEntry _ factor) _)

/-- The mathematical target of the column-major runtime input. -/
noncomputable def conversionTarget (coordinates generators : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes) :
    Fin (MvPolynomial.eval sizes coordinates) → Carrier := fun coordinate => (arguments () coordinate).2

/-- Accepted target blocks contain exactly the global embedding's target value. -/
theorem convertAllCoordinates_target_factor
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate)
    (factor : CoordinateReduction.FactorIndex (L := L) (conversionGenerators coordinates generators sizes arguments)) :
    Option.map (fun block => block (CoordinateReduction.factorEntry _ factor))
      (((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
        ⟨arguments, trivial⟩ factor.1).2.1) =
      some (some ⟨CoordinateReduction.factorEntry _ factor,
        CoordinateReduction.target (L := L) (conversionGenerators coordinates generators sizes arguments)
          (conversionTarget coordinates generators sizes arguments) valid factor⟩) := by
  let input := conversionGenerators (L := L) coordinates generators sizes arguments
  let value : CoordinateReduction.images (L := L) input factor.1 :=
    ⟨conversionTarget coordinates generators sizes arguments factor.1, valid factor.1⟩
  change Option.map _ (checkedQuotientBlock (CoordinateReduction.images (L := L) input factor.1) value.val) = _
  rw [checkedQuotientBlock_of_mem]
  exact congrArg some (quotientBlock_entry (CoordinateReduction.factorEntry input factor) value)

/-- The accepted runtime conversion preserves and reflects SMP membership. -/
theorem conversion_membership
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (valid : ∀ coordinate, conversionTarget coordinates generators sizes arguments coordinate ∈
      CoordinateReduction.images (L := L) (conversionGenerators coordinates generators sizes arguments) coordinate) :
    CoordinateReduction.target (L := L) (conversionGenerators coordinates generators sizes arguments)
      (conversionTarget coordinates generators sizes arguments) valid ∈ Substructure.closure L
        (Set.range (CoordinateReduction.generators (L := L) (conversionGenerators coordinates generators sizes arguments))) ↔
      conversionTarget coordinates generators sizes arguments ∈
        Substructure.closure (M := Fin (MvPolynomial.eval sizes coordinates) → Carrier) L
          (Set.range (conversionGenerators coordinates generators sizes arguments)) :=
  CoordinateReduction.membership _ _ valid

/-- Every generator belongs to its generated coordinate image, so converting
input generators never produces the outside-image outcome. -/
theorem convertAllCoordinates_generators_valid
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (generator : Fin (MvPolynomial.eval sizes generators)) :
    (((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ coordinate).2.2 generator) ≠ none := by
  let column : Fin (MvPolynomial.eval sizes generators) → Carrier := (arguments () coordinate).1
  change checkedQuotientBlock (Substructure.closure L (Set.range column)) (column generator) ≠ none
  intro rejected
  exact (checkedQuotientBlock_none _ _).mp rejected
    (Substructure.subset_closure ⟨generator, rfl⟩)

/-- A rejected target block certifies nonmembership in the original generated
relation, independently of the other coordinate outputs. -/
theorem convertAllCoordinates_obstruction
    (coordinates generators : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).Arguments sizes)
    (coordinate : Fin (MvPolynomial.eval sizes coordinates))
    (rejected : ((convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).compute sizes
      ⟨arguments, trivial⟩ coordinate).2.1 = none) :
    (fun index => ((arguments () index).2 : Carrier)) ∉ Substructure.closure (M := Fin (MvPolynomial.eval sizes coordinates) → Carrier) L
      (Set.range (fun generator : Fin (MvPolynomial.eval sizes generators) =>
        fun index => ((arguments () index).1 generator : Carrier))) := by
  apply coordinate_obstruction _ _ coordinate
  exact (checkedQuotientBlock_none _ _).mp rejected

end Polytime2.SMP
