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

import Polytime2.Examples.SMP.Conversion

/-! # Internal coordinate views for exact-size SMP preparation

All views share the already computed coordinate images and quotient blocks.
No padded public SMP result, binary count record, or dense adapter is exported.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic] {Carrier Parameter : Type}
variable [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- One sort is active exactly at coordinates having its source image algebra. -/
noncomputable def catalogueFlags (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    Computation Parameter Unit where
  inputDomains _ := (subalgebraDomain L Carrier).constant.arrayOfLength length
  outputDomain := EncodedDomain.booleans.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := fun index => @decide ((arguments.val () index : L.Substructure Carrier) = entry.1)
    (Classical.propDecidable _)

theorem catalogueFlags_realizable (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    (catalogueFlags length entry).Realizable := by
  classical
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let predicate := fun (value : (subalgebraDomain L Carrier).Carrier Empty.elim) =>
    decide ((value : L.Substructure Carrier) = entry.1)
  have predicateRealizable := (finitePredicate_realizable (subalgebraDomain L Carrier) predicate).withConstantSizes
    (Parameter := Parameter)
  have booleanResult := predicateRealizable.reinterpretOutput EncodedDomain.booleans
    (fun _ value => value)
    (by intros; simp [finitePredicate, finiteOperation, Computation.withConstantSizes,
      EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.constant])
    (by
      intro sizes value
      simp only [finitePredicate, finiteOperation, Computation.withConstantSizes,
        EncodedDomain.booleans, EncodedDomain.constant_encode_bits,
        EncodedDomain.fixed_encode_bits])
  exact mapArray_realizable image EncodedDomain.booleans length
    (fun _ value => decide ((value : L.Substructure Carrier) = entry.1)) booleanResult

/-- Read image algebras from the already converted coordinate records. -/
noncomputable def convertedImages (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := (convertAllCoordinates (L := L) (Carrier := Carrier) coordinates generators).outputDomain
  outputDomain := (subalgebraDomain L Carrier).constant.arrayOfLength coordinates
  precondition _ _ := True
  compute _ arguments := fun index => (arguments.val () index).1

theorem convertedImages_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (convertedImages (L := L) (Carrier := Carrier) coordinates generators).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let slot : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let payload := slot.prod (slot.arrayOfLength generators)
  exact mapArray_realizable (image.prod payload) image coordinates (fun _ value => value.1)
    (pairProjection_realizable image payload false)

/-- A fixed mathematical operation maps a coordinate's target and generator
blocks together. The source image and all runtime lengths remain unchanged. -/
noncomputable def coordinateBlockMap (generators : MvPolynomial Parameter ℕ)
    (target : EncodedDomain.{0, 0} Empty)
    (operation : Option (SIBlock L Carrier) → target.Carrier Empty.elim) : Computation Parameter Unit where
  inputDomains _ := (coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain
  outputDomain := target.constant.prod (target.constant.arrayOfLength generators)
  precondition _ _ := True
  compute _ arguments := (operation (arguments.val ()).2.1,
    fun generator => operation ((arguments.val ()).2.2 generator))

theorem coordinateBlockMap_realizable (generators : MvPolynomial Parameter ℕ)
    (target : EncodedDomain.{0, 0} Empty)
    (operation : Option (SIBlock L Carrier) → target.Carrier Empty.elim) :
    (coordinateBlockMap generators target operation).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let block : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let payload := block.prod (block.arrayOfLength generators)
  have mapped := (finiteOperation_realizable (fun _ : Unit => elementDomain (Option (SIBlock L Carrier)))
    target (fun values => operation (values ()))).withConstantSizes (Parameter := Parameter)
  have first := ((pairProjection_realizable image payload true).fst).followedBy
      mapped rfl (by intros; trivial)
  have columns := ((pairProjection_realizable image payload true).snd).followedBy
      (mapArray_realizable block target.constant generators (fun _ value => operation value) mapped)
      rfl (by intros; trivial)
  exact first.prodMk columns

/-- Acceptance remains explicit even when an image has no nontrivial SI sort. -/
noncomputable def coordinateAccepted (generators : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (coordinateConversion (L := L) (Carrier := Carrier) generators).outputDomain
  outputDomain := EncodedDomain.booleans.constant
  precondition _ _ := True
  compute _ arguments := (arguments.val ()).2.1.isSome

theorem coordinateAccepted_realizable (generators : MvPolynomial Parameter ℕ) :
    (coordinateAccepted (L := L) (Carrier := Carrier) generators).Realizable := by
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let block : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let payload := block.prod (block.arrayOfLength generators)
  exact ((pairProjection_realizable image payload true).fst).followedBy ((finitePredicate_realizable (elementDomain (Option (SIBlock L Carrier)))
    (fun value => value.isSome)).withConstantSizes (Parameter := Parameter)) rfl (by intros; trivial)

/-- Keep one target-acceptance bit per original coordinate. -/
noncomputable def conversionAcceptance (coordinates generators : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  mapArray ((coordinateAccepted (L := L) (Carrier := Carrier) generators).inputDomains ())
    EncodedDomain.booleans.constant coordinates
    (fun sizes value => (coordinateAccepted (L := L) (Carrier := Carrier) generators).compute sizes
      ⟨(fun _ => value), trivial⟩)

theorem conversionAcceptance_realizable (coordinates generators : MvPolynomial Parameter ℕ) :
    (conversionAcceptance (L := L) (Carrier := Carrier) coordinates generators).Realizable :=
  mapArray_realizable _ _ _ _ (coordinateAccepted_realizable generators)

end Polytime2.SMP
