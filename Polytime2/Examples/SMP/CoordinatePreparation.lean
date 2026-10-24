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

import Polytime2.Examples.SMP.Blocks
import Polytime2.Arrays.Transform

/-! # Certified coordinate-image computation and target conversion -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SMP

open FirstOrder FirstOrder.Language
open Polytime2.Computation

variable {L : Language.{0, 0}} [L.IsAlgebraic]
variable {Carrier Parameter : Type} [L.Structure Carrier] [Finite Carrier] [Fintype Parameter]

/-- Apply the selected image's quotient maps to every generator in a column. -/
noncomputable def columnBlocks (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then (elementDomain Carrier).constant.arrayOfLength length
    else (subalgebraDomain L Carrier).constant
  outputDomain := (elementDomain (Option (SIBlock L Carrier))).constant.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := fun index => checkedQuotientBlock (arguments.val false) (arguments.val true index)

theorem columnBlocks_realizable (length : MvPolynomial Parameter ℕ) :
    (columnBlocks (L := L) (Carrier := Carrier) length).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => (subalgebraDomain L Carrier).constant
  let source : EncodedDomain Parameter := (elementDomain Carrier).constant
  let target : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  let operation := fun sizes (values : ∀ name, (context name).Carrier sizes) (value : source.Carrier sizes) =>
    checkedQuotientBlock (values ()) value
  have step := ((quotientBlockComputation_realizable (L := L) (Carrier := Carrier)).withConstantSizes
    (Parameter := Parameter)).withArguments (arrayTransformStep context source target operation).inputDomains
      ⟨(fun choice => if choice then (Sum.inr () : Unit ⊕ Unit) else .inl ()), by
        intro first second equal; cases first <;> cases second <;> simp_all⟩
      (by intro choice; cases choice <;> rfl)
  have mapped := arrayTransform_realizable context source target length operation step
  exact mapped.withArguments (columnBlocks (L := L) (Carrier := Carrier) length).inputDomains
    ⟨(fun name => match name with | .inl _ => false | .inr _ => true), by
      rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) equal <;> first | rfl | cases equal⟩
    (by rintro (name | name); cases name; rfl; cases name; rfl)

/-- One coordinate produces its image, transformed target, and generator blocks.
The active slot pattern depends only on the image, not on the chosen value. -/
noncomputable def coordinateConversion (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains choice := if choice then (elementDomain Carrier).constant
    else (elementDomain Carrier).constant.arrayOfLength length
  outputDomain := (subalgebraDomain L Carrier).constant.prod
    ((elementDomain (Option (SIBlock L Carrier))).constant.prod
      ((elementDomain (Option (SIBlock L Carrier))).constant.arrayOfLength length))
  precondition _ _ := True
  compute sizes arguments :=
    let column : Fin (MvPolynomial.eval sizes length) → Carrier := arguments.val false
    let image := Substructure.closure L (Set.range column)
    (image, (checkedQuotientBlock image (arguments.val true),
      fun index => checkedQuotientBlock image (arguments.val false index)))

/-- The generated image is computed once and retained for both transformations. -/
theorem coordinateConversion_realizable (length : MvPolynomial Parameter ℕ) :
    (coordinateConversion (L := L) (Carrier := Carrier) length).Realizable := by
  let computation := coordinateConversion (L := L) (Carrier := Carrier) length
  let image : EncodedDomain Parameter := (subalgebraDomain L Carrier).constant
  let slot : EncodedDomain Parameter := (elementDomain (Option (SIBlock L Carrier))).constant
  have closure := (columnClosure_realizable (L := L) (Carrier := Carrier) length).withArguments
    computation.inputDomains ⟨(fun _ => false), by intro first second _; cases first; cases second; rfl⟩
    (by intro name; cases name; rfl)
  let domains : Bool ⊕ Unit → EncodedDomain Parameter := Sum.elim computation.inputDomains (fun _ => image)
  have retained := (encodingMap_realizable image image (fun _ value => value)
    (by intros; rfl) (by intros; rfl)).withArguments domains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name; rfl)
  have target := ((quotientBlockComputation_realizable (L := L) (Carrier := Carrier)).withConstantSizes
    (Parameter := Parameter)).withArguments domains
    ⟨(fun choice => if choice then (Sum.inl true : Bool ⊕ Unit) else .inr ()), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  have generators := (columnBlocks_realizable (L := L) (Carrier := Carrier) length).withArguments domains
    ⟨(fun choice => if choice then (Sum.inl false : Bool ⊕ Unit) else .inr ()), by
      intro first second equal; cases first <;> cases second <;> simp_all⟩
    (by intro choice; cases choice <;> rfl)
  have combined := closure.letThen (retained.prodMk (target.prodMk generators)) (fun _ => rfl) rfl (by intros; trivial)
  exact combined.withSpecification computation.precondition computation.compute (by intros; trivial) (by intros; rfl)

end Polytime2.SMP
