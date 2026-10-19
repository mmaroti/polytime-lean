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

import Polytime2.Examples.SMP.CatalogueOrder
import Polytime2.Arrays.Transform
import Polytime2.Arrays.Count
import Polytime2.Computation.Constant

/-! # Stored active-coordinate counts for each fixed SI catalogue sort -/

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
  let predicate := fun (_ : Empty → ℕ) (value : (subalgebraDomain L Carrier).Carrier Empty.elim) =>
    decide ((value : L.Substructure Carrier) = entry.1)
  have predicateRealizable := (finitePredicate_realizable (subalgebraDomain L Carrier) predicate).withConstantSizes
    (Parameter := Parameter)
  have booleanResult := predicateRealizable.withEncodedOutput EncodedDomain.booleans
    (fun _ arguments => decide ((arguments.val () : L.Substructure Carrier) = entry.1))
    (by intros; simp [finitePredicate, unaryMap, Computation.withConstantSizes,
      EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.constant])
    (by intros; simp [CallingConvention.encoded, finitePredicate, unaryMap, Computation.withConstantSizes,
      EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.constant,
      EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast, predicate])
  exact mapArray_realizable image EncodedDomain.booleans length
    (fun _ value => decide ((value : L.Substructure Carrier) = entry.1)) booleanResult

/-- Actual sort counts are ordinary output values at the unchanged size assignment. -/
noncomputable def catalogueCount (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    Computation Parameter Unit :=
  (catalogueFlags length entry).followedBy (countFlags length) rfl (by intros; trivial)

theorem catalogueCount_realizable (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier) :
    (catalogueCount length entry).Realizable :=
  (catalogueFlags_realizable length entry).followedBy (countFlags_realizable length) rfl (by intros; trivial)

/-- Counts are exact natural values, not new runtime size assignments. -/
theorem catalogueCount_correct (length : MvPolynomial Parameter ℕ) (entry : SICatalogue L Carrier)
    (sizes : Parameter → ℕ) (images : Fin (MvPolynomial.eval sizes length) → L.Substructure Carrier) :
    ((catalogueCount length entry).compute sizes ⟨(fun _ => images), trivial⟩).toNat =
      (List.ofFn (fun index => @decide (images index = entry.1) (Classical.propDecidable _))).count true :=
  countFlags_correct _ _ _

/-- Counts are recorded in the fixed increasing catalogue-rank order. -/
noncomputable def catalogueCounts (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (subalgebraDomain L Carrier).constant.arrayOfLength length
  outputDomain := EncodedDomain.record (Nat.card (SICatalogue L Carrier))
    (fun _ => EncodedDomain.bitVectors (length + 1))
  precondition _ _ := True
  compute sizes arguments := fun rank =>
    (catalogueCount length ((catalogueRank (L := L) (Carrier := Carrier)).symm rank)).compute sizes ⟨arguments.val, trivial⟩

theorem catalogueCounts_realizable (length : MvPolynomial Parameter ℕ) :
    (catalogueCounts (L := L) (Carrier := Carrier) length).Realizable :=
  Realizable.recordOutputs _ _ _ _ _ (fun rank => catalogueCount_realizable length (catalogueRank.symm rank))

end Polytime2.SMP
