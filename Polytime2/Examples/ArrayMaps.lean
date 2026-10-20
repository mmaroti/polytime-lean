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

import Polytime2.Arrays.Operations
import Polytime2.Matrices.FieldRow
import Polytime2.Computation.Records

/-! # Mathematical array maps and finite-field row scaling -/

namespace Polytime2.Examples.ArrayMaps

open Polytime2.Computation

-- Parameter: runtime size names; Scalar: the specialization-fixed finite field.
variable {Parameter : Type} [Fintype Parameter]
variable {Scalar : Type} [Field Scalar] [Fintype Scalar]

noncomputable def scaledRow (length : MvPolynomial Parameter ℕ) : Polytime2.Computation Parameter Bool :=
  arrayMap (FieldRow.scalarDomain (Fintype.equivFin Scalar))
    (FieldRow.scalarDomain (Fintype.equivFin Scalar)) length
    (fun (coefficient value : Scalar) => coefficient * value)

theorem scaledRow_realizable (length : MvPolynomial Parameter ℕ) :
    (scaledRow (Scalar := Scalar) length).Realizable := arrayMap_realizable _ _ _ _

theorem scaledRow_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (scaledRow (Scalar := Scalar) length).Arguments sizes)
    (valid : (scaledRow (Scalar := Scalar) length).precondition sizes arguments) :
    (scaledRow (Scalar := Scalar) length).compute sizes ⟨arguments, valid⟩ =
      fun index => (fun (coefficient value : Scalar) => coefficient * value)
        (arguments false) (arguments true index) := rfl

-- Mapping also covers empty arrays and arrays of zero-bit singleton elements.
example (length : MvPolynomial Parameter ℕ) :
    (arrayMap (EncodedDomain.fixed (Equiv.refl (Fin 1)))
      (EncodedDomain.fixed (Equiv.refl (Fin 1))) length (fun _ value => value)).Realizable :=
  arrayMap_realizable _ _ _ _

-- Scalar pairs used by row maps have the generic certified pair operations.
example (second : Bool) :
    (pairProjection (FieldRow.scalarDomain (Fintype.equivFin Scalar))
      (FieldRow.scalarDomain (Fintype.equivFin Scalar)) second).Realizable :=
  pairProjection_realizable _ _ _

end Polytime2.Examples.ArrayMaps
