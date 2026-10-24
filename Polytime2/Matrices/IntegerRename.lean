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

import Polytime2.Encoding.IntegerMatrices
import Polytime2.Primitives.BitOperations

/-! # Integer matrices at renamed mathematical dimensions

Computed-rank callees retain original matrix data while naming its dimensions
in a larger size family. The canonical row-major encoding is unchanged.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

/-- View a host matrix at its renamed mathematical dimensions and entry width. -/
noncomputable def integerMatrixRenamedView (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((integerMatrices rows columns width).renameParameters names)
    (integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names width))
    (integerMatricesRenameValues rows columns width names)

/-- Only the mathematical indices change; the existing encoded word is retained. -/
theorem integerMatrixRenamedView_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    (integerMatrixRenamedView rows columns width names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, integerMatrices, EncodedDomain.matrix,
      EncodedDomain.arrayOfLength, EncodedDomain.reindex,
      binaryIntegers, EncodedDomain.restrict, EncodedDomain.prod, MvPolynomial.eval_rename]
  · intro sizes value
    exact (integerMatricesRenameValues_bits rows columns width names sizes value).symm

/-- Return a renamed-dimension matrix to its original host carrier. -/
noncomputable def integerMatrixOriginalView (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap (integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width)) ((integerMatrices rows columns width).renameParameters names)
    (fun sizes => (integerMatricesRenameEquiv rows columns width names sizes).symm)

/-- The inverse parameter view reuses exactly the existing matrix word. -/
theorem integerMatrixOriginalView_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    (integerMatrixOriginalView rows columns width names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, integerMatrices, EncodedDomain.matrix,
      EncodedDomain.arrayOfLength, EncodedDomain.reindex, binaryIntegers,
      EncodedDomain.restrict, EncodedDomain.prod, MvPolynomial.eval_rename]
  · intro sizes value
    exact (integerMatricesRenameEquiv_symm_bits rows columns width names sizes value).symm

end Polytime2.Computation
