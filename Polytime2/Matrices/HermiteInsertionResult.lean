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

import Polytime2.Matrices.IntegerRename
import Polytime2.Arrays.SearchCoordinates

/-! # Returning an insertion result to its original parameter carrier

Both actual matrices and the optional new pivot keep their canonical bits when
renamed dimensions are viewed through the original host size assignment.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Two bounded matrices and an optional new column, with ordinary mathematical carriers. -/
noncomputable def hermiteInsertionResult (rows columns width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ((integerMatrices rows columns width).prod (integerMatrices rows rows width)).prod (arraySearchResult columns)

end Polytime2.EncodedDomain

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

/-- Reinterpret the complete insertion result at its original dimensions. -/
noncomputable def hermiteInsertionResultOriginalView (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap (hermiteInsertionResult (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.rename names width)) ((hermiteInsertionResult rows columns width).renameParameters names)
    (fun sizes value =>
      (((integerMatricesRenameEquiv rows columns width names sizes).symm value.1.1,
        (integerMatricesRenameEquiv rows rows width names sizes).symm value.1.2),
        value.2.map (Fin.cast (MvPolynomial.eval_rename names sizes columns))))

/-- Matrix and optional-coordinate parameter transport preserve the entire result word. -/
theorem hermiteInsertionResultOriginalView_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    (hermiteInsertionResultOriginalView rows columns width names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, hermiteInsertionResult, integerMatrices, EncodedDomain.matrix,
      EncodedDomain.arrayOfLength, EncodedDomain.reindex, binaryIntegers,
      EncodedDomain.restrict, EncodedDomain.prod, arraySearchResult, boundedIndexOfWidth,
      MvPolynomial.eval_rename]
  · intro sizes value
    have matrixBits := integerMatricesRenameEquiv_symm_bits rows columns width names sizes value.1.1
    have basisBits := integerMatricesRenameEquiv_symm_bits rows rows width names sizes value.1.2
    have pivotBits := arraySearchResult_original_bits columns names sizes value.2
    simp only [renameParameters_bits] at matrixBits basisBits pivotBits
    simp only [renameParameters_bits, hermiteInsertionResult, bits_prod_encode,
      ArrayEncoding.bits_cast, ArrayEncoding.bits_append]
    rw [← matrixBits, ← basisBits, pivotBits]

end Polytime2.Computation
