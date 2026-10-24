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
import Polytime2.Matrices.SmithMath
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

/-- A full matrix and both square bases with independent entry bounds. -/
noncomputable def integerMatrixPresentation (rows columns width : MvPolynomial Parameter ℕ)
    (leftWidth : MvPolynomial Parameter ℕ := width) (rightWidth : MvPolynomial Parameter ℕ := width) :=
  (integerMatrices rows columns width).prod
    ((integerMatrices rows rows leftWidth).prod (integerMatrices columns columns rightWidth))

/-- Return the three matrices to the original host domains, preserving bits. -/
noncomputable def integerMatrixPresentationOriginalView
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap
    ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names matrixWidth)).prod
      ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names rows)
        (MvPolynomial.rename names leftWidth)).prod
      (integerMatrices (MvPolynomial.rename names columns) (MvPolynomial.rename names columns)
        (MvPolynomial.rename names rightWidth))))
    (((integerMatrices rows columns matrixWidth).prod
      ((integerMatrices rows rows leftWidth).prod (integerMatrices columns columns rightWidth))).renameParameters names)
    (fun sizes value =>
      ((integerMatricesRenameEquiv rows columns matrixWidth names sizes).symm value.1,
        (integerMatricesRenameEquiv rows rows leftWidth names sizes).symm value.2.1,
        (integerMatricesRenameEquiv columns columns rightWidth names sizes).symm value.2.2))

/-- Each matrix view retains its canonical word, so the whole result does too. -/
theorem integerMatrixPresentationOriginalView_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    (integerMatrixPresentationOriginalView rows columns matrixWidth leftWidth rightWidth names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, integerMatrices, EncodedDomain.matrix,
      EncodedDomain.arrayOfLength, EncodedDomain.reindex, binaryIntegers,
      EncodedDomain.restrict, EncodedDomain.prod, MvPolynomial.eval_rename]
  · intro sizes value
    have matrixBits := integerMatricesRenameEquiv_symm_bits rows columns matrixWidth names sizes value.1
    have leftBits := integerMatricesRenameEquiv_symm_bits rows rows leftWidth names sizes value.2.1
    have rightBits := integerMatricesRenameEquiv_symm_bits columns columns rightWidth names sizes value.2.2
    simp only [renameParameters_bits] at matrixBits leftBits rightBits
    simp only [renameParameters_bits, bits_prod_encode, ArrayEncoding.bits_cast, ArrayEncoding.bits_append]
    rw [← matrixBits, ← leftBits, ← rightBits]

/-- Returning a presentation to host dimensions preserves its three matrices,
even when native width formulas are only propositionally equal to renamings. -/
theorem integerMatrixPresentationOriginalView_values
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter)
    (nativeMatrixWidth nativeLeftWidth nativeRightWidth : MvPolynomial Parameter ℕ)
    (matrixWidthEqual : nativeMatrixWidth = MvPolynomial.rename names matrixWidth)
    (leftWidthEqual : nativeLeftWidth = MvPolynomial.rename names leftWidth)
    (rightWidthEqual : nativeRightWidth = MvPolynomial.rename names rightWidth)
    (domainEqual : (integerMatrixPresentationOriginalView rows columns matrixWidth leftWidth rightWidth names).inputDomains () =
      integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
        nativeMatrixWidth nativeLeftWidth nativeRightWidth)
    (sizes : Parameter → ℕ)
    (value : (integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      nativeMatrixWidth nativeLeftWidth nativeRightWidth).Carrier sizes) :
    let result := (integerMatrixPresentationOriginalView rows columns matrixWidth leftWidth rightWidth names).compute sizes
      ⟨fun _ => domainEqual.symm ▸ value, trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) =
      ((fun row column => value.1.val
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)),
      (fun row column => value.2.1.val
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm column)),
      (fun row column => value.2.2.val
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column))) := by
  subst nativeMatrixWidth nativeLeftWidth nativeRightWidth
  rfl

set_option maxHeartbeats 800000 in
/-- Host-domain reconstruction preserves the Smith contract independently of
how the supplied presentation was computed. -/
theorem integerMatrixPresentationOriginalView_isSmithForm
    (rows columns width : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (nativeWidth : MvPolynomial Parameter ℕ) (widthEqual : nativeWidth = MvPolynomial.rename names width)
    (domainEqual : (integerMatrixPresentationOriginalView rows columns width width width names).inputDomains () =
      integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns) nativeWidth)
    (sizes : Parameter → ℕ)
    (matrix : Matrix (Fin (MvPolynomial.eval (sizes ∘ names) rows)) (Fin (MvPolynomial.eval (sizes ∘ names) columns)) ℤ)
    (value : (integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns) nativeWidth).Carrier sizes)
    (nativeRank rank : ℕ) (rankEqual : nativeRank = rank)
    (form : IntegerMatrix.IsSmithForm
      (fun row column => matrix (Fin.cast (MvPolynomial.eval_rename names sizes rows) row)
        (Fin.cast (MvPolynomial.eval_rename names sizes columns) column))
      value.1.val value.2.1.val value.2.2.val nativeRank) :
    let result := (integerMatrixPresentationOriginalView rows columns width width width names).compute sizes
      ⟨fun _ => domainEqual.symm ▸ value, trivial⟩
    IntegerMatrix.IsSmithForm matrix result.1.val result.2.1.val result.2.2.val rank := by
  subst nativeWidth
  exact @IntegerMatrix.IsSmithForm.cast
    (MvPolynomial.eval sizes (MvPolynomial.rename names rows)) (MvPolynomial.eval sizes (MvPolynomial.rename names columns))
    (MvPolynomial.eval (sizes ∘ names) rows) (MvPolynomial.eval (sizes ∘ names) columns) nativeRank rank
    (MvPolynomial.eval_rename names sizes rows) (MvPolynomial.eval_rename names sizes columns) rankEqual
    (fun row column => matrix (Fin.cast (MvPolynomial.eval_rename names sizes rows) row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns) column))
    value.1.val value.2.1.val value.2.2.val form


end Polytime2.Computation
