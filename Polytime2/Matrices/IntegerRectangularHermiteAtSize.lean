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

import Polytime2.Matrices.IntegerRectangularHermiteAtRank
import Polytime2.Matrices.IntegerRename

/-! # Host parameter views for rectangular Hermite reduction at a named rank

Invoke leading-block rectangular reduction at the named active rank. Its
capacity depends only on host dimensions and input width. Return all three
matrices through the existing bit-preserving original-parameter view.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

private noncomputable def callee (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  integerRectangularHermiteAtRank (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names width)

private noncomputable def native (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  (callee rows columns width names rankName).onResults
    (fun _ : Unit => (integerMatrices rows columns width).renameParameters names)
    (fun sizes arguments => (callee rows columns width names rankName).precondition sizes
      (fun _ => integerMatricesRenameValues rows columns width names sizes (arguments ())))
    (fun _ sizes arguments => integerMatricesRenameValues rows columns width names sizes (arguments.val ()))
    (by intro sizes arguments; exact arguments.property)

private theorem native_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (native rows columns width names rankName).Realizable := by
  apply (integerRectangularHermiteAtRank_realizable (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names width)).onResults
    (fun _ : Unit => (integerMatrices rows columns width).renameParameters names) _ _
    (by intro sizes arguments; exact arguments.property)
  intro singleton
  cases singleton
  exact (integerMatrixRenamedView_realizable rows columns width names).withPrecondition _ (by intros; trivial)

omit [Fintype HostParameter] [Fintype Parameter] in
private theorem outputWidth_rename (rows width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    rectangularHermiteOutputWidth (MvPolynomial.rename names rows) (MvPolynomial.rename names width) =
      MvPolynomial.rename names (rectangularHermiteOutputWidth rows width) := by
  simp [rectangularHermiteOutputWidth, hermiteAlternatingEntryWidth,
    hermiteAlternatingRunBasisWidth, hermiteAlternatingBasisWidth, hermiteAlternatingBudget,
    IntegerMatrix.hermiteSweepBasisIncrement, map_ofNat]

private theorem compatible (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerMatrixPresentationOriginalView rows columns (rectangularHermiteOutputWidth rows width)
      (rectangularHermiteOutputWidth rows width) (rectangularHermiteOutputWidth rows width) names).inputDomains () =
      (native rows columns width names rankName).outputDomain := by
  change ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularHermiteOutputWidth rows width))).prod
    ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names rows)
      (MvPolynomial.rename names (rectangularHermiteOutputWidth rows width))).prod
    (integerMatrices (MvPolynomial.rename names columns) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularHermiteOutputWidth rows width))))) = _
  rw [← outputWidth_rename]
  rfl

/-- Reduce at the named rank and return the three full matrices in their host domains. -/
noncomputable def integerRectangularHermiteAtSize (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter Unit :=
  (native rows columns width names rankName).followedBy
    (integerMatrixPresentationOriginalView rows columns (rectangularHermiteOutputWidth rows width)
      (rectangularHermiteOutputWidth rows width) (rectangularHermiteOutputWidth rows width) names)
    (compatible rows columns width names rankName) (by intros; trivial)

/-- Native-dimension reduction and original-domain reconstruction retain canonical bits. -/
theorem integerRectangularHermiteAtSize_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerRectangularHermiteAtSize rows columns width names rankName).Realizable :=
  (native_realizable rows columns width names rankName).followedBy
    (integerMatrixPresentationOriginalView_realizable rows columns (rectangularHermiteOutputWidth rows width)
      (rectangularHermiteOutputWidth rows width) (rectangularHermiteOutputWidth rows width) names)
    (compatible rows columns width names rankName) (by intros; trivial)

/-- Host rank bounds and a positive lower active block permit the named-rank call. -/
theorem integerRectangularHermiteAtSize_permitted (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularHermiteAtSize rows columns width names rankName).Arguments sizes)
    (rowBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) rows)
    (columnBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) columns)
    (lower : ((arguments ()).val.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).IsLowerTriangular)
    (positive : ∀ index, 0 < (arguments ()).val (Fin.castLE rowBound index) (Fin.castLE columnBound index)) :
    (integerRectangularHermiteAtSize rows columns width names rankName).precondition sizes arguments := by
  have nativeRows : MvPolynomial.eval sizes (MvPolynomial.X rankName) ≤ MvPolynomial.eval sizes (MvPolynomial.rename names rows) := by
    simpa only [MvPolynomial.eval_X, MvPolynomial.eval_rename] using rowBound
  have nativeColumns : MvPolynomial.eval sizes (MvPolynomial.X rankName) ≤ MvPolynomial.eval sizes (MvPolynomial.rename names columns) := by
    simpa only [MvPolynomial.eval_X, MvPolynomial.eval_rename] using columnBound
  apply integerLeadingBlockDiagonalize_permitted (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names width) sizes
    (fun _ => integerMatricesRenameValues rows columns width names sizes (arguments ())) nativeRows nativeColumns
  · intro row column before
    have zero := @lower (Fin.cast (MvPolynomial.eval_X rankName) row) (Fin.cast (MvPolynomial.eval_X rankName) column) before
    change (arguments ()).val _ _ = 0
    convert zero using 1
    apply congrArg₂ (arguments ()).val <;> apply Fin.ext <;> rfl
  · intro index
    have pos := positive (Fin.cast (MvPolynomial.eval_X rankName) index)
    change 0 < (arguments ()).val _ _
    convert pos using 1
    apply congrArg₂ (arguments ()).val <;> apply Fin.ext <;> rfl

/-- Named-rank reduction returns exactly the mathematical result in host dimensions. -/
theorem integerRectangularHermiteAtSize_correct (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteAtSize rows columns width names rankName).Arguments sizes //
      (integerRectangularHermiteAtSize rows columns width names rankName).precondition sizes arguments})
    (rowBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) rows)
    (columnBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) columns) :
    let result := (integerRectangularHermiteAtSize rows columns width names rankName).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.rectangularHermiteRun rowBound columnBound (MvPolynomial.eval (sizes ∘ names) width)
        ((arguments.val ()).val.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)) := by
  let nativeArguments := fun _ : Unit => integerMatricesRenameValues rows columns width names sizes (arguments.val ())
  let nativeBounds := arguments.property.choose
  let original := (native rows columns width names rankName).compute sizes arguments
  have actual : (original.1.val, original.2.1.val, original.2.2.val) =
      IntegerMatrix.rectangularHermiteRun nativeBounds.1 nativeBounds.2
        (MvPolynomial.eval sizes (MvPolynomial.rename names width))
        ((nativeArguments ()).val.submatrix (Fin.castLE nativeBounds.1) (Fin.castLE nativeBounds.2)) :=
    integerRectangularHermiteAtRank_correct (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.X rankName) (MvPolynomial.rename names width) sizes ⟨nativeArguments, arguments.property⟩
  have agreement := IntegerMatrix.rectangularHermiteRun_congr
    (MvPolynomial.eval_rename names sizes rows) (MvPolynomial.eval_rename names sizes columns)
    (MvPolynomial.eval_X rankName) (MvPolynomial.eval_rename names sizes width)
    nativeBounds.1 nativeBounds.2 rowBound columnBound
    ((nativeArguments ()).val.submatrix (Fin.castLE nativeBounds.1) (Fin.castLE nativeBounds.2))
    ((arguments.val ()).val.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)) (by
      intro row column otherRow otherColumn rowSame columnSame
      apply congrArg₂ (arguments.val ()).val <;> exact Fin.ext (by assumption))
  have values := integerMatrixPresentationOriginalView_values rows columns
    (rectangularHermiteOutputWidth rows width) (rectangularHermiteOutputWidth rows width)
    (rectangularHermiteOutputWidth rows width) names _ _ _
    (outputWidth_rename rows width names) (outputWidth_rename rows width names) (outputWidth_rename rows width names)
    (compatible rows columns width names rankName) sizes original
  have transported := congrArg (fun result =>
    ((fun row column => result.1 (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)),
    (fun row column => result.2.1 (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm column)),
    (fun row column => result.2.2 (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)))) actual
  apply values.trans (transported.trans ?_)
  apply Prod.ext
  · funext row column
    exact agreement.1 _ _ row column rfl rfl
  · apply Prod.ext
    · funext row column
      exact agreement.2.1 _ _ row column rfl rfl
    · funext row column
      exact agreement.2.2 _ _ row column rfl rfl

end Polytime2.Computation
