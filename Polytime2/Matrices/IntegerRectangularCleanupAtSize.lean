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

import Polytime2.Matrices.IntegerRectangularCleanup
import Polytime2.Matrices.IntegerCompactAtSize

/-! # Host parameter views for divisibility cleanup at a named rank

Invoke full rectangular diagonal cleanup at the named active rank. Its
capacity depends only on host dimensions and input width. Return all three
matrices through the existing bit-preserving original-parameter view.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

private noncomputable def callee (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :=
  integerRectangularCleanupAtRank (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
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
  apply (integerRectangularCleanupAtRank_realizable (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names width)).onResults
    (fun _ : Unit => (integerMatrices rows columns width).renameParameters names) _ _
    (by intro sizes arguments; exact arguments.property)
  intro singleton
  cases singleton
  exact (integerMatrixRenamedView_realizable rows columns width names).withPrecondition _ (by intros; trivial)

omit [Fintype HostParameter] [Fintype Parameter] in
private theorem outputWidth_rename (rows width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) :
    rectangularCleanupOutputWidth (MvPolynomial.rename names rows) (MvPolynomial.rename names width) =
      MvPolynomial.rename names (rectangularCleanupOutputWidth rows width) := by
  simp [rectangularCleanupOutputWidth, positiveDiagonalProductWidth,
    positiveDiagonalBasisWidth, positiveDiagonalBudget, diagonalCleanupWorkspace,
    map_ofNat]

private theorem compatible (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerCompactResultOriginalView rows columns (rectangularCleanupOutputWidth rows width)
      (rectangularCleanupOutputWidth rows width) (rectangularCleanupOutputWidth rows width) names).inputDomains () =
      (native rows columns width names rankName).outputDomain := by
  change ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width))).prod
    ((integerMatrices (MvPolynomial.rename names rows) (MvPolynomial.rename names rows)
      (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width))).prod
    (integerMatrices (MvPolynomial.rename names columns) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width))))) = _
  rw [← outputWidth_rename]
  rfl

/-- Clean divisibility at the named rank and return the three full matrices in their host domains. -/
noncomputable def integerRectangularCleanupAtSize (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) : Computation Parameter Unit :=
  (native rows columns width names rankName).followedBy
    (integerCompactResultOriginalView rows columns (rectangularCleanupOutputWidth rows width)
      (rectangularCleanupOutputWidth rows width) (rectangularCleanupOutputWidth rows width) names)
    (compatible rows columns width names rankName) (by intros; trivial)

/-- Native-dimension cleanup and original-domain reconstruction retain canonical bits. -/
theorem integerRectangularCleanupAtSize_realizable (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) :
    (integerRectangularCleanupAtSize rows columns width names rankName).Realizable :=
  (native_realizable rows columns width names rankName).followedBy
    (integerCompactResultOriginalView_realizable rows columns (rectangularCleanupOutputWidth rows width)
      (rectangularCleanupOutputWidth rows width) (rectangularCleanupOutputWidth rows width) names)
    (compatible rows columns width names rankName) (by intros; trivial)

/-- Host rank bounds and a positive rectangular diagonal permit cleanup. -/
theorem integerRectangularCleanupAtSize_permitted (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularCleanupAtSize rows columns width names rankName).Arguments sizes)
    (rowBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) rows)
    (columnBound : sizes rankName ≤ MvPolynomial.eval (sizes ∘ names) columns)
    (diagonal : Fin (sizes rankName) → ℕ)
    (positive : ∀ index, 0 < diagonal index)
    (equation : (arguments ()).val = IntegerMatrix.rectangularDiagonal
      (MvPolynomial.eval (sizes ∘ names) rows)
      (MvPolynomial.eval (sizes ∘ names) columns) diagonal) :
    (integerRectangularCleanupAtSize rows columns width names rankName).precondition sizes arguments := by
  have nativeRows : MvPolynomial.eval sizes (MvPolynomial.X rankName) ≤ MvPolynomial.eval sizes (MvPolynomial.rename names rows) := by
    simpa only [MvPolynomial.eval_X, MvPolynomial.eval_rename] using rowBound
  have nativeColumns : MvPolynomial.eval sizes (MvPolynomial.X rankName) ≤ MvPolynomial.eval sizes (MvPolynomial.rename names columns) := by
    simpa only [MvPolynomial.eval_X, MvPolynomial.eval_rename] using columnBound
  let nativeDiagonal : Fin (MvPolynomial.eval sizes (MvPolynomial.X rankName)) → ℕ :=
    fun index => diagonal (Fin.cast (MvPolynomial.eval_X rankName) index)
  apply integerRectangularCleanup_permitted (MvPolynomial.rename names rows)
    (MvPolynomial.rename names columns) (MvPolynomial.X rankName)
    (MvPolynomial.rename names width) sizes
    (fun _ => integerMatricesRenameValues rows columns width names sizes (arguments ()))
    nativeRows nativeColumns nativeDiagonal (fun index => positive _)
  funext row column
  have same := congrArg (fun matrix => matrix
    (Fin.cast (MvPolynomial.eval_rename names sizes rows) row)
    (Fin.cast (MvPolynomial.eval_rename names sizes columns) column)) equation
  exact same.trans (by
    simp [IntegerMatrix.rectangularDiagonal, nativeDiagonal])

set_option maxHeartbeats 800000 in
/-- Named-rank cleanup satisfies the Smith contract in the original host dimensions. -/
theorem integerRectangularCleanupAtSize_isSmithForm
    (rows columns width : MvPolynomial HostParameter ℕ)
    (names : HostParameter → Parameter) (rankName : Parameter) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanupAtSize rows columns width names rankName).Arguments sizes //
      (integerRectangularCleanupAtSize rows columns width names rankName).precondition sizes arguments}) :
    let result := (integerRectangularCleanupAtSize rows columns width names rankName).compute sizes arguments
    IntegerMatrix.IsSmithForm (arguments.val ()).val result.1.val result.2.1.val result.2.2.val (sizes rankName) := by
  let nativeArguments := fun _ : Unit => integerMatricesRenameValues rows columns width names sizes (arguments.val ())
  have form := integerRectangularCleanupAtRank_isSmithForm
    (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (MvPolynomial.X rankName) (MvPolynomial.rename names width) sizes
    ⟨nativeArguments, arguments.property⟩
  let original : (integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (rectangularCleanupOutputWidth (MvPolynomial.rename names rows) (MvPolynomial.rename names width))).Carrier sizes :=
    (native rows columns width names rankName).compute sizes arguments
  have originalEq : original =
      (integerRectangularCleanupAtRank (MvPolynomial.rename names rows)
        (MvPolynomial.rename names columns) (MvPolynomial.X rankName)
        (MvPolynomial.rename names width)).compute sizes ⟨nativeArguments, arguments.property⟩ := by
    dsimp only [original, native, callee, Computation.onResults]
  have originalForm : IntegerMatrix.IsSmithForm (nativeArguments ()).val
      original.1.val original.2.1.val original.2.2.val
      (MvPolynomial.eval sizes (MvPolynomial.X rankName)) := by
    rw [originalEq]
    exact form
  let codecEqual : integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width)) =
      integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
        (rectangularCleanupOutputWidth (MvPolynomial.rename names rows) (MvPolynomial.rename names width)) :=
    compatible rows columns width names rankName
  let converted : (integerMatrixPresentation (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
      (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width))).Carrier sizes :=
    codecEqual.symm ▸ original
  have transported := integerMatrixPresentation_transport_values
    (MvPolynomial.rename names rows) (MvPolynomial.rename names columns)
    (rectangularCleanupOutputWidth (MvPolynomial.rename names rows) (MvPolynomial.rename names width))
    (MvPolynomial.rename names (rectangularCleanupOutputWidth rows width))
    (outputWidth_rename rows width names) codecEqual sizes original
  change (converted.1.val, converted.2.1.val, converted.2.2.val) =
    (original.1.val, original.2.1.val, original.2.2.val) at transported
  have convertedForm : IntegerMatrix.IsSmithForm (nativeArguments ()).val
      converted.1.val converted.2.1.val converted.2.2.val
      (MvPolynomial.eval sizes (MvPolynomial.X rankName)) := by
    exact @IntegerMatrix.IsSmithForm.of_values
      (MvPolynomial.eval sizes (MvPolynomial.rename names rows))
      (MvPolynomial.eval sizes (MvPolynomial.rename names columns))
      (nativeArguments ()).val (MvPolynomial.eval sizes (MvPolynomial.X rankName))
      (original.1.val, original.2.1.val, original.2.2.val)
      (converted.1.val, converted.2.1.val, converted.2.2.val) transported originalForm
  have hostForm := @IntegerMatrix.IsSmithForm.cast
    (MvPolynomial.eval sizes (MvPolynomial.rename names rows))
    (MvPolynomial.eval sizes (MvPolynomial.rename names columns))
    (MvPolynomial.eval (sizes ∘ names) rows) (MvPolynomial.eval (sizes ∘ names) columns)
    (MvPolynomial.eval sizes (MvPolynomial.X rankName)) (sizes rankName)
    (MvPolynomial.eval_rename names sizes rows) (MvPolynomial.eval_rename names sizes columns)
    (MvPolynomial.eval_X rankName) (nativeArguments ()).val
    converted.1.val converted.2.1.val converted.2.2.val convertedForm
  have inputSame : (fun row column => (nativeArguments ()).val
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)) = (arguments.val ()).val := by
    funext row column
    apply congrArg₂ (arguments.val ()).val <;> apply Fin.ext <;> rfl
  have hostInput := congrArg (fun matrix => IntegerMatrix.IsSmithForm matrix
    (fun row column => converted.1.val
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column))
    (fun row column => converted.2.1.val
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes rows).symm column))
    (fun row column => converted.2.2.val
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm row)
      (Fin.cast (MvPolynomial.eval_rename names sizes columns).symm column)) (sizes rankName)) inputSame
  exact hostInput.mp hostForm

end Polytime2.Computation
