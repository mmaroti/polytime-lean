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

import Polytime2.Matrices.IntegerRectangularHermiteAtSize
import Polytime2.Computation.ComputedCall

/-! # Rectangular Hermite reduction at the decoded active rank

The input pairs the mathematical rank with the supported rectangular matrix.
Read the rank internally, invoke the named-rank reduction, and discard the
internal size header. Full result capacities depend only on host dimensions
and the input entry width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def input (rows columns width : MvPolynomial Parameter ℕ) :=
  (boundedUnary columns).prod (integerMatrices rows columns width)

private noncomputable def payload (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerMatrices rows columns (rectangularHermiteOutputWidth rows width)).prod
    ((integerMatrices rows rows (rectangularHermiteOutputWidth rows width)).prod
      (integerMatrices columns columns (rectangularHermiteOutputWidth rows width)))

private noncomputable def bounds (columns : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ := fun _ => columns

private noncomputable def callee (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerRectangularHermiteAtSize rows columns width Sum.inl (.inr ())).onResults
    (fun _ : Unit => (input rows columns width).renameParameters Sum.inl)
    (fun sizes arguments => (integerRectangularHermiteAtSize rows columns width Sum.inl (.inr ())).precondition sizes
      (fun _ => (arguments ()).2))
    (fun _ _ arguments => (arguments.val ()).2) (by intro sizes arguments; exact arguments.property)

private theorem callee_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (callee rows columns width).Realizable := by
  apply (integerRectangularHermiteAtSize_realizable rows columns width Sum.inl (.inr ())).onResults
    (fun _ : Unit => (input rows columns width).renameParameters Sum.inl) _ _
    (by intro sizes arguments; exact arguments.property)
  intro singleton
  cases singleton
  exact ((renamedPairView_realizable (boundedUnary columns) (integerMatrices rows columns width)
    (Sum.inl : Parameter → Parameter ⊕ Unit)).followedBy
      (pairProjection_realizable ((boundedUnary columns).renameParameters Sum.inl)
        ((integerMatrices rows columns width).renameParameters Sum.inl) true) rfl (by intros; trivial)).withPrecondition _ (by intros; trivial)

private noncomputable def frame (rows columns width : MvPolynomial Parameter ℕ) :=
  (extendedSizeFrame (bounds columns) (input rows columns width)).onResults
    (fun _ : Unit => input rows columns width) (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => fun _ => (arguments.val ()).1 | true => arguments.val ()) (by intros; trivial)

private theorem frame_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (frame rows columns width).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => input rows columns width
  have rank := pairProjection_realizable (boundedUnary columns) (integerMatrices rows columns width) false
  apply (extendedSizeFrame_realizable (bounds columns) (input rows columns width)).onResults
    context (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · apply Realizable.namedRecordOutputs
    intro name
    cases name
    exact rank
  · exact Realizable.argument context () (fun _ _ => True)

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (input rows columns width).Carrier sizes) : Prop :=
  ∃ within : (arguments ()).1.val ≤ MvPolynomial.eval sizes rows ∧
      (arguments ()).1.val ≤ MvPolynomial.eval sizes columns,
    ((arguments ()).2.val.submatrix (Fin.castLE within.1) (Fin.castLE within.2)).IsLowerTriangular ∧
      ∀ index, 0 < (arguments ()).2.val (Fin.castLE within.1 index) (Fin.castLE within.2 index)

private noncomputable def call (rows columns width : MvPolynomial Parameter ℕ) :=
  (callee rows columns width).atComputedUnarySizes (extendedSizeBounds (bounds columns))

private theorem permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (input rows columns width).Carrier sizes) (valid : allowed rows columns width sizes arguments) :
    (call rows columns width).precondition sizes
      (fun _ => (frame rows columns width).compute sizes ⟨arguments, trivial⟩) := by
  obtain ⟨within, lower, positive⟩ := valid
  let framed := (frame rows columns width).compute sizes ⟨arguments, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds columns)) sizes framed.1
  change (integerRectangularHermiteAtSize rows columns width Sum.inl (.inr ())).precondition actual (fun _ => framed.2.2)
  exact integerRectangularHermiteAtSize_permitted rows columns width Sum.inl (.inr ()) actual
    (fun _ => framed.2.2) within.1 within.2 lower positive

/-- Decode the active rank and reduce, retaining the internal computed-size header. -/
noncomputable def integerRectangularHermiteStoredRank (rows columns width : MvPolynomial Parameter ℕ) :=
  (call rows columns width).onResults (frame rows columns width).inputDomains (allowed rows columns width)
    (fun _ sizes arguments => (frame rows columns width).compute sizes ⟨arguments.val, trivial⟩)
    (fun sizes arguments => permitted rows columns width sizes arguments.val arguments.property)

/-- Rank reading, size preparation, and the complete stored-rank call are realized. -/
theorem integerRectangularHermiteStoredRank_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermiteStoredRank rows columns width).Realizable := by
  apply ((callee_realizable rows columns width).atComputedUnarySizes (extendedSizeBounds (bounds columns))).onResults
    (frame rows columns width).inputDomains (allowed rows columns width) _
    (fun sizes arguments => permitted rows columns width sizes arguments.val arguments.property)
  intro singleton
  cases singleton
  exact (frame_realizable rows columns width).withPrecondition _ (by intros; trivial)

/-- Reduce at the decoded rank and return only the three full host matrices. -/
noncomputable def integerRectangularHermiteHost (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerRectangularHermiteStoredRank rows columns width).inputDomains
  outputDomain := payload rows columns width
  precondition := allowed rows columns width
  compute sizes arguments := ((integerRectangularHermiteStoredRank rows columns width).compute sizes arguments).2

/-- The canonical host-frame view removes the internal size header without changing payload bits. -/
theorem integerRectangularHermiteHost_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermiteHost rows columns width).Realizable := by
  let output := payload rows columns width
  let index := computedSizeDomain (extendedSizeBounds (bounds columns))
  let computation := integerRectangularHermiteStoredRank rows columns width
  have viewed := (integerRectangularHermiteStoredRank_realizable rows columns width).withEncodedOutput
    (index.prod output) (fun sizes arguments => let result := computation.compute sizes arguments; (result.1, result.2)) (by
      intro sizes
      change MvPolynomial.eval sizes (index.widthPolynomial + output.widthPolynomial) =
        MvPolynomial.eval sizes (index.widthPolynomial + SizeSubstitution.polynomial (extendedSizeBounds (bounds columns))
          (output.renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)).widthPolynomial)
      rw [extendedSize_payloadWidth]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      let counts : (computedSizeDomain (bounds columns)).Carrier sizes := fun _ => (arguments.val ()).1
      exact (extendedSizeFrame_encode_bits (bounds columns) output sizes counts (computation.compute sizes arguments).2).symm)
  exact viewed.followedBy (pairProjection_realizable index output true) rfl (by intros; trivial)

/-- The size passed to the callee is exactly the rank supplied with the matrix. -/
theorem integerRectangularHermiteStoredRank_count (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteStoredRank rows columns width).Arguments sizes //
      (integerRectangularHermiteStoredRank rows columns width).precondition sizes arguments}) :
    (((integerRectangularHermiteStoredRank rows columns width).compute sizes arguments).1 (.inr ())).val =
      (arguments.val ()).1.val := rfl

/-- Only mathematical rank bounds and the positive lower active block are required. -/
theorem integerRectangularHermiteHost_permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularHermiteHost rows columns width).Arguments sizes)
    (rowBound : (arguments ()).1.val ≤ MvPolynomial.eval sizes rows)
    (columnBound : (arguments ()).1.val ≤ MvPolynomial.eval sizes columns)
    (lower : ((arguments ()).2.val.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).IsLowerTriangular)
    (positive : ∀ index, 0 < (arguments ()).2.val (Fin.castLE rowBound index) (Fin.castLE columnBound index)) :
    (integerRectangularHermiteHost rows columns width).precondition sizes arguments :=
  ⟨⟨rowBound, columnBound⟩, lower, positive⟩

/-- The decoded-rank call returns exactly the rectangular reduction in host dimensions. -/
theorem integerRectangularHermiteHost_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteHost rows columns width).Arguments sizes //
      (integerRectangularHermiteHost rows columns width).precondition sizes arguments}) :
    let result := (integerRectangularHermiteHost rows columns width).compute sizes arguments
    let within := arguments.property.choose
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.rectangularHermiteRun within.1 within.2 (MvPolynomial.eval sizes width)
        ((arguments.val ()).2.val.submatrix (Fin.castLE within.1) (Fin.castLE within.2)) := by
  let framed := (frame rows columns width).compute sizes ⟨arguments.val, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds columns)) sizes framed.1
  have valid : (integerRectangularHermiteAtSize rows columns width Sum.inl (.inr ())).precondition actual
      (fun _ => framed.2.2) := permitted rows columns width sizes arguments.val arguments.property
  exact integerRectangularHermiteAtSize_correct rows columns width Sum.inl (.inr ()) actual
    ⟨fun _ => framed.2.2, valid⟩ arguments.property.choose.1 arguments.property.choose.2

/-- For a supported input, the decoded-rank result retains the full presentation and both bases. -/
theorem integerRectangularHermiteHost_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermiteHost rows columns width).Arguments sizes //
      (integerRectangularHermiteHost rows columns width).precondition sizes arguments})
    (zeroRows : ∀ row, (arguments.val ()).1.val ≤ row.val → (arguments.val ()).2.val row = 0)
    (zeroColumns : ∀ column, (arguments.val ()).1.val ≤ column.val → (arguments.val ()).2.val.transpose column = 0) :
    let result := (integerRectangularHermiteHost rows columns width).compute sizes arguments
    result.2.1.val * (arguments.val ()).2.val * result.2.2.val = result.1.val ∧
      IsUnit result.2.1.val.det ∧ IsUnit result.2.2.val.det := by
  have preserved := IntegerMatrix.rectangularHermiteRun_of_supported arguments.property.choose.1 arguments.property.choose.2
    (MvPolynomial.eval sizes width) (arguments.val ()).2.val zeroRows zeroColumns
  rw [← integerRectangularHermiteHost_correct rows columns width sizes arguments] at preserved
  exact preserved

end Polytime2.Computation
