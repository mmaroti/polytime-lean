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

import Polytime2.Matrices.IntegerRectangularCleanupAtSize
import Polytime2.Computation.ComputedCall

/-! # Divisibility cleanup at the decoded active rank

The input pairs the mathematical rank with the positive rectangular diagonal.
Read the rank internally, invoke the named-rank cleanup, and discard the
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
  (integerMatrices rows columns (rectangularCleanupOutputWidth rows width)).prod
    ((integerMatrices rows rows (rectangularCleanupOutputWidth rows width)).prod
      (integerMatrices columns columns (rectangularCleanupOutputWidth rows width)))

private noncomputable def bounds (columns : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ := fun _ => columns

private noncomputable def callee (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerRectangularCleanupAtSize rows columns width Sum.inl (.inr ())).onResults
    (fun _ : Unit => (input rows columns width).renameParameters Sum.inl)
    (fun sizes arguments => (integerRectangularCleanupAtSize rows columns width Sum.inl (.inr ())).precondition sizes
      (fun _ => (arguments ()).2))
    (fun _ _ arguments => (arguments.val ()).2) (by intro sizes arguments; exact arguments.property)

private theorem callee_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (callee rows columns width).Realizable := by
  apply (integerRectangularCleanupAtSize_realizable rows columns width Sum.inl (.inr ())).onResults
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
  ∃ _within : (arguments ()).1.val ≤ MvPolynomial.eval sizes rows ∧
      (arguments ()).1.val ≤ MvPolynomial.eval sizes columns,
    ∃ diagonal : Fin (arguments ()).1.val → ℕ, (∀ index, 0 < diagonal index) ∧
      (arguments ()).2.val = IntegerMatrix.rectangularDiagonal
        (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal

private noncomputable def call (rows columns width : MvPolynomial Parameter ℕ) :=
  (callee rows columns width).atComputedUnarySizes (extendedSizeBounds (bounds columns))

private theorem permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (input rows columns width).Carrier sizes) (valid : allowed rows columns width sizes arguments) :
    (call rows columns width).precondition sizes
      (fun _ => (frame rows columns width).compute sizes ⟨arguments, trivial⟩) := by
  obtain ⟨within, diagonal, positive, equation⟩ := valid
  let framed := (frame rows columns width).compute sizes ⟨arguments, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds columns)) sizes framed.1
  change (integerRectangularCleanupAtSize rows columns width Sum.inl (.inr ())).precondition actual (fun _ => framed.2.2)
  exact integerRectangularCleanupAtSize_permitted rows columns width Sum.inl (.inr ()) actual
    (fun _ => framed.2.2) within.1 within.2 diagonal positive equation

/-- Decode the active rank and clean divisibility, retaining the internal computed-size header. -/
noncomputable def integerRectangularCleanupStoredRank (rows columns width : MvPolynomial Parameter ℕ) :=
  (call rows columns width).onResults (frame rows columns width).inputDomains (allowed rows columns width)
    (fun _ sizes arguments => (frame rows columns width).compute sizes ⟨arguments.val, trivial⟩)
    (fun sizes arguments => permitted rows columns width sizes arguments.val arguments.property)

/-- Rank reading, size preparation, and the complete stored-rank call are realized. -/
theorem integerRectangularCleanupStoredRank_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanupStoredRank rows columns width).Realizable := by
  apply ((callee_realizable rows columns width).atComputedUnarySizes (extendedSizeBounds (bounds columns))).onResults
    (frame rows columns width).inputDomains (allowed rows columns width) _
    (fun sizes arguments => permitted rows columns width sizes arguments.val arguments.property)
  intro singleton
  cases singleton
  exact (frame_realizable rows columns width).withPrecondition _ (by intros; trivial)

/-- Clean divisibility at the decoded rank and return only the three full host matrices. -/
noncomputable def integerRectangularCleanupHost (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerRectangularCleanupStoredRank rows columns width).inputDomains
  outputDomain := payload rows columns width
  precondition := allowed rows columns width
  compute sizes arguments := ((integerRectangularCleanupStoredRank rows columns width).compute sizes arguments).2

/-- The canonical host-frame view removes the internal size header without changing payload bits. -/
theorem integerRectangularCleanupHost_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanupHost rows columns width).Realizable := by
  let output := payload rows columns width
  let index := computedSizeDomain (extendedSizeBounds (bounds columns))
  let computation := integerRectangularCleanupStoredRank rows columns width
  have viewed := (integerRectangularCleanupStoredRank_realizable rows columns width).withEncodedOutput
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
theorem integerRectangularCleanupStoredRank_count (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanupStoredRank rows columns width).Arguments sizes //
      (integerRectangularCleanupStoredRank rows columns width).precondition sizes arguments}) :
    (((integerRectangularCleanupStoredRank rows columns width).compute sizes arguments).1 (.inr ())).val =
      (arguments.val ()).1.val := rfl

/-- Only mathematical rank bounds and a positive rectangular diagonal are required. -/
theorem integerRectangularCleanupHost_permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularCleanupHost rows columns width).Arguments sizes)
    (rowBound : (arguments ()).1.val ≤ MvPolynomial.eval sizes rows)
    (columnBound : (arguments ()).1.val ≤ MvPolynomial.eval sizes columns)
    (diagonal : Fin (arguments ()).1.val → ℕ) (positive : ∀ index, 0 < diagonal index)
    (equation : (arguments ()).2.val = IntegerMatrix.rectangularDiagonal
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal) :
    (integerRectangularCleanupHost rows columns width).precondition sizes arguments :=
  ⟨⟨rowBound, columnBound⟩, diagonal, positive, equation⟩

/-- The stored-rank cleanup returns a full Smith form for the supplied host matrix. -/
theorem integerRectangularCleanupHost_isSmithForm (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanupHost rows columns width).Arguments sizes //
      (integerRectangularCleanupHost rows columns width).precondition sizes arguments}) :
    let result := (integerRectangularCleanupHost rows columns width).compute sizes arguments
    IntegerMatrix.IsSmithForm (arguments.val ()).2.val result.1.val result.2.1.val result.2.2.val
      (arguments.val ()).1.val := by
  let framed := (frame rows columns width).compute sizes ⟨arguments.val, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds columns)) sizes framed.1
  have valid : (integerRectangularCleanupAtSize rows columns width Sum.inl (.inr ())).precondition actual
      (fun _ => framed.2.2) := permitted rows columns width sizes arguments.val arguments.property
  have form := integerRectangularCleanupAtSize_isSmithForm rows columns width Sum.inl (.inr ()) actual
    ⟨fun _ => framed.2.2, valid⟩
  exact form

end Polytime2.Computation
