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

import Polytime2.Matrices.IntegerCompactAtSize
import Polytime2.Computation.ComputedCall

/-! # Compaction at the rank decoded from pivot metadata

The input is a record of pivot metadata, the matrix, and its two bases. The
rank is read internally and bounded by the row count. The computed-size call
returns the three matrices at their original, independent widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def fields
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Fin 4 → EncodedDomain Parameter
  | 0 => hermitePivotSelection rows columns
  | 1 => integerMatrices rows columns matrixWidth
  | 2 => integerMatrices rows rows leftWidth
  | 3 => integerMatrices columns columns rightWidth

private noncomputable def payload
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  (integerMatrices rows columns matrixWidth).prod
    ((integerMatrices rows rows leftWidth).prod (integerMatrices columns columns rightWidth))

private noncomputable def unpack
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : (Parameter ⊕ Unit) → ℕ)
    (value : ((record 4 (fields rows columns matrixWidth leftWidth rightWidth)).renameParameters Sum.inl).Carrier sizes) :
    (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())).Arguments sizes :=
  fun name => match name with
    | 0 => value 0 | 1 => value 1 | 2 => value 2 | 3 => value 3

private noncomputable def callee
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())).onResults
    (fun _ : Unit => (record 4 (fields rows columns matrixWidth leftWidth rightWidth)).renameParameters Sum.inl)
    (fun sizes arguments => (arguments () 0).1 = sizes (.inr ()))
    (fun name sizes arguments => unpack rows columns matrixWidth leftWidth rightWidth sizes (arguments.val ()) name)
    (by intro sizes arguments; exact arguments.property)

private theorem callee_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (callee rows columns matrixWidth leftWidth rightWidth).Realizable := by
  apply (integerCompactAtSizeOriginal_realizable rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())).onResults
    (fun _ : Unit => (record 4 (fields rows columns matrixWidth leftWidth rightWidth)).renameParameters Sum.inl)
    (fun sizes arguments => (arguments () 0).1 = sizes (.inr ()))
    (fun name sizes arguments => unpack rows columns matrixWidth leftWidth rightWidth sizes (arguments.val ()) name)
    (by intro sizes arguments; exact arguments.property)
  intro name
  fin_cases name
  · exact (recordProjectionAtNames_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 0
      (Sum.inl : Parameter → Parameter ⊕ Unit)).withPrecondition _ (by intros; trivial)
  · exact (recordProjectionAtNames_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 1
      (Sum.inl : Parameter → Parameter ⊕ Unit)).withPrecondition _ (by intros; trivial)
  · exact (recordProjectionAtNames_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 2
      (Sum.inl : Parameter → Parameter ⊕ Unit)).withPrecondition _ (by intros; trivial)
  · exact (recordProjectionAtNames_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 3
      (Sum.inl : Parameter → Parameter ⊕ Unit)).withPrecondition _ (by intros; trivial)

private noncomputable def bounds (rows : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ := fun _ => rows

private noncomputable def frame
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  (extendedSizeFrame (bounds rows) (record 4 (fields rows columns matrixWidth leftWidth rightWidth))).onResults
    (fun _ : Unit => record 4 (fields rows columns matrixWidth leftWidth rightWidth)) (fun _ _ => True)
    (fun choice _ arguments => match choice with
      | false => fun _ => ⟨(arguments.val () 0).1, Nat.lt_succ_of_le (by
          simpa only [bounds, Fintype.card_fin] using Fintype.card_le_of_injective
            (α := Fin (arguments.val () 0).1) (β := Fin (MvPolynomial.eval _ rows))
            (arguments.val () 0).2.1 (arguments.val () 0).2.1.injective)⟩
      | true => arguments.val ()) (by intros; trivial)

private theorem frame_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (frame rows columns matrixWidth leftWidth rightWidth).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => record 4 (fields rows columns matrixWidth leftWidth rightWidth)
  have rank := (recordProjection_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 0).followedBy
    (hermitePivotSelectionRank_realizable rows columns) rfl (by intros; trivial)
  apply (extendedSizeFrame_realizable (bounds rows) (record 4 (fields rows columns matrixWidth leftWidth rightWidth))).onResults
    context (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · apply Realizable.namedRecordOutputs
    intro name
    cases name
    exact rank
  · exact Realizable.argument context () (fun _ _ => True)

/-- Decode the pivot rank and compact, retaining the computed-size header. -/
noncomputable def integerCompactStoredRank
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  ((callee rows columns matrixWidth leftWidth rightWidth).atComputedUnarySizes (extendedSizeBounds (bounds rows))).onResults
    (frame rows columns matrixWidth leftWidth rightWidth).inputDomains (fun _ _ => True)
    (fun _ sizes arguments => (frame rows columns matrixWidth leftWidth rightWidth).compute sizes ⟨arguments.val, trivial⟩)
    (by intros; rfl)

/-- Rank extraction, framing, and the complete compaction call are polynomial-time. -/
theorem integerCompactStoredRank_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).Realizable := by
  apply ((callee_realizable rows columns matrixWidth leftWidth rightWidth).atComputedUnarySizes
    (extendedSizeBounds (bounds rows))).onResults
    (frame rows columns matrixWidth leftWidth rightWidth).inputDomains (fun _ _ => True) _ (by intros; rfl)
  intro name
  cases name
  exact frame_realizable rows columns matrixWidth leftWidth rightWidth

/-- Compact at the decoded rank and return only the three host matrices. -/
noncomputable def integerCompactHost
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains := (integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).inputDomains
  outputDomain := payload rows columns matrixWidth leftWidth rightWidth
  precondition _ _ := True
  compute sizes arguments := ((integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).compute sizes arguments).2

/-- Project away the internal header through its canonical host-frame view. -/
theorem integerCompactHost_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerCompactHost rows columns matrixWidth leftWidth rightWidth).Realizable := by
  let output := payload rows columns matrixWidth leftWidth rightWidth
  let index := computedSizeDomain (extendedSizeBounds (bounds rows))
  let computation := integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth
  have viewed := (integerCompactStoredRank_realizable rows columns matrixWidth leftWidth rightWidth).withEncodedOutput
    (index.prod output)
    (fun sizes arguments => let result := computation.compute sizes arguments; (result.1, result.2)) (by
      intro sizes
      change MvPolynomial.eval sizes (index.widthPolynomial + output.widthPolynomial) =
        MvPolynomial.eval sizes (index.widthPolynomial + SizeSubstitution.polynomial (extendedSizeBounds (bounds rows))
          (output.renameParameters (Sum.inl : Parameter → Parameter ⊕ Unit)).widthPolynomial)
      rw [extendedSize_payloadWidth]) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      let counts : (computedSizeDomain (bounds rows)).Carrier sizes := fun _ =>
        ⟨(arguments.val () 0).1, Nat.lt_succ_of_le (by
          simpa only [bounds, Fintype.card_fin] using Fintype.card_le_of_injective
            (α := Fin (arguments.val () 0).1) (β := Fin (MvPolynomial.eval sizes rows))
            (arguments.val () 0).2.1 (arguments.val () 0).2.1.injective)⟩
      exact (extendedSizeFrame_encode_bits (bounds rows) output sizes counts
        (computation.compute sizes arguments).2).symm)
  exact viewed.followedBy (pairProjection_realizable index output true) rfl (by intros; trivial)

/-- The internal call uses precisely the rank stored in the input metadata. -/
theorem integerCompactStoredRank_count
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).Arguments sizes //
      (integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).precondition sizes arguments}) :
    (((integerCompactStoredRank rows columns matrixWidth leftWidth rightWidth).compute sizes arguments).1 (.inr ())).val =
      (arguments.val () 0).1 := rfl

/-- Automatic-rank compaction is exactly the host mathematical permutation action. -/
theorem integerCompactHost_correct
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHost rows columns matrixWidth leftWidth rightWidth).Arguments sizes //
      (integerCompactHost rows columns matrixWidth leftWidth rightWidth).precondition sizes arguments}) :
    let result := (integerCompactHost rows columns matrixWidth leftWidth rightWidth).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.permuteWithBases (IntegerMatrix.pivotPermutation (arguments.val () 0).2.1)
        (IntegerMatrix.pivotPermutation (arguments.val () 0).2.2)
        (arguments.val () 1).val (arguments.val () 2).val (arguments.val () 3).val := by
  let framed := (frame rows columns matrixWidth leftWidth rightWidth).compute sizes ⟨arguments.val, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds rows)) sizes framed.1
  let values := unpack rows columns matrixWidth leftWidth rightWidth actual framed.2
  exact integerCompactAtSizeOriginal_correct rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())
    actual ⟨values, rfl⟩

/-- Compaction preserves the accumulated presentation and both unit determinants. -/
theorem integerCompactHost_preserves
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHost rows columns matrixWidth leftWidth rightWidth).Arguments sizes //
      (integerCompactHost rows columns matrixWidth leftWidth rightWidth).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val () 2).val * original * (arguments.val () 3).val = (arguments.val () 1).val)
    (leftUnit : IsUnit (arguments.val () 2).val.det)
    (rightUnit : IsUnit (arguments.val () 3).val.det) :
    let result := (integerCompactHost rows columns matrixWidth leftWidth rightWidth).compute sizes arguments
    result.2.1.val * original * result.2.2.val = result.1.val ∧
      IsUnit result.2.1.val.det ∧ IsUnit result.2.2.val.det := by
  have preserved := IntegerMatrix.permuteWithBases_preserves
    (IntegerMatrix.pivotPermutation (arguments.val () 0).2.1)
    (IntegerMatrix.pivotPermutation (arguments.val () 0).2.2)
    (arguments.val () 1).val original (arguments.val () 2).val (arguments.val () 3).val
    equation leftUnit rightUnit
  rw [← integerCompactHost_correct rows columns matrixWidth leftWidth rightWidth sizes arguments] at preserved
  exact preserved

end Polytime2.Computation
