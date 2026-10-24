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
import Polytime2.Computation.ComputedHost

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

private noncomputable def callee (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  (integerCompactAtSizeOriginal rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())).withRenamedRecordArgument
    (fields rows columns matrixWidth leftWidth rightWidth) Sum.inl (by intro name; fin_cases name <;> rfl)

private theorem callee_realizable (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (callee rows columns matrixWidth leftWidth rightWidth).Realizable :=
  (integerCompactAtSizeOriginal_realizable rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())).withRenamedRecordArgument
    (fields rows columns matrixWidth leftWidth rightWidth) Sum.inl (by intro name; fin_cases name <;> rfl)

private noncomputable def bounds (rows : MvPolynomial Parameter ℕ) : Unit → MvPolynomial Parameter ℕ := fun _ => rows

private noncomputable def counts (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (record 4 (fields rows columns matrixWidth leftWidth rightWidth)).Carrier sizes) : (computedSizeDomain (bounds rows)).Carrier sizes :=
  fun _ => (hermitePivotSelectionRank rows columns).compute sizes ⟨fun _ => value 0, trivial⟩

private noncomputable def frame (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  computedHostFrame (bounds rows) (record 4 (fields rows columns matrixWidth leftWidth rightWidth)) (counts rows columns matrixWidth leftWidth rightWidth)

private theorem readers_realizable (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) (name : Unit) :
    (unaryMap (record 4 (fields rows columns matrixWidth leftWidth rightWidth)) (boundedUnary (bounds rows name)) (fun _ _ => True)
      (fun sizes value => counts rows columns matrixWidth leftWidth rightWidth sizes value.val name)).Realizable := by
  exact (recordProjection_realizable 4 (fields rows columns matrixWidth leftWidth rightWidth) 0).followedBy
    (hermitePivotSelectionRank_realizable rows columns) rfl (by intros; trivial)


/-- Decode the pivot rank and return only the three host matrices. -/
noncomputable def integerCompactHost
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((callee rows columns matrixWidth leftWidth rightWidth).atComputedHostSizes (bounds rows)
    (record 4 (fields rows columns matrixWidth leftWidth rightWidth))
    (payload rows columns matrixWidth leftWidth rightWidth)
    (counts rows columns matrixWidth leftWidth rightWidth) rfl rfl).withPrecondition
    (fun _ _ => True) (by intros; rfl)

/-- Count reading, invocation, and removal of the internal header compose. -/
theorem integerCompactHost_realizable
    (rows columns matrixWidth leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerCompactHost rows columns matrixWidth leftWidth rightWidth).Realizable :=
  ((callee_realizable rows columns matrixWidth leftWidth rightWidth).atComputedHostSizes (bounds rows)
    (record 4 (fields rows columns matrixWidth leftWidth rightWidth))
    (payload rows columns matrixWidth leftWidth rightWidth)
    (counts rows columns matrixWidth leftWidth rightWidth) rfl rfl
    (readers_realizable rows columns matrixWidth leftWidth rightWidth)).withPrecondition _ (by intros; rfl)

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
  simp only [integerCompactHost, Computation.withPrecondition, atComputedHostSizes_compute]
  let framed := (frame rows columns matrixWidth leftWidth rightWidth).compute sizes ⟨arguments.val, trivial⟩
  let actual := computedSizeAssignment (extendedSizeBounds (bounds rows)) sizes framed.1
  let values := unpack rows columns matrixWidth leftWidth rightWidth actual framed.2
  exact integerCompactAtSizeOriginal_correct rows columns matrixWidth leftWidth rightWidth Sum.inl (.inr ())
    actual ⟨values, rfl⟩

end Polytime2.Computation
