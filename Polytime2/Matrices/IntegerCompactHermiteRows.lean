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

import Polytime2.Matrices.IntegerCompactStoredRank
import Polytime2.Matrices.HermiteRowsController
import Polytime2.Matrices.CompactHermiteMath

/-! # Certified complete compact Hermite row pass

The input is an arbitrary bounded integer matrix. Run the complete row sweep,
compact its pivot embeddings, and return its rank, compact matrix, and both
actual bases. All workspace is derived from the input dimensions and width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def compactSweep (rows columns width : MvPolynomial Parameter ℕ) :=
  integerCompactHost rows columns (hermiteRowsWorkspace width rows) (hermiteRowsWorkspace width rows) 1

private noncomputable def sweepContext (rows columns width : MvPolynomial Parameter ℕ) : Unit → EncodedDomain Parameter :=
  fun _ => (integerHermiteRows rows columns width).outputDomain

private noncomputable def sweepFields (rows columns width : MvPolynomial Parameter ℕ) :=
  (compactSweep rows columns width).inputDomains ()

private noncomputable def sweepRecord (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := sweepContext rows columns width
  outputDomain := sweepFields rows columns width
  precondition _ _ := True
  compute _ arguments name := match name with
    | 0 => (arguments.val ()).2
    | 1 => (arguments.val ()).1.1
    | 2 => (arguments.val ()).1.2
    | 3 => ⟨1, by intro row column; by_cases same : row = column <;> simp [Matrix.one_apply, same]⟩

private theorem sweepRecord_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (sweepRecord rows columns width).Realizable := by
  let context := sweepContext rows columns width
  let matrix := integerMatrices rows columns (hermiteRowsWorkspace width rows)
  let basis := integerMatrices rows rows (hermiteRowsWorkspace width rows)
  let metadata := hermitePivotSelection rows columns
  have pair := (pairProjection_realizable (matrix.prod basis) metadata false)
  have selected := pairProjection_realizable (matrix.prod basis) metadata true
  apply Realizable.recordOutputs context 4 _ (fun _ _ => True) _
  intro name
  fin_cases name
  · exact selected
  · exact pair.fst
  · exact pair.snd
  · exact (integerIdentity_realizable columns).onResults context (fun _ _ => True)
      (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)

private noncomputable def finishSweep (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  let compacted := (sweepRecord rows columns width).followedBy (compactSweep rows columns width) rfl (by intros; trivial)
  let rank := (pairProjection (integerMatrices rows columns (hermiteRowsWorkspace width rows) |>.prod
    (integerMatrices rows rows (hermiteRowsWorkspace width rows))) (hermitePivotSelection rows columns) true).followedBy
    (hermitePivotSelectionRank rows columns) rfl (by intros; trivial)
  Computation.mk (sweepContext rows columns width) ((boundedUnary rows).prod compacted.outputDomain)
    (fun _ _ => True) (fun sizes arguments => (rank.compute sizes arguments, compacted.compute sizes arguments))

private theorem finishSweep_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (finishSweep rows columns width).Realizable := by
  have compacted := (sweepRecord_realizable rows columns width).followedBy
    (integerCompactHost_realizable rows columns (hermiteRowsWorkspace width rows) (hermiteRowsWorkspace width rows) 1)
    rfl (by intros; trivial)
  have rank := (pairProjection_realizable
    ((integerMatrices rows columns (hermiteRowsWorkspace width rows)).prod
      (integerMatrices rows rows (hermiteRowsWorkspace width rows))) (hermitePivotSelection rows columns) true).followedBy
    (hermitePivotSelectionRank_realizable rows columns) rfl (by intros; trivial)
  exact rank.prodMk compacted

/-- Complete compact row normalization with input-derived workspace and both bases. -/
noncomputable def integerCompactHermiteRows (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (integerHermiteRows rows columns width).followedBy (finishSweep rows columns width) rfl (by intros; trivial)

/-- The whole compact row pass, including rank decoding and basis permutation, is realized. -/
theorem integerCompactHermiteRows_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteRows rows columns width).Realizable :=
  (integerHermiteRows_realizable rows columns width).followedBy (finishSweep_realizable rows columns width)
    rfl (by intros; trivial)

/-- The complete realized pass equals mathematical compact row normalization. -/
theorem integerCompactHermiteRows_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteRows rows columns width).Arguments sizes //
      (integerCompactHermiteRows rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteRows rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteRows (arguments.val ()).val := by
  let swept := (integerHermiteRows rows columns width).compute sizes arguments
  let prepared := (sweepRecord rows columns width).compute sizes ⟨fun _ => swept, trivial⟩
  have compacted := integerCompactHost_correct rows columns (hermiteRowsWorkspace width rows)
    (hermiteRowsWorkspace width rows) 1 sizes ⟨fun _ => prepared, trivial⟩
  have sweepEqual := integerHermiteRows_correct rows columns width sizes arguments
  dsimp only [IntegerMatrix.compactHermiteRows]
  rw [← sweepEqual]
  apply Prod.ext
  · rfl
  · exact compacted

end Polytime2.Computation
