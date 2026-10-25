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

import Polytime2.Computation.Specification
import Polytime2.Matrices.IntegerCompactHermiteColumns
import Polytime2.Matrices.IntegerBasisCompose
import Polytime2.Matrices.HermiteStabilizationMath

/-! # Certified initial Hermite stabilization

Run compact row normalization and then compact column normalization, retaining
both actual bases by matrix multiplication. Arbitrary signed rectangular input
is admitted. All output widths are derived from the original dimensions and
entry width; the result has zero inactive rows and columns.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def firstPass (rows columns width : MvPolynomial Parameter ℕ) :=
  integerCompactHermiteRows rows columns width

private noncomputable def secondPass (rows columns width : MvPolynomial Parameter ℕ) :=
  integerCompactHermiteColumns rows columns (hermiteRowsWorkspace width rows)

private noncomputable def runSecond (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (pairProjection (boundedUnary rows)
    ((integerMatrices rows columns (hermiteRowsWorkspace width rows)).prod
      ((integerMatrices rows rows (hermiteRowsWorkspace width rows)).prod (integerMatrices columns columns 1))) true).followedBy
    ((pairProjection (integerMatrices rows columns (hermiteRowsWorkspace width rows))
      ((integerMatrices rows rows (hermiteRowsWorkspace width rows)).prod (integerMatrices columns columns 1)) false).followedBy
      (secondPass rows columns width) rfl (by intros; trivial)) rfl (by intros; trivial)

private theorem runSecond_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (runSecond rows columns width).Realizable := by
  exact (pairProjection_realizable _ _ true).followedBy
    ((pairProjection_realizable _ _ false).followedBy
      (integerCompactHermiteColumns_realizable rows columns (hermiteRowsWorkspace width rows))
      rfl (by intros; trivial)) rfl (by intros; trivial)

private noncomputable def pairedPasses (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  Computation.mk (fun _ => (firstPass rows columns width).outputDomain)
    ((firstPass rows columns width).outputDomain.prod (secondPass rows columns width).outputDomain)
    (fun _ _ => True) (fun sizes arguments =>
      (arguments.val (), (runSecond rows columns width).compute sizes arguments))

private theorem pairedPasses_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (pairedPasses rows columns width).Realizable :=
  (Realizable.argument (fun _ : Unit => (firstPass rows columns width).outputDomain) () (fun _ _ => True)).prodMk (runSecond_realizable rows columns width)

private noncomputable def initialProducts (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (pairedPasses rows columns width).outputDomain
  outputDomain := (boundedUnary columns).prod
    ((integerMatrices rows columns (hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns)).prod
      ((integerMatrices rows rows (rows + 1 + hermiteRowsWorkspace width rows)).prod
        (integerMatrices columns columns (columns + 1 + hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns))))
  precondition _ _ := True
  compute sizes arguments :=
    let first := (arguments.val ()).1
    let second := (arguments.val ()).2
    (second.1, second.2.1,
      (integerMatrixMultiply rows rows rows 1 (hermiteRowsWorkspace width rows)).compute sizes
        ⟨fun choice => match choice with | false => second.2.2.1 | true => first.2.2.1, trivial⟩,
      (integerMatrixMultiply columns columns columns 1 (hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns)).compute sizes
        ⟨fun choice => match choice with | false => first.2.2.2 | true => second.2.2.2, trivial⟩)

private theorem initialProducts_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (initialProducts rows columns width).Realizable := by
  let context := (initialProducts rows columns width).inputDomains
  let oldDomain := (firstPass rows columns width).outputDomain
  let newDomain := (secondPass rows columns width).outputDomain
  have first := pairProjection_realizable oldDomain newDomain false
  have second := pairProjection_realizable oldDomain newDomain true
  have oldMatrices := first.snd
  have newMatrices := second.snd
  have oldBases := oldMatrices.snd
  have newBases := newMatrices.snd
  have oldLeft := oldBases.fst
  have oldRight := oldBases.snd
  have newLeft := newBases.fst
  have newRight := newBases.snd
  have bases := (integerBasisCompose_realizable rows columns (hermiteRowsWorkspace width rows) 1 1
    (hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns)).onResults context (fun _ _ => True)
    (fun name _ arguments => match name with
      | 0 => (arguments.val ()).1.2.2.1 | 1 => (arguments.val ()).1.2.2.2
      | 2 => (arguments.val ()).2.2.2.1 | 3 => (arguments.val ()).2.2.2.2)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact oldLeft
      · exact oldRight
      · exact newLeft
      · exact newRight)
  have rank := second.fst
  have matrix := newMatrices.fst
  have matrices := matrix.prodMk bases
  exact rank.prodMk matrices

/-- Initial row and column stabilization, with both accumulated unimodular bases. -/
private noncomputable def initialRaw (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((firstPass rows columns width).followedBy (pairedPasses rows columns width) rfl (by intros; trivial)).followedBy
    (initialProducts rows columns width) rfl (by intros; trivial)

/-- Both compact passes and both basis products are polynomial-time realizable. -/
private theorem initialRaw_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (initialRaw rows columns width).Realizable :=
  ((integerCompactHermiteRows_realizable rows columns width).followedBy
    (pairedPasses_realizable rows columns width) rfl (by intros; trivial)).followedBy
    (initialProducts_realizable rows columns width) rfl (by intros; trivial)

/-- Runtime initialization equals the mathematical two-pass construction. -/
private theorem initialRaw_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (initialRaw rows columns width).Arguments sizes //
      (initialRaw rows columns width).precondition sizes arguments}) :
    let result := (initialRaw rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteInitial (arguments.val ()).val := by
  let first := (integerCompactHermiteRows rows columns width).compute sizes arguments
  have firstCorrect := integerCompactHermiteRows_correct rows columns width sizes arguments
  have secondCorrect := integerCompactHermiteColumns_correct rows columns (hermiteRowsWorkspace width rows)
    sizes ⟨fun _ => first.2.1, trivial⟩
  dsimp only [IntegerMatrix.compactHermiteInitial]
  rw [← firstCorrect]
  dsimp only
  change _ = (_, (IntegerMatrix.compactHermiteColumns first.2.1.val).2.1,
    (IntegerMatrix.compactHermiteColumns first.2.1.val).2.2.1 * first.2.2.1.val,
    first.2.2.2.val * (IntegerMatrix.compactHermiteColumns first.2.1.val).2.2.2)
  rw [← secondCorrect]
  rfl

private theorem initialEntryFits (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (initialRaw rows columns width).Arguments sizes //
      (initialRaw rows columns width).precondition sizes arguments}) :
    ∀ row column, (((initialRaw rows columns width).compute sizes arguments).2.1.val row column).natAbs <
      2 ^ MvPolynomial.eval sizes (IntegerMatrix.hermiteInitialWidth rows columns width) := by
  have bounded := IntegerMatrix.compactHermiteInitial_bound (MvPolynomial.eval sizes width)
    (arguments.val ()).val (arguments.val ()).property
  rw [← initialRaw_correct rows columns width sizes arguments] at bounded
  simpa [IntegerMatrix.hermiteInitialWidth] using bounded.1

/-- Initial stabilization at the mathematical entry width, with both accumulated bases. -/
private noncomputable def implementation (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (initialRaw rows columns width).inputDomains
  outputDomain := (boundedUnary columns).prod
    ((integerMatrices rows columns (IntegerMatrix.hermiteInitialWidth rows columns width)).prod
      ((integerMatrices rows rows (rows + 1 + hermiteRowsWorkspace width rows)).prod
        (integerMatrices columns columns (columns + 1 + hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns))))
  precondition := (initialRaw rows columns width).precondition
  compute sizes arguments :=
    let result := (initialRaw rows columns width).compute sizes arguments
    (result.1, ⟨result.2.1.val, initialEntryFits rows columns width sizes arguments⟩, result.2.2)

/-- Certified stabilization and resizing return the proved mathematical entry width. -/
private theorem implementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (implementation rows columns width).Realizable := by
  let computation := implementation rows columns width
  have actual := initialRaw_realizable rows columns width
  have rank := actual.fst
  have matrices := actual.snd
  have matrix := matrices.fst
  have bases := matrices.snd
  have resized := matrix.followedBy
    (integerMatrixResize_realizable rows columns (hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns)
      (IntegerMatrix.hermiteInitialWidth rows columns width)) rfl (by
        intro sizes arguments valid
        exact initialEntryFits rows columns width sizes ⟨arguments, valid⟩)
  have together := resized.prodMk bases
  exact rank.prodMk together

/-- Returning the mathematical entry width preserves the exact initialization result. -/
private theorem implementation_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation rows columns width).Arguments sizes //
      (implementation rows columns width).precondition sizes arguments}) :
    let result := (implementation rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteInitial (arguments.val ()).val :=
  initialRaw_correct rows columns width sizes arguments

/-- The ordinary compact initial presentation, with rank and both actual bases.
The two passes, their products, and result resizing stay behind the boundary. -/
noncomputable def integerCompactHermiteInitial (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  specificationBy (fun _ => integerMatrices rows columns width)
    ((boundedUnary columns).prod
      ((integerMatrices rows columns (IntegerMatrix.hermiteInitialWidth rows columns width)).prod
        ((integerMatrices rows rows (rows + 1 + hermiteRowsWorkspace width rows)).prod
          (integerMatrices columns columns (columns + 1 + hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns)))))
    (fun _ _ => True)
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val))
    (fun _ arguments => IntegerMatrix.compactHermiteInitial (arguments.val ()).val)
    (fun sizes arguments => ⟨(implementation rows columns width).compute sizes arguments,
      implementation_correct rows columns width sizes arguments⟩)

theorem integerCompactHermiteInitial_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerCompactHermiteInitial rows columns width).Realizable := by
  apply (implementation_realizable rows columns width).specificationBy
  · intro sizes
    exact Fin.val_injective.prodMap
      (Subtype.val_injective.prodMap (Subtype.val_injective.prodMap Subtype.val_injective))
  · intro sizes arguments valid
    exact implementation_correct rows columns width sizes ⟨arguments, valid⟩

/-- Observe the exact mathematical initial presentation without resizing or tape preparation. -/
theorem integerCompactHermiteInitial_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteInitial rows columns width).Arguments sizes //
      (integerCompactHermiteInitial rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteInitial rows columns width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val) =
      IntegerMatrix.compactHermiteInitial (arguments.val ()).val := by
  exact specificationBy_correct _ (integerCompactHermiteInitial rows columns width).outputDomain _
    (fun _ result => (result.1.val, result.2.1.val, result.2.2.1.val, result.2.2.2.val)) _ _ sizes arguments

/-- Initialization retains the presentation, both unit determinants, and both inactive strips. -/
theorem integerCompactHermiteInitial_specification (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteInitial rows columns width).Arguments sizes //
      (integerCompactHermiteInitial rows columns width).precondition sizes arguments}) :
    let result := (integerCompactHermiteInitial rows columns width).compute sizes arguments
    result.2.2.1.val * (arguments.val ()).val * result.2.2.2.val = result.2.1.val ∧
      IsUnit result.2.2.1.val.det ∧ IsUnit result.2.2.2.val.det ∧
      IntegerMatrix.IsCompactRowHermite result.1.val result.2.1.val.transpose ∧
      (∀ row, result.1.val ≤ row.val → result.2.1.val row = 0) := by
  have correct := IntegerMatrix.compactHermiteInitial_correct (arguments.val ()).val
  rw [← integerCompactHermiteInitial_correct rows columns width sizes arguments] at correct
  exact correct

/-- The returned active dimension is the ordinary integer matrix rank. -/
theorem integerCompactHermiteInitial_rank (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteInitial rows columns width).Arguments sizes //
      (integerCompactHermiteInitial rows columns width).precondition sizes arguments}) :
    ((integerCompactHermiteInitial rows columns width).compute sizes arguments).1.val =
      (arguments.val ()).val.rank := by
  have correct := IntegerMatrix.compactHermiteInitial_rank (arguments.val ()).val
  rw [← integerCompactHermiteInitial_correct rows columns width sizes arguments] at correct
  exact correct

end Polytime2.Computation
