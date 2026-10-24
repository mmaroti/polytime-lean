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

import Polytime2.Matrices.IntegerCompactHermiteInitial
import Polytime2.Matrices.IntegerRectangularHermiteStoredRank

/-! # Complete rectangular Hermite reduction with accumulated bases

Initialize an arbitrary bounded integer matrix, reduce at the decoded active
rank, and compose both actual bases. The input has no additional precondition;
all ranks, widths, and iteration budgets are derived internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def initialWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  IntegerMatrix.hermiteInitialWidth rows columns width
private noncomputable def resultWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  rectangularHermiteOutputWidth rows (initialWidth rows columns width)
private noncomputable def leftWidth (rows width : MvPolynomial Parameter ℕ) := rows + 1 + hermiteRowsWorkspace width rows
private noncomputable def rightWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  columns + 1 + hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns

private theorem permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteInitial rows columns width).Arguments sizes //
      (integerCompactHermiteInitial rows columns width).precondition sizes arguments}) :
    (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).precondition sizes
      (fun _ => let result := (integerCompactHermiteInitial rows columns width).compute sizes arguments; (result.1, result.2.1)) := by
  have invariant := integerCompactHermiteInitial_specification rows columns width sizes arguments
  obtain ⟨columnBound, rowBound, zeroColumns, upper, positive, reduced⟩ := invariant.2.2.2.1
  apply integerRectangularHermiteHost_permitted rows columns (initialWidth rows columns width) sizes _ rowBound columnBound
  · exact upper.transpose
  · exact positive

private noncomputable def reduce (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).onResults
    (integerCompactHermiteInitial rows columns width).inputDomains (integerCompactHermiteInitial rows columns width).precondition
    (fun _ sizes arguments => let result := (integerCompactHermiteInitial rows columns width).compute sizes arguments; (result.1, result.2.1))
    (fun sizes arguments => permitted rows columns width sizes arguments)

private theorem reduce_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (reduce rows columns width).Realizable := by
  let computation := reduce rows columns width
  have actual := integerCompactHermiteInitial_realizable rows columns width
  have rank := actual.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have matrix := (actual.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)).followedBy
    (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have prepared := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ rank matrix
  apply (integerRectangularHermiteHost_realizable rows columns (initialWidth rows columns width)).onResults
    computation.inputDomains computation.precondition _ (fun sizes arguments => permitted rows columns width sizes arguments)
  intro singleton
  cases singleton
  exact prepared

/-- Arbitrary signed rectangular reduction with decoded rank and both accumulated bases. -/
noncomputable def integerHermiteReduction (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerCompactHermiteInitial rows columns width).inputDomains
  outputDomain := (boundedUnary columns).prod
    ((integerMatrices rows columns (resultWidth rows columns width)).prod
      ((integerMatrices rows rows (rows + resultWidth rows columns width + leftWidth rows width)).prod
        (integerMatrices columns columns (columns + rightWidth rows columns width + resultWidth rows columns width))))
  precondition _ _ := True
  compute sizes arguments :=
    let first := (integerCompactHermiteInitial rows columns width).compute sizes arguments
    let second := (reduce rows columns width).compute sizes arguments
    let bases := (integerBasisCompose rows columns (leftWidth rows width) (rightWidth rows columns width)
      (resultWidth rows columns width) (resultWidth rows columns width)).compute sizes
      ⟨(fun name => match name with | 0 => first.2.2.1 | 1 => first.2.2.2 | 2 => second.2.1 | 3 => second.2.2), trivial⟩
    (first.1, second.1, bases)

/-- Initial stabilization, decoded-rank reduction, and both accumulated products are realized. -/
theorem integerHermiteReduction_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteReduction rows columns width).Realizable := by
  let computation := integerHermiteReduction rows columns width
  have first := integerCompactHermiteInitial_realizable rows columns width
  have second := reduce_realizable rows columns width
  have rank := first.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have matrix := second.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldBases := (first.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)).followedBy
    (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have newBases := second.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have oldLeft := oldBases.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have oldRight := oldBases.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have newLeft := newBases.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
  have newRight := newBases.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
  have bases := (integerBasisCompose_realizable rows columns (leftWidth rows width) (rightWidth rows columns width)
    (resultWidth rows columns width) (resultWidth rows columns width)).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments =>
      let first := (integerCompactHermiteInitial rows columns width).compute sizes arguments
      let second := (reduce rows columns width).compute sizes arguments
      match name with | 0 => first.2.2.1 | 1 => first.2.2.2 | 2 => second.2.1 | 3 => second.2.2)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact oldLeft
      · exact oldRight
      · exact newLeft
      · exact newRight)
  have full := Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ matrix bases
  exact Realizable.pairOutputs computation.inputDomains _ _ computation.precondition _ _ rank full

private theorem supportedPresentation (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (first : ((integerRectangularHermiteHost rows columns width).inputDomains ()).Carrier sizes)
    (valid : (integerRectangularHermiteHost rows columns width).precondition sizes
      (fun _ => first))
    (shape : IntegerMatrix.IsCompactRowHermite first.1.val first.2.val.transpose)
    (zeroRows : ∀ row, first.1.val ≤ row.val → first.2.val row = 0) :
    let second := (integerRectangularHermiteHost rows columns width).compute sizes
      ⟨fun _ => first, valid⟩
    second.2.1.val * first.2.val * second.2.2.val = second.1.val ∧
      IsUnit second.2.1.val.det ∧ IsUnit second.2.2.val.det := by
  obtain ⟨columnBound, rowBound, zeroColumns, upper, positive, reduced⟩ := shape
  have preserved := integerRectangularHermiteHost_preserves rows columns width sizes
    ⟨fun _ => first, valid⟩ zeroRows zeroColumns
  exact preserved

private theorem reduce_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerCompactHermiteInitial rows columns width).Arguments sizes //
      (integerCompactHermiteInitial rows columns width).precondition sizes arguments}) :
    let first := (integerCompactHermiteInitial rows columns width).compute sizes arguments
    let second := (reduce rows columns width).compute sizes arguments
    second.2.1.val * first.2.1.val * second.2.2.val = second.1.val ∧
      IsUnit second.2.1.val.det ∧ IsUnit second.2.2.val.det := by
  let first := (integerCompactHermiteInitial rows columns width).compute sizes arguments
  let pair : ((integerRectangularHermiteHost rows columns (initialWidth rows columns width)).inputDomains ()).Carrier sizes :=
    (first.1, first.2.1)
  have valid : (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).precondition sizes (fun _ => pair) :=
    permitted rows columns width sizes arguments
  have invariant := integerCompactHermiteInitial_specification rows columns width sizes arguments
  have shape : IntegerMatrix.IsCompactRowHermite pair.1.val pair.2.val.transpose := invariant.2.2.2.1
  have zeroRows : ∀ row, pair.1.val ≤ row.val → pair.2.val row = 0 := invariant.2.2.2.2
  have preserved := supportedPresentation rows columns (initialWidth rows columns width) sizes pair valid shape zeroRows
  have equation : (reduce rows columns width).compute sizes arguments =
      (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).compute sizes ⟨fun _ => pair, valid⟩ := by
    dsimp only [reduce, Computation.onResults]
  dsimp only
  rw [equation]
  exact preserved

/-- The complete rectangular reduction preserves the presentation and both unit determinants. -/
theorem integerHermiteReduction_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteReduction rows columns width).Arguments sizes //
      (integerHermiteReduction rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteReduction rows columns width).compute sizes arguments
    result.2.2.1.val * (arguments.val ()).val * result.2.2.2.val = result.2.1.val ∧
      IsUnit result.2.2.1.val.det ∧ IsUnit result.2.2.2.val.det := by
  have first := integerCompactHermiteInitial_specification rows columns width sizes arguments
  have second := reduce_preserves rows columns width sizes arguments
  dsimp only at first second
  refine ⟨?_, ?_, ?_⟩
  · change ((_ * _) * (arguments.val ()).val * (_ * _)) = _
    calc
      _ = ((reduce rows columns width).compute sizes arguments).2.1.val *
          (((integerCompactHermiteInitial rows columns width).compute sizes arguments).2.2.1.val *
            (arguments.val ()).val * ((integerCompactHermiteInitial rows columns width).compute sizes arguments).2.2.2.val) *
          ((reduce rows columns width).compute sizes arguments).2.2.val := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [first.1]; exact second.1
  · change IsUnit ((((reduce rows columns width).compute sizes arguments).2.1.val *
      ((integerCompactHermiteInitial rows columns width).compute sizes arguments).2.2.1.val).det)
    rw [Matrix.det_mul]
    exact second.2.1.mul first.2.1
  · change IsUnit ((((integerCompactHermiteInitial rows columns width).compute sizes arguments).2.2.2.val *
      ((reduce rows columns width).compute sizes arguments).2.2.val).det)
    rw [Matrix.det_mul]
    exact first.2.2.1.mul second.2.2

/-- The decoded active rank fits both mathematical dimensions. -/
theorem integerHermiteReduction_dimensions (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteReduction rows columns width).Arguments sizes //
      (integerHermiteReduction rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteReduction rows columns width).compute sizes arguments
    result.1.val ≤ MvPolynomial.eval sizes rows ∧ result.1.val ≤ MvPolynomial.eval sizes columns := by
  have initial := integerCompactHermiteInitial_specification rows columns width sizes arguments
  exact ⟨initial.2.2.2.1.2.1, initial.2.2.2.1.1⟩

/-- The returned rank is the ordinary integer matrix rank. -/
theorem integerHermiteReduction_rank (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteReduction rows columns width).Arguments sizes //
      (integerHermiteReduction rows columns width).precondition sizes arguments}) :
    ((integerHermiteReduction rows columns width).compute sizes arguments).1.val = (arguments.val ()).val.rank :=
  integerCompactHermiteInitial_rank rows columns width sizes arguments

private theorem diagonalAtState (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (first : (integerCompactHermiteInitial rows columns width).outputDomain.Carrier sizes)
    (valid : (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).precondition sizes
      (fun _ => (first.1, first.2.1))) :
    let second := (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).compute sizes
      ⟨fun _ => (first.1, first.2.1), valid⟩
    ∃ diagonal : Fin first.1.val → ℕ, (∀ index, 0 < diagonal index) ∧
      second.1.val = IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal := by
  let hostArguments : (integerRectangularHermiteHost rows columns (initialWidth rows columns width)).Arguments sizes :=
    fun _ => (first.1, first.2.1)
  let within := valid.choose
  let block := first.2.1.val.submatrix (Fin.castLE within.1) (Fin.castLE within.2)
  let budget := MvPolynomial.eval sizes (initialWidth rows columns width) * first.1.val * first.1.val + 2
  let square := IntegerMatrix.hermiteAlternatingRun budget block
  let diagonal := fun index => (square.1 index index).natAbs
  have shape := IntegerMatrix.hermiteAlternatingRun_triangular budget block valid.choose_spec.1 valid.choose_spec.2
  have full := IntegerMatrix.rectangularHermiteRun_diagonal within.1 within.2
    (MvPolynomial.eval sizes (initialWidth rows columns width)) block valid.choose_spec.1 valid.choose_spec.2
    (fun row column => first.2.1.property _ _)
  have same := congrArg Prod.fst (integerRectangularHermiteHost_correct rows columns (initialWidth rows columns width) sizes
    ⟨hostArguments, valid⟩)
  refine ⟨diagonal, ?_, same.trans full⟩
  intro index
  exact Int.natAbs_pos.mpr (ne_of_gt (shape.2 index))

/-- The full output matrix is a positive active diagonal with zero inactive entries. -/
theorem integerHermiteReduction_diagonal (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteReduction rows columns width).Arguments sizes //
      (integerHermiteReduction rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteReduction rows columns width).compute sizes arguments
    ∃ diagonal : Fin result.1.val → ℕ, (∀ index, 0 < diagonal index) ∧
      result.2.1.val = IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal :=
  diagonalAtState rows columns width sizes ((integerCompactHermiteInitial rows columns width).compute sizes arguments)
    (permitted rows columns width sizes arguments)

end Polytime2.Computation
