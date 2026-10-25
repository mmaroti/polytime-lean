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

import Polytime2.Matrices.IntegerHermiteReduction
import Polytime2.Matrices.IntegerRectangularCleanupStoredRank

/-! # Complete rectangular Smith reduction with accumulated bases

Hermite-reduce an arbitrary bounded integer matrix, clean its decoded active
diagonal, and compose both actual bases. The input has no additional precondition;
all ranks, widths, and iteration budgets are derived internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def initialWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  rectangularHermiteOutputWidth rows (IntegerMatrix.hermiteInitialWidth rows columns width)
/-- Diagonal entry capacity derived from the original matrix dimensions and width. -/
noncomputable def smithReductionDiagonalWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  rectangularCleanupOutputWidth rows (initialWidth rows columns width)
private noncomputable def leftWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  rows + initialWidth rows columns width + (rows + 1 + hermiteRowsWorkspace width rows)
private noncomputable def rightWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  columns + (columns + 1 + hermiteRowsWorkspace (hermiteRowsWorkspace width rows) columns) +
    initialWidth rows columns width

/-- Left basis capacity derived from the original mathematical input sizes. -/
noncomputable def smithReductionLeftWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  rows + smithReductionDiagonalWidth rows columns width + leftWidth rows columns width

/-- Right basis capacity derived from the original mathematical input sizes. -/
noncomputable def smithReductionRightWidth (rows columns width : MvPolynomial Parameter ℕ) :=
  columns + rightWidth rows columns width + smithReductionDiagonalWidth rows columns width

private theorem permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteReduction rows columns width).Arguments sizes //
      (integerHermiteReduction rows columns width).precondition sizes arguments}) :
    (integerRectangularCleanupHost rows columns (initialWidth rows columns width)).precondition sizes
      (fun _ => let result := (integerHermiteReduction rows columns width).compute sizes arguments; (result.1, result.2.1)) := by
  have dimensions := integerHermiteReduction_dimensions rows columns width sizes arguments
  obtain ⟨diagonal, positive, equation⟩ := integerHermiteReduction_diagonal rows columns width sizes arguments
  exact integerRectangularCleanupHost_permitted rows columns (initialWidth rows columns width) sizes _
    dimensions.1 dimensions.2 diagonal positive equation

private noncomputable def reduce (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerRectangularCleanupHost rows columns (initialWidth rows columns width)).onResults
    (integerHermiteReduction rows columns width).inputDomains (integerHermiteReduction rows columns width).precondition
    (fun _ sizes arguments => let result := (integerHermiteReduction rows columns width).compute sizes arguments; (result.1, result.2.1))
    (fun sizes arguments => permitted rows columns width sizes arguments)

private theorem reduce_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (reduce rows columns width).Realizable := by
  let computation := reduce rows columns width
  have actual := integerHermiteReduction_realizable rows columns width
  apply (integerRectangularCleanupHost_realizable rows columns (initialWidth rows columns width)).onResults
    computation.inputDomains computation.precondition _ (fun sizes arguments => permitted rows columns width sizes arguments)
  intro singleton
  cases singleton
  exact (actual.fst.prodMk ((actual.snd).fst))

private noncomputable def smithOutputDomain (rows columns width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (boundedUnary columns).prod
    ((integerMatrices rows columns (smithReductionDiagonalWidth rows columns width)).prod
      ((integerMatrices rows rows (smithReductionLeftWidth rows columns width)).prod
        (integerMatrices columns columns (smithReductionRightWidth rows columns width))))

private noncomputable def smithValue (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : Unit → (integerMatrices rows columns width).Carrier sizes // True}) :
    (smithOutputDomain rows columns width).Carrier sizes :=
  let first := (integerHermiteReduction rows columns width).compute sizes arguments
  let second := (reduce rows columns width).compute sizes arguments
  let bases := (integerBasisCompose rows columns (leftWidth rows columns width) (rightWidth rows columns width)
    (smithReductionDiagonalWidth rows columns width) (smithReductionDiagonalWidth rows columns width)).compute sizes
    ⟨(fun name => match name with | 0 => first.2.2.1 | 1 => first.2.2.2 | 2 => second.2.1 | 3 => second.2.2), trivial⟩
  (first.1, second.1, bases)

/-- Smith reduction of arbitrary signed rectangular input with rank and both bases. -/
noncomputable def integerSmithReduction (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specification (fun _ => integerMatrices rows columns width) (smithOutputDomain rows columns width) (fun _ _ => True)
    (smithValue rows columns width)

/-- Hermite reduction, decoded-rank cleanup, and both accumulated products are realized. -/
theorem integerSmithReduction_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerSmithReduction rows columns width).Realizable := by
  have first := integerHermiteReduction_realizable rows columns width
  have second := reduce_realizable rows columns width
  have oldBases := (first.snd).snd
  have newBases := second.snd
  have bases := (integerBasisCompose_realizable rows columns (leftWidth rows columns width) (rightWidth rows columns width)
    (smithReductionDiagonalWidth rows columns width) (smithReductionDiagonalWidth rows columns width)).onResults
    (fun _ : Unit => integerMatrices rows columns width) (fun _ _ => True)
    (fun name sizes arguments =>
      let first := (integerHermiteReduction rows columns width).compute sizes arguments
      let second := (reduce rows columns width).compute sizes arguments
      match name with | 0 => first.2.2.1 | 1 => first.2.2.2 | 2 => second.2.1 | 3 => second.2.2)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact oldBases.fst
      · exact oldBases.snd
      · exact newBases.fst
      · exact newBases.snd)
  apply (first.fst.prodMk (second.fst.prodMk bases)).specification (smithValue rows columns width)
  intro sizes arguments valid
  rfl

set_option maxHeartbeats 4000000 in
private theorem cleanup_form (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : Unit → (integerMatrices rows columns width).Carrier sizes // True}) :
    let first := (integerHermiteReduction rows columns width).compute sizes arguments
    let second := (reduce rows columns width).compute sizes arguments
    IntegerMatrix.IsSmithForm first.2.1.val second.1.val second.2.1.val second.2.2.val first.1.val := by
  let first := (integerHermiteReduction rows columns width).compute sizes arguments
  let pair : ((integerRectangularCleanupHost rows columns (initialWidth rows columns width)).inputDomains ()).Carrier sizes :=
    (first.1, first.2.1)
  have valid : (integerRectangularCleanupHost rows columns (initialWidth rows columns width)).precondition sizes (fun _ => pair) :=
    permitted rows columns width sizes arguments
  have form := integerRectangularCleanupHost_isSmithForm rows columns (initialWidth rows columns width) sizes
    ⟨fun _ => pair, valid⟩
  have equation : (reduce rows columns width).compute sizes arguments =
      (integerRectangularCleanupHost rows columns (initialWidth rows columns width)).compute sizes ⟨fun _ => pair, valid⟩ := by
    rfl
  have transported := congrArg
    (fun result : (integerRectangularCleanupHost rows columns (initialWidth rows columns width)).outputDomain.Carrier sizes =>
      IntegerMatrix.IsSmithForm pair.2.val result.1.val result.2.1.val result.2.2.val pair.1.val) equation
  exact transported.mpr form

set_option maxHeartbeats 800000 in
/-- The complete computation returns a Smith diagonal and both actual unimodular bases. -/
theorem integerSmithReduction_isSmithForm (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : Unit → (integerMatrices rows columns width).Carrier sizes // True}) :
    let result := (integerSmithReduction rows columns width).compute sizes arguments
    IntegerMatrix.IsSmithForm (arguments.val ()).val result.2.1.val result.2.2.1.val result.2.2.2.val result.1.val := by
  have first := integerHermiteReduction_preserves rows columns width sizes arguments
  have second := cleanup_form rows columns width sizes arguments
  dsimp only at first second
  have composed := second.of_equation first.1 first.2.1 first.2.2
  simp only [integerSmithReduction, specification_compute, smithValue]
  have bases := integerBasisCompose_correct rows columns (leftWidth rows columns width)
    (rightWidth rows columns width) (smithReductionDiagonalWidth rows columns width)
    (smithReductionDiagonalWidth rows columns width) sizes
    ⟨(fun name => match name with
      | 0 => ((integerHermiteReduction rows columns width).compute sizes arguments).2.2.1
      | 1 => ((integerHermiteReduction rows columns width).compute sizes arguments).2.2.2
      | 2 => ((reduce rows columns width).compute sizes arguments).2.1
      | 3 => ((reduce rows columns width).compute sizes arguments).2.2), trivial⟩
  have left := congrArg Prod.fst bases
  have right := congrArg Prod.snd bases
  dsimp only at left right
  rw [left, right]
  exact composed

set_option maxHeartbeats 800000 in
/-- The returned rank is the rank of the original integer matrix. -/
theorem integerSmithReduction_rank (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : Unit → (integerMatrices rows columns width).Carrier sizes // True}) :
    ((integerSmithReduction rows columns width).compute sizes arguments).1.val = (arguments.val ()).val.rank := by
  simpa only [integerSmithReduction, specification_compute, smithValue] using
    integerHermiteReduction_rank rows columns width sizes arguments

end Polytime2.Computation
