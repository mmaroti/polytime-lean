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

import Polytime2.Matrices.IntegerHermiteDiagonalize
import Polytime2.Matrices.ExtendIntegerBasis
import Polytime2.Matrices.RectangularPresentation
import Polytime2.Matrices.RectangularHermiteMath
import Polytime2.Arrays.BoundedPositions

/-! # Lifting square Hermite diagonalization to a rectangular presentation

Diagonalize the active square matrix, build its full rectangular diagonal, and
extend both actual bases by identities. The mathematical rank fits both output
dimensions. All result widths are derived from that rank and the input width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Read the magnitudes of a square matrix's diagonal into its canonical natural array. -/
noncomputable def integerMatrixDiagonalMagnitudes (rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  arrayTabulate (fun _ : Unit => integerMatrices rank rank width) (binaryNaturalsOfWidth width) rank
    (fun _ arguments index => ⟨((arguments ()).val index index).natAbs, (arguments ()).property index index⟩)

/-- Diagonal reading uses existing coordinate conversion, entry lookup, and magnitude. -/
theorem integerMatrixDiagonalMagnitudes_realizable (rank width : MvPolynomial Parameter ℕ) :
    (integerMatrixDiagonalMagnitudes rank width).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => integerMatrices rank rank width
  let operation sizes (arguments : ∀ name, (context name).Carrier sizes) (index : Fin (MvPolynomial.eval sizes rank)) :
      (binaryNaturalsOfWidth width).Carrier sizes :=
    ⟨((arguments ()).val index index).natAbs, (arguments ()).property index index⟩
  let step := arrayTransformStep context (arrayPosition rank) (binaryNaturalsOfWidth width) operation
  have index := (arrayPositionToIndex_realizable rank).withArguments step.inputDomains
    (MultiTape.oneTape (.inr ())) (by intros; rfl)
  have entry := (integerMatrixEntry_realizable rank rank width).onResults step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inr ()) | 1 => arguments.val (.inr ()) | 2 => arguments.val (.inl ()))
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact index
      · exact index
      · exact Realizable.argument step.inputDomains (.inl ()) step.precondition)
  have magnitude := entry.followedBy (integerMagnitude_realizable width) rfl (by intros; trivial)
  exact arrayTabulate_realizable context (binaryNaturalsOfWidth width) rank operation magnitude

private noncomputable def entryWidth (rank width : MvPolynomial Parameter ℕ) := hermiteAlternatingEntryWidth rank width
private noncomputable def basisWidth (rank width : MvPolynomial Parameter ℕ) :=
  hermiteAlternatingRunBasisWidth rank (entryWidth rank width) (hermiteAlternatingBudget rank width)

private noncomputable def diagonalAndBases (rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (integerHermiteDiagonalize rank width).outputDomain
  outputDomain := ((binaryNaturalsOfWidth (entryWidth rank width)).arrayOfLength rank).prod
    ((integerMatrices rank rank (basisWidth rank width)).prod (integerMatrices rank rank (basisWidth rank width)))
  precondition _ _ := True
  compute sizes arguments :=
    ((integerMatrixDiagonalMagnitudes rank (entryWidth rank width)).compute sizes ⟨fun _ => (arguments.val ()).1, trivial⟩,
      (arguments.val ()).2)

private theorem diagonalAndBases_realizable (rank width : MvPolynomial Parameter ℕ) :
    (diagonalAndBases rank width).Realizable := by
  have mapped := (integerMatrixDiagonalMagnitudes_realizable rank (entryWidth rank width)).prodMap
    (copy_realizable ((integerMatrices rank rank (basisWidth rank width)).prod
      (integerMatrices rank rank (basisWidth rank width))))
  exact mapped.withSpecification (fun _ _ => True) (diagonalAndBases rank width).compute
    (by intros; trivial) (by intros; rfl)

private noncomputable def assemble (rows columns rank width : MvPolynomial Parameter ℕ) :=
  ((diagonalAndBases rank width).withPrecondition
    (fun sizes _ => MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns) (by intros; trivial)).followedBy
    (integerRectangularDiagonalWithBases rows columns rank (entryWidth rank width) (basisWidth rank width))
    rfl (fun _ _ valid => valid)

private theorem assemble_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (assemble rows columns rank width).Realizable :=
  ((diagonalAndBases_realizable rank width).withPrecondition
    (assemble rows columns rank width).precondition (by intros; trivial)).followedBy
    (integerRectangularDiagonalWithBases_realizable rows columns rank (entryWidth rank width) (basisWidth rank width))
    rfl (fun _ _ valid => valid)

private noncomputable def prepared (rows columns rank width : MvPolynomial Parameter ℕ) :=
  (integerHermiteDiagonalize rank width).withPrecondition
    (fun sizes arguments =>
      (MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
        MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns) ∧
      (arguments ()).val.IsLowerTriangular ∧ ∀ index, 0 < (arguments ()).val index index)
    (fun _ _ valid => valid.2)

/-- Diagonalize an active square matrix and return the full rectangular matrix and bases. -/
noncomputable def integerRectangularHermite (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (prepared rows columns rank width).followedBy (assemble rows columns rank width) rfl (fun _ _ valid => valid.1)

/-- Square diagonalization, rectangular output construction, and both identity extensions are realized. -/
theorem integerRectangularHermite_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularHermite rows columns rank width).Realizable :=
  ((integerHermiteDiagonalize_realizable rank width).withPrecondition
    (prepared rows columns rank width).precondition (fun _ _ valid => valid.2)).followedBy
    (assemble_realizable rows columns rank width) rfl (fun _ _ valid => valid.1)

/-- The realized rectangular lift is exactly the mathematical active-block construction. -/
theorem integerRectangularHermite_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularHermite rows columns rank width).Arguments sizes //
      (integerRectangularHermite rows columns rank width).precondition sizes arguments}) :
    let result := (integerRectangularHermite rows columns rank width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.rectangularHermiteRun arguments.property.1.1 arguments.property.1.2
        (MvPolynomial.eval sizes width) (arguments.val ()).val := by
  let square := (integerHermiteDiagonalize rank width).compute sizes ⟨arguments.val, arguments.property.2⟩
  have same : (square.1.val, square.2.1.val, square.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun
        (MvPolynomial.eval sizes width * MvPolynomial.eval sizes rank * MvPolynomial.eval sizes rank + 2)
        (arguments.val ()).val := by
    have actual := integerHermiteAlternatingRun_correct rank width (hermiteAlternatingBudget rank width) sizes
      ⟨arguments.val, arguments.property.2⟩
    change (square.1.val, square.2.1.val, square.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes (hermiteAlternatingBudget rank width)) (arguments.val ()).val at actual
    simpa only [hermiteAlternatingBudget, map_add, map_mul, MvPolynomial.eval_ofNat] using actual
  have diagonal := IntegerMatrix.rectangularHermiteRun_diagonal arguments.property.1.1 arguments.property.1.2
    (MvPolynomial.eval sizes width) (arguments.val ()).val arguments.property.2.1 arguments.property.2.2
    (arguments.val ()).property
  rw [← same] at diagonal
  apply Prod.ext
  · exact diagonal.symm
  · apply Prod.ext
    · have extended := extendIntegerBasis_correct rows rank (basisWidth rank width) sizes
        ⟨fun _ => square.2.1, arguments.property.1.1⟩
      exact extended.trans (congrArg (IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes rows) arguments.property.1.1)
        (congrArg (fun result => result.2.1) same))
    · have extended := extendIntegerBasis_correct columns rank (basisWidth rank width) sizes
        ⟨fun _ => square.2.2, arguments.property.1.2⟩
      exact extended.trans (congrArg (IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes columns) arguments.property.1.2)
        (congrArg (fun result => result.2.2) same))

end Polytime2.Computation
