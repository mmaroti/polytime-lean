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

import Polytime2.Matrices.IntegerOperations
import Polytime2.Matrices.IntegerHermiteDiagonalize
import Polytime2.Matrices.Tabulate

/-! # Extracting the leading mathematical matrix block

Read the leading square block at an active rank bounded by both dimensions.
The entry width is unchanged. Rank bounds are mathematical admissibility;
existing indexed row and array reads handle the differing coordinate widths.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private def fits (rows columns rank : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) : Prop :=
  MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
    MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns

/-- Extract the leading square block, preserving the original magnitude width. -/
noncomputable def integerMatrixLeadingBlock (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := integerMatrices rows columns width
  outputDomain := integerMatrices rank rank width
  precondition sizes _ := fits rows columns rank sizes
  compute _ arguments := ⟨(arguments.val ()).val.submatrix (Fin.castLE arguments.property.1) (Fin.castLE arguments.property.2),
    fun _ _ => (arguments.val ()).property _ _⟩

/-- Block extraction composes existing row lookup, scalar lookup, and tabulation. -/
theorem integerMatrixLeadingBlock_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerMatrixLeadingBlock rows columns rank width).Realizable := by
  classical
  let computation := integerMatrixLeadingBlock rows columns rank width
  let source := integerMatrices rows columns width
  let bounded := source.restrict (fun sizes _ => fits rows columns rank sizes)
  let context : Unit → EncodedDomain Parameter := fun _ => bounded
  let scalar := binaryIntegers width
  let operation sizes (arguments : ∀ name, (context name).Carrier sizes)
      (row column : Fin (MvPolynomial.eval sizes rank)) : scalar.Carrier sizes :=
    ⟨(arguments ()).val.val (Fin.castLE (arguments ()).property.1 row)
      (Fin.castLE (arguments ()).property.2 column), (arguments ()).val.property _ _⟩
  let step := matrixTabulateStep context scalar rank rank operation
  have row := (integerMatrixRowWithIndex_realizable rows columns width (arrayPosition rank)
    (fun _ index => index.val) (arrayPosition_value rank)).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr false) | true => (arguments.val (.inl ())).val)
    (by
      intro sizes arguments
      exact (arguments.val (.inr false)).isLt.trans_le (arguments.val (.inl ())).property.1)
    (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr false) step.precondition
      · exact ((copy_realizable source).reinterpretInputs (fun _ : Unit => bounded)
          (fun _ _ value => value.val) (by intros; rfl) (by intros; rfl)
          (fun _ _ => True) (by intros; trivial)).withArguments step.inputDomains
          (MultiTape.oneTape (.inl ())) (by intros; rfl))
  have entry := (arrayLookupWithIndex_realizable scalar (arrayPosition rank) (fun _ index => index.val)
    (arrayPosition_value rank) columns).onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr true)
      | true => fun column => ⟨(arguments.val (.inl ())).val.val
          (Fin.castLE (arguments.val (.inl ())).property.1 (arguments.val (.inr false))) column,
          (arguments.val (.inl ())).val.property _ _⟩)
    (by
      intro sizes arguments
      exact (arguments.val (.inr true)).isLt.trans_le (arguments.val (.inl ())).property.2)
    (by
      intro choice
      cases choice
      · exact Realizable.argument step.inputDomains (.inr true) step.precondition
      · exact row)
  have scalarReady : step.Realizable := entry.withSpecification step.precondition step.compute
    (by intros; trivial) (by intros; rfl)
  have tabulated := matrixTabulate_realizable context scalar rank rank operation scalarReady
  have collected := tabulated.reindexOutput computation.outputDomain.Carrier
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
  have prepared := ((copy_realizable source).withPrecondition computation.precondition (by intros; trivial)).refineOutput
    (fun sizes _ => fits rows columns rank sizes) (by intro sizes arguments; exact arguments.property)
  have complete := prepared.followedBy collected rfl (by intros; trivial)
  exact complete.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- The output is exactly the ordinary leading submatrix. -/
theorem integerMatrixLeadingBlock_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerMatrixLeadingBlock rows columns rank width).Arguments sizes //
      (integerMatrixLeadingBlock rows columns rank width).precondition sizes arguments}) :
    ((integerMatrixLeadingBlock rows columns rank width).compute sizes arguments).val =
      (arguments.val ()).val.submatrix (Fin.castLE arguments.property.1) (Fin.castLE arguments.property.2) := rfl

private def activeAllowed (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (integerMatrices rows columns width).Carrier sizes) : Prop :=
  ∃ bounds : fits rows columns rank sizes,
    ((arguments ()).val.submatrix (Fin.castLE bounds.1) (Fin.castLE bounds.2)).IsLowerTriangular ∧
      ∀ index, 0 < (arguments ()).val (Fin.castLE bounds.1 index) (Fin.castLE bounds.2 index)

private noncomputable def prepareActive (rows columns rank width : MvPolynomial Parameter ℕ) :=
  (integerMatrixLeadingBlock rows columns rank width).withPrecondition (activeAllowed rows columns rank width)
    (fun _ _ valid => valid.choose)

private theorem activePermitted (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (prepareActive rows columns rank width).Arguments sizes)
    (valid : (prepareActive rows columns rank width).precondition sizes arguments) :
    (integerHermiteDiagonalize rank width).precondition sizes
      (fun _ => (prepareActive rows columns rank width).compute sizes ⟨arguments, valid⟩) :=
  valid.choose_spec

/-- Extract and diagonalize a positive lower triangular leading block. -/
noncomputable def integerLeadingBlockDiagonalize (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (prepareActive rows columns rank width).followedBy (integerHermiteDiagonalize rank width) rfl
    (activePermitted rows columns rank width)

/-- Mathematical rank bounds and a positive lower active block suffice. -/
theorem integerLeadingBlockDiagonalize_permitted (rows columns rank width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerLeadingBlockDiagonalize rows columns rank width).Arguments sizes)
    (rowBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows)
    (columnBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns)
    (lower : ((arguments ()).val.submatrix (Fin.castLE rowBound) (Fin.castLE columnBound)).IsLowerTriangular)
    (positive : ∀ index, 0 < (arguments ()).val (Fin.castLE rowBound index) (Fin.castLE columnBound index)) :
    (integerLeadingBlockDiagonalize rows columns rank width).precondition sizes arguments :=
  ⟨⟨rowBound, columnBound⟩, lower, positive⟩

/-- Extraction and the complete square diagonalizer are certified by composition. -/
theorem integerLeadingBlockDiagonalize_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerLeadingBlockDiagonalize rows columns rank width).Realizable :=
  ((integerMatrixLeadingBlock_realizable rows columns rank width).withPrecondition
    (activeAllowed rows columns rank width) (fun _ _ valid => valid.choose)).followedBy
    (integerHermiteDiagonalize_realizable rank width) rfl (activePermitted rows columns rank width)

end Polytime2.Computation
