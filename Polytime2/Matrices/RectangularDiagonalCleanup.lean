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
import Polytime2.Matrices.PositiveDiagonalCleanup
import Polytime2.Matrices.RectangularPresentation
import Polytime2.Matrices.ExtendIntegerBasis

/-! # Certified Smith cleanup for an already diagonal rectangular matrix

Input a positive bounded active natural diagonal and independent full row and
column counts containing it. Normalize the active entries, construct the full
rectangular diagonal, and extend both actual bases by identities. Only the
mathematical positivity and dimension inclusions are preconditions. Derived
workspace widths and all output construction stay inside the implementation.
This stage does not perform the preceding reduction of an arbitrary matrix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain
open Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def assemble (rows columns rank width : MvPolynomial Parameter ℕ) :=
  integerRectangularDiagonalWithBases rows columns rank (positiveDiagonalProductWidth rank width + 1)
    (positiveDiagonalBasisWidth rank width)

private theorem assemble_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (assemble rows columns rank width).Realizable :=
  integerRectangularDiagonalWithBases_realizable rows columns rank (positiveDiagonalProductWidth rank width + 1)
    (positiveDiagonalBasisWidth rank width)

private theorem assemble_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (assemble rows columns rank width).Arguments sizes //
      (assemble rows columns rank width).precondition sizes arguments}) :
    let result := (assemble rows columns rank width).compute sizes arguments
    (result.1.val, (result.2.1.val, result.2.2.val)) =
      (IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        (fun index => ((arguments.val ()).1 index).val),
       (IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes rows) arguments.property.1 (arguments.val ()).2.1.val,
        IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes columns) arguments.property.2 (arguments.val ()).2.2.val)) := by
  apply Prod.ext
  · exact integerRectangularDiagonal_correct rows columns rank (positiveDiagonalProductWidth rank width + 1) sizes
      ⟨(fun _ => (arguments.val ()).1), trivial⟩
  · exact Prod.ext
      (extendIntegerBasis_correct rows rank (positiveDiagonalBasisWidth rank width) sizes
        ⟨(fun _ => (arguments.val ()).2.1), arguments.property.1⟩)
      (extendIntegerBasis_correct columns rank (positiveDiagonalBasisWidth rank width) sizes
        ⟨(fun _ => (arguments.val ()).2.2), arguments.property.2⟩)

private noncomputable def prepared (rows columns rank width : MvPolynomial Parameter ℕ) :=
  (positiveDiagonalCleanup rank width).withPrecondition
    (fun sizes arguments => (∀ index, 0 < (arguments () index).val) ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns)
    (fun _ _ valid => valid.1)

/-- Return full-sized Smith diagonal and unimodular bases for an active rectangular diagonal. -/
private noncomputable def implementation (rows columns rank width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (prepared rows columns rank width).followedBy (assemble rows columns rank width) rfl (fun _ _ valid => valid.2)

private theorem implementation_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (implementation rows columns rank width).Realizable :=
  ((positiveDiagonalCleanup_realizable rank width).withPrecondition
    (prepared rows columns rank width).precondition (fun _ _ valid => valid.1)).followedBy
    (assemble_realizable rows columns rank width) rfl (fun _ _ valid => valid.2)

/-- The complete output equals the mathematical rectangular cleanup, including both bases. -/
private theorem implementation_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation rows columns rank width).Arguments sizes //
      (implementation rows columns rank width).precondition sizes arguments}) :
    let result := (implementation rows columns rank width).compute sizes arguments
    (result.1.val, (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.rectangularDiagonalCleanup (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        arguments.property.2.1 arguments.property.2.2 (MvPolynomial.eval sizes width)
        (fun index => (arguments.val () index).val) := by
  have cleaned := positiveDiagonalCleanup_correct rank width sizes ⟨arguments.val, arguments.property.1⟩
  have assembled := assemble_correct rows columns rank width sizes
    ⟨(fun _ => (positiveDiagonalCleanup rank width).compute sizes ⟨arguments.val, arguments.property.1⟩), arguments.property.2⟩
  have extended := congrArg (fun state =>
    (IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) state.1,
      (IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes rows) arguments.property.2.1 state.2.1,
       IntegerMatrix.extendDiagonalBasis (MvPolynomial.eval sizes columns) arguments.property.2.2 state.2.2))) cleaned
  exact assembled.trans extended

/-- The mathematical rectangular cleanup and its full identity-extended bases.
Only positivity and inclusion of the active dimensions are required. -/
noncomputable def rectangularPositiveDiagonalCleanup (rows columns rank width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  specificationBy (fun _ => (binaryNaturalsOfWidth width).arrayOfLength rank)
    ((integerMatrices rows columns ((positiveDiagonalProductWidth rank width + 1) + 1)).prod
      ((integerMatrices rows rows (positiveDiagonalBasisWidth rank width + 1)).prod
        (integerMatrices columns columns (positiveDiagonalBasisWidth rank width + 1))))
    (fun sizes arguments => (∀ index, 0 < (arguments () index).val) ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns)
    (fun _ result => (result.1.val, (result.2.1.val, result.2.2.val)))
    (fun sizes arguments => IntegerMatrix.rectangularDiagonalCleanup
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
      arguments.property.2.1 arguments.property.2.2 (MvPolynomial.eval sizes width)
      (fun index => (arguments.val () index).val))
    (fun sizes arguments => ⟨(implementation rows columns rank width).compute sizes arguments,
      implementation_correct rows columns rank width sizes arguments⟩)

theorem rectangularPositiveDiagonalCleanup_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (rectangularPositiveDiagonalCleanup rows columns rank width).Realizable := by
  apply (implementation_realizable rows columns rank width).specificationBy
  · intro sizes
    exact Subtype.val_injective.prodMap (Subtype.val_injective.prodMap Subtype.val_injective)
  · intro sizes arguments valid
    exact implementation_correct rows columns rank width sizes ⟨arguments, valid⟩

/-- Observe the mathematical answer without initialization or basis-extension wiring. -/
theorem rectangularPositiveDiagonalCleanup_correct (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (rectangularPositiveDiagonalCleanup rows columns rank width).Arguments sizes //
      (rectangularPositiveDiagonalCleanup rows columns rank width).precondition sizes arguments}) :
    let result := (rectangularPositiveDiagonalCleanup rows columns rank width).compute sizes arguments
    (result.1.val, (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.rectangularDiagonalCleanup (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        arguments.property.2.1 arguments.property.2.2 (MvPolynomial.eval sizes width)
        (fun index => (arguments.val () index).val) := by
  exact specificationBy_correct _ (rectangularPositiveDiagonalCleanup rows columns rank width).outputDomain _
    (fun _ result => (result.1.val, (result.2.1.val, result.2.2.val))) _ _ sizes arguments

/-- The realized rectangular output satisfies the full Smith contract at the supplied rank. -/
theorem rectangularPositiveDiagonalCleanup_isSmithForm (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (rectangularPositiveDiagonalCleanup rows columns rank width).Arguments sizes //
      (rectangularPositiveDiagonalCleanup rows columns rank width).precondition sizes arguments}) :
    let result := (rectangularPositiveDiagonalCleanup rows columns rank width).compute sizes arguments
    IntegerMatrix.IsSmithForm
      (IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
        (fun index => (arguments.val () index).val)) result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval sizes rank) := by
  have correct := rectangularPositiveDiagonalCleanup_correct rows columns rank width sizes arguments
  have pure := IntegerMatrix.rectangularDiagonalCleanup_isSmithForm arguments.property.2.1 arguments.property.2.2
    (MvPolynomial.eval sizes width) (fun index => (arguments.val () index).val) arguments.property.1
    (fun index => (arguments.val () index).isLt)
  have transfer := congrArg (fun result => IntegerMatrix.IsSmithForm
    (IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)
      (fun index => (arguments.val () index).val)) result.1 result.2.1 result.2.2 (MvPolynomial.eval sizes rank)) correct
  exact transfer.mpr pure

end Polytime2.Computation
