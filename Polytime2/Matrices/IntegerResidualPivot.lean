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
import Polytime2.Matrices.HermitePivotMath
import Polytime2.Arithmetic.SignedArithmetic
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.BoundedPositions
import Polytime2.Arrays.FindFalse
import Polytime2.Arrays.SearchGuard
import Polytime2.Computation.Specification

/-! # Certified residual-pivot search

Given a bounded integer matrix and one row, return an optional nonzero column.
The public result is `none` exactly for a zero row. Tabulation, matrix lookup,
signed zero testing, and the existing first-false search supply the runtime
certificate, including an empty column dimension.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def context (rows columns width : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => boundedIndex rows
  | true => integerMatrices rows columns width

private def zeroFlag (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (context rows columns width name).Carrier sizes)
    (column : Fin (MvPolynomial.eval sizes columns)) : Bool := decide ((arguments true).val (arguments false) column = 0)

private noncomputable def flags (rows columns width : MvPolynomial Parameter ℕ) :=
  arrayTabulate (context rows columns width) booleans columns (zeroFlag rows columns width)

private theorem flags_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (flags rows columns width).Realizable := by
  apply arrayTabulate_realizable
  let step := arrayTransformStep (context rows columns width) (arrayPosition columns) booleans (zeroFlag rows columns width)
  have coordinate := (arrayPositionToIndex_realizable columns).withArguments step.inputDomains
    (MultiTape.oneTape (.inr ())) (by intros; rfl)
  have entry := (integerMatrixEntry_realizable rows columns width).onResults step.inputDomains step.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val (.inl false)
      | 1 => arguments.val (.inr ())
      | 2 => arguments.val (.inl true))
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument step.inputDomains (.inl false) step.precondition
      · exact coordinate
      · exact Realizable.argument step.inputDomains (.inl true) step.precondition)
  have tested := entry.followedBy (integerIsZero_realizable width) rfl (by intros; trivial)
  exact tested.withSpecification step.precondition step.compute (by intros; trivial) (by intros; rfl)

/-- Search one mathematical row, retaining the optional coordinate and hiding the scan sentinel. -/
noncomputable def integerResidualPivot (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (flags rows columns width).followedBy (arrayFindFalse columns) rfl (by intros; trivial)

theorem integerResidualPivot_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerResidualPivot rows columns width).Realizable :=
  (flags_realizable rows columns width).followedBy (arrayFindFalse_realizable columns) rfl (by intros; trivial)

/-- The runtime search agrees with the shared mathematical residual selection. -/
theorem integerResidualPivot_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerResidualPivot rows columns width).Arguments sizes //
      (integerResidualPivot rows columns width).precondition sizes arguments}) :
    (integerResidualPivot rows columns width).compute sizes arguments =
      IntegerMatrix.hermiteResidualPivot (arguments.val false) (arguments.val true).val :=
  arrayFindFalse_spec columns sizes (fun column => decide ((arguments.val true).val (arguments.val false) column = 0))

/-- Absence of a residual pivot certifies the whole row is zero. -/
theorem integerResidualPivot_none (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerResidualPivot rows columns width).Arguments sizes //
      (integerResidualPivot rows columns width).precondition sizes arguments}) :
    (integerResidualPivot rows columns width).compute sizes arguments = none ↔
      (arguments.val true).val (arguments.val false) = 0 := by
  rw [integerResidualPivot_correct]
  exact IntegerMatrix.hermiteResidualPivot_none _ _

/-- A returned coordinate is an actual nonzero entry. -/
theorem integerResidualPivot_nonzero (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerResidualPivot rows columns width).Arguments sizes //
      (integerResidualPivot rows columns width).precondition sizes arguments})
    (column : Fin (MvPolynomial.eval sizes columns))
    (found : (integerResidualPivot rows columns width).compute sizes arguments = some column) :
    (arguments.val true).val (arguments.val false) column ≠ 0 := by
  apply IntegerMatrix.hermiteResidualPivot_nonzero (arguments.val false) (arguments.val true).val column
  exact (integerResidualPivot_correct rows columns width sizes arguments).symm.trans found

/-- Decide whether the selected residual row is zero using its optional pivot search. -/
private noncomputable def implementation (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool :=
  (integerResidualPivot rows columns width).followedBy (arraySearchIsNone columns) rfl (by intros; trivial)

/-- The zero-row guard composes residual search with the shared optional-result discriminator. -/
private theorem implementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (implementation rows columns width).Realizable :=
  (integerResidualPivot_realizable rows columns width).followedBy (arraySearchIsNone_realizable columns) rfl (by intros; trivial)

/-- The guard accepts precisely when every mathematical entry in the selected row is zero. -/
private theorem implementation_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation rows columns width).Arguments sizes //
      (implementation rows columns width).precondition sizes arguments}) :
    (implementation rows columns width).compute sizes arguments = true ↔
      (arguments.val true).val (arguments.val false) = 0 :=
  (arraySearchIsNone_correct columns sizes ((integerResidualPivot rows columns width).compute sizes arguments)).trans
    (integerResidualPivot_none rows columns width sizes arguments)

/-- Decide whether the ordinary selected row is zero. -/
noncomputable def integerResidualRowIsZero (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  decision (context rows columns width)
    (fun _ _ => True) (fun _ arguments => (arguments true).val (arguments false) = 0)

theorem integerResidualRowIsZero_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerResidualRowIsZero rows columns width).Realizable :=
  (implementation_realizable rows columns width).decision _
    (fun sizes arguments valid => implementation_correct rows columns width sizes ⟨arguments, valid⟩)

/-- The public guard accepts precisely the zero row. -/
theorem integerResidualRowIsZero_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerResidualRowIsZero rows columns width).Arguments sizes //
      (integerResidualRowIsZero rows columns width).precondition sizes arguments}) :
    (integerResidualRowIsZero rows columns width).compute sizes arguments = true ↔
      (arguments.val true).val (arguments.val false) = 0 :=
  decision_correct _ _ _ sizes arguments

end Polytime2.Computation
