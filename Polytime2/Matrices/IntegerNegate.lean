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
import Polytime2.Matrices.NegateMath

/-! # Certified single-row and single-column sign changes

Every bounded integer matrix and valid target index is admissible. Negation
preserves the magnitude width. The row implementation reuses lookup, array
mapping, and update; column negation reuses it through certified transposition.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerRowNegate (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains | false => boundedIndex rows | true => integerMatrices rows columns width
  outputDomain := integerMatrices rows columns width
  precondition _ _ := True
  compute sizes arguments := ⟨IntegerMatrix.rowNegate (Row := Fin (MvPolynomial.eval sizes rows))
    (arguments.val false) (arguments.val true).val,
    IntegerMatrix.rowNegate_bound (MvPolynomial.eval sizes width) _ _ (arguments.val true).property⟩

set_option backward.isDefEq.respectTransparency false in
theorem integerRowNegate_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowNegate rows columns width).Realizable := by
  let computation := integerRowNegate rows columns width
  let inputs := computation.inputDomains
  let scalar := binaryIntegers width
  let negate sizes (value : scalar.Carrier sizes) : scalar.Carrier sizes :=
    ⟨-value.val, by simpa using value.property⟩
  have mapped := mapArray_realizable scalar scalar columns negate (integerNegate_realizable width)
  have negated := (Realizable.Internal.integerMatrixRow_realizable rows columns width).followedBy mapped
    rfl (by intros; trivial)
  have original := (Realizable.argument inputs true (fun _ _ => True)).reinterpretOutput
    ((scalar.arrayOfLength columns).arrayOfLength rows)
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width))
    (fun sizes => (integerMatrices_nested_width rows columns width sizes).symm)
    (fun sizes value => (integerMatrices_nested_encode_bits rows columns width sizes value).symm)
  have updated := (arrayUpdate_realizable (scalar.arrayOfLength columns) rows).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | 0 => arguments.val false
      | 1 => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width) (arguments.val true)
      | 2 => fun column => negate sizes ⟨(arguments.val true).val (arguments.val false) column,
          (arguments.val true).property (arguments.val false) column⟩)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument inputs false (fun _ _ => True)
      · exact original
      · exact negated)
  have result := updated.reinterpretOutput computation.outputDomain
    (fun sizes value => (IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes width)).symm value)
    (fun sizes => integerMatrices_nested_width rows columns width sizes)
    (fun sizes value => integerMatrices_of_nested_encode_bits rows columns width sizes value)
  apply result.withSpecification (fun _ _ => True) computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Subtype.ext
  funext row column
  dsimp only [Computation.reinterpretOutput, Computation.onResults, arrayUpdate]
  erw [IntegerMatrix.entryBoundEquiv_symm_apply]
  simp only [computation, integerRowNegate]
  erw [IntegerMatrix.rowNegate_apply]
  by_cases same : row = arguments false
  · subst row
    erw [Function.update_self]
    simp [negate]
  · erw [Function.update_of_ne same, IntegerMatrix.entryBoundEquiv_apply]
    simp [same]

/-- Column negation has the same bound and reuses the row machine. -/
noncomputable def integerColumnNegate (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains | false => boundedIndex columns | true => integerMatrices rows columns width
  outputDomain := integerMatrices rows columns width
  precondition _ _ := True
  compute sizes arguments := ⟨(IntegerMatrix.rowNegate (Row := Fin (MvPolynomial.eval sizes columns))
    (arguments.val false) (arguments.val true).val.transpose).transpose,
    fun row column => IntegerMatrix.rowNegate_bound (MvPolynomial.eval sizes width) _ _
      (fun column row => (arguments.val true).property row column) column row⟩

theorem integerColumnNegate_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnNegate rows columns width).Realizable := by
  let computation := integerColumnNegate rows columns width
  let inputs := computation.inputDomains
  have transposed := (integerMatrixTranspose_realizable rows columns width).withArguments inputs
    (MultiTape.oneTape true) (fun _ => rfl)
  have negated := (integerRowNegate_realizable columns rows width).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => match name with
      | false => arguments.val false
      | true => (integerMatrixTranspose rows columns width).compute sizes ⟨(fun _ => arguments.val true), trivial⟩)
    (by intros; trivial) (by
      intro name
      cases name
      · exact Realizable.argument inputs false (fun _ _ => True)
      · exact transposed)
  have complete := negated.followedBy (integerMatrixTranspose_realizable columns rows width) rfl (by intros; trivial)
  exact complete.withSpecification (fun _ _ => True) computation.compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
