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

import Polytime2.Matrices.IntegerHermiteStep
import Polytime2.Matrices.HermiteStageMath

/-! # Certified interleaved Hermite stage update

Inputs are source, incoming, and earlier rows, a selected column, and the
working matrix and left basis. The three rows are distinct and the source
pivot is positive. Eliminate the incoming entry, then normalize the selected
earlier row against the resulting positive gcd pivot, updating both matrices.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width : MvPolynomial Parameter ℕ) : Fin 6 → EncodedDomain Parameter
  | 0 | 1 | 2 => boundedIndex rows
  | 3 => boundedIndex columns
  | 4 => integerMatrices rows columns width
  | 5 => integerMatrices rows rows width

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width name).Carrier sizes) :=
  arguments 0 ≠ arguments 1 ∧ arguments 0 ≠ arguments 2 ∧ arguments 2 ≠ arguments 1 ∧
    0 < (arguments 4).val (arguments 0) (arguments 3)

private def selection : Fin 5 ↪ Fin 6 := ⟨![0, 1, 3, 4, 5], by decide +kernel⟩

private noncomputable def elimination (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 6) :=
  ((integerHermiteRowStep rows columns width).withArguments (inputs rows columns width) selection
    (by intro name; fin_cases name <;> rfl)).withPrecondition (allowed rows columns width)
      (fun _ _ valid => ⟨valid.1, valid.2.2.2⟩)

private theorem elimination_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (elimination rows columns width).Realizable :=
  ((integerHermiteRowStep_realizable rows columns width).withArguments (inputs rows columns width) selection
    (by intro name; fin_cases name <;> rfl)).withPrecondition (allowed rows columns width)
      (fun _ _ valid => ⟨valid.1, valid.2.2.2⟩)

private noncomputable def intermediateWidth (width : MvPolynomial Parameter ℕ) := 2 * (2 * width + 1) + 1

private noncomputable def prepared (rows columns width : MvPolynomial Parameter ℕ)
    (name : Fin 5) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width name).Carrier sizes //
      allowed rows columns width sizes arguments}) :
    (integerRowRemainderWithLeft rows columns (intermediateWidth width)).inputDomains name |>.Carrier sizes :=
  match name with
  | 0 => arguments.val 0
  | 1 => arguments.val 2
  | 2 => arguments.val 3
  | 3 => ((elimination rows columns width).compute sizes arguments).1
  | 4 => ((elimination rows columns width).compute sizes arguments).2

private theorem prepared_permitted (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width name).Carrier sizes //
      allowed rows columns width sizes arguments}) :
    (integerRowRemainderWithLeft rows columns (intermediateWidth width)).precondition sizes
      (fun name => prepared rows columns width name sizes arguments) := by
  refine ⟨arguments.property.2.1, ?_⟩
  change 0 < (IntegerMatrix.hermiteRowStep (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 3)
    (arguments.val 4).val (arguments.val 5).val).1 (arguments.val 0) (arguments.val 3)
  rw [(IntegerMatrix.hermiteRowStep_entries (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) _ _ arguments.property.1 _ _ _ arguments.property.2.2.2).1]
  exact_mod_cast Int.gcd_pos_of_ne_zero_left
    ((arguments.val 4).val (arguments.val 1) (arguments.val 3)) (ne_of_gt arguments.property.2.2.2)

/-- Eliminate an incoming entry and normalize one earlier row with the same resulting pivot. -/
noncomputable def integerHermiteRowStageUpdate (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 6) :=
  (integerRowRemainderWithLeft rows columns (intermediateWidth width)).onResults
    (inputs rows columns width) (allowed rows columns width) (prepared rows columns width)
    (prepared_permitted rows columns width)

/-- The update is realized by composition of the existing certified integer operations. -/
theorem integerHermiteRowStageUpdate_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStageUpdate rows columns width).Realizable := by
  apply (integerRowRemainderWithLeft_realizable rows columns (intermediateWidth width)).onResults
    (inputs rows columns width) (allowed rows columns width) (prepared rows columns width)
    (prepared_permitted rows columns width)
  intro name
  fin_cases name
  · exact Realizable.argument (inputs rows columns width) 0 (allowed rows columns width)
  · exact Realizable.argument (inputs rows columns width) 2 (allowed rows columns width)
  · exact Realizable.argument (inputs rows columns width) 3 (allowed rows columns width)
  · exact (elimination_realizable rows columns width).followedBy
      (pairProjection_realizable (integerMatrices rows columns (intermediateWidth width))
        (integerMatrices rows rows (intermediateWidth width)) false) rfl (by intros; trivial)
  · exact (elimination_realizable rows columns width).followedBy
      (pairProjection_realizable (integerMatrices rows columns (intermediateWidth width))
        (integerMatrices rows rows (intermediateWidth width)) true) rfl (by intros; trivial)

/-- The returned matrices are exactly one mathematical interleaved stage with the selected earlier row. -/
theorem integerHermiteRowStageUpdate_correct (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStageUpdate rows columns width).Arguments sizes //
      (integerHermiteRowStageUpdate rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRowStageUpdate rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 3) [arguments.val 2]
      (arguments.val 4).val (arguments.val 5).val := rfl

/-- The actual returned basis preserves the presentation and unimodularity. -/
theorem integerHermiteRowStageUpdate_preserves (rows columns width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStageUpdate rows columns width).Arguments sizes //
      (integerHermiteRowStageUpdate rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 5).val * original * right = (arguments.val 4).val)
    (unit : IsUnit (arguments.val 5).val.det) :
    let result := (integerHermiteRowStageUpdate rows columns width).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det := by
  exact IntegerMatrix.hermiteRowStage_preserves (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1)
    arguments.property.1 (arguments.val 3) [arguments.val 2]
    (by simpa only [List.mem_singleton] using arguments.property.2.1)
    (arguments.val 4).val original (arguments.val 5).val right equation unit

end Polytime2.Computation
