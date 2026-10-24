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

import Polytime2.Matrices.HermiteColumnBounds
import Polytime2.Matrices.IntegerEuclideanReduction
import Polytime2.Matrices.IntegerBezoutTracking
import Polytime2.Arithmetic.SignedDivides

/-! # Certified progress-sensitive Hermite row elimination

For a bounded rectangular matrix, distinct source and target rows, a selected
column with positive source entry, and a bounded left basis, clear the target
entry and return both updated matrices. Divisible entries use quotient
cancellation and retain the source row; all other entries use Bézout reduction.
The output width is derived internally. Polynomial bounds for repeated steps
are proved separately from this local realization.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Clear a target with quotient cancellation or a genuine gcd pivot change. -/
noncomputable def integerHermiteRowStep (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) where
  inputDomains | 0 | 1 => boundedIndex rows | 2 => boundedIndex columns
               | 3 => integerMatrices rows columns width | 4 => integerMatrices rows rows width
  outputDomain := (integerMatrices rows columns (2 * (2 * width + 1) + 1)).prod
    (integerMatrices rows rows (2 * (2 * width + 1) + 1))
  precondition _ arguments := arguments 0 ≠ arguments 1 ∧ 0 < (arguments 3).val (arguments 0) (arguments 2)
  compute sizes arguments :=
    let result := IntegerMatrix.hermiteRowStep
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (arguments.val 0) (arguments.val 1) (arguments.val 2)
      (arguments.val 3).val (arguments.val 4).val
    have bounds := IntegerMatrix.hermiteRowStep_bound
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width)
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val
      ((arguments.val 3).property _ _) ((arguments.val 3).property _ _)
      (arguments.val 3).property (arguments.val 4).property
    have capacity : MvPolynomial.eval sizes width + (2 * MvPolynomial.eval sizes width + 2) ≤
        MvPolynomial.eval sizes (2 * (2 * width + 1) + 1) := by
      simp only [map_add, map_mul, map_ofNat, map_one]
      omega
    (⟨result.1, fun row column => (bounds.1 row column).trans_le (pow_le_pow_right₀ (by decide) capacity)⟩,
      ⟨result.2, fun row column => (bounds.2 row column).trans_le (pow_le_pow_right₀ (by decide) capacity)⟩)

/-- The returned ordinary matrices are exactly the mathematical Hermite step. -/
theorem integerHermiteRowStep_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRowStep rows columns width).Arguments sizes //
      (integerHermiteRowStep rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRowStep rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStep
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val 0) (arguments.val 1) (arguments.val 2) (arguments.val 3).val (arguments.val 4).val := rfl

private def hermiteEntrySelection (source : Bool) : Fin 3 ↪ Fin 5 :=
  ⟨(fun name => match name with | 0 => if source then 0 else 1 | 1 => 2 | 2 => 3), by
    intro first second equal
    cases source <;> fin_cases first <;> fin_cases second <;> simp_all⟩

private theorem hermiteGuard_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (Computation.mk (integerHermiteRowStep rows columns width).inputDomains booleans
      (integerHermiteRowStep rows columns width).precondition (fun _ arguments =>
        decide ((arguments.val 3).val (arguments.val 0) (arguments.val 2) ∣
          (arguments.val 3).val (arguments.val 1) (arguments.val 2)))).Realizable := by
  classical
  let computation := integerHermiteRowStep rows columns width
  let entry (source : Bool) := ((integerMatrixEntry rows columns width).withArguments computation.inputDomains
    (hermiteEntrySelection source) (by intro name; cases source <;> fin_cases name <;> rfl)).withPrecondition
      computation.precondition (by intros; trivial)
  have entryReady (source : Bool) : (entry source).Realizable :=
    ((integerMatrixEntry_realizable rows columns width).withArguments computation.inputDomains
      (hermiteEntrySelection source) (by intro name; cases source <;> fin_cases name <;> rfl)).withPrecondition
        computation.precondition (by intros; trivial)
  have divided := (integerDivides_realizable width).onResults computation.inputDomains computation.precondition
    (fun source sizes arguments => (entry (!source)).compute sizes arguments) (by intros; trivial)
    (fun source => entryReady (!source))
  exact divided.withSpecification computation.precondition _ (by intros; assumption) (by intros; rfl)

private theorem hermiteRemainder_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (Computation.mk (integerHermiteRowStep rows columns width).inputDomains
      (integerHermiteRowStep rows columns width).outputDomain
      (integerHermiteRowStep rows columns width).precondition (fun sizes arguments =>
        let result := (integerRowRemainderWithLeft rows columns width).compute sizes arguments
        (⟨result.1.val, fun row column => (result.1.property row column).trans_le
          (pow_le_pow_right₀ (by decide) (by simp only [map_add, map_mul, map_ofNat, map_one]; omega))⟩,
         ⟨result.2.val, fun row column => (result.2.property row column).trans_le
          (pow_le_pow_right₀ (by decide) (by simp only [map_add, map_mul, map_ofNat, map_one]; omega))⟩))).Realizable := by
  have widthEqual : 2 * (2 * width + 1) + 1 = (2 * width + 1) + (2 * width + 2) := by ring
  have mapped := (integerMatrixWiden_realizable rows columns (2 * width + 1) (2 * width + 2)
    (2 * (2 * width + 1) + 1) widthEqual).prodMap
    (integerMatrixWiden_realizable rows rows (2 * width + 1) (2 * width + 2)
      (2 * (2 * width + 1) + 1) widthEqual)
  have widened := mapped.withPrecondition (fun _ _ => True) (by intros; trivial)
  have complete := (integerRowRemainderWithLeft_realizable rows columns width).followedBy widened rfl (by intros; trivial)
  exact complete.withSpecification (integerHermiteRowStep rows columns width).precondition _
    (by intros; assumption) (by intros; rfl)

theorem integerHermiteRowStep_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStep rows columns width).Realizable := by
  classical
  let computation := integerHermiteRowStep rows columns width
  let condition (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) :=
    decide ((arguments 3).val (arguments 0) (arguments 2) ∣ (arguments 3).val (arguments 1) (arguments 2))
  apply Realizable.ofCases condition (hermiteGuard_realizable rows columns width)
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have ready := (hermiteRemainder_realizable rows columns width).withPrecondition allowed
      (fun _ _ valid => valid.1)
    apply ready.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have divides : (arguments 3).val (arguments 0) (arguments 2) ∣
        (arguments 3).val (arguments 1) (arguments 2) := of_decide_eq_true valid.2
    have source := integerRowRemainderWithLeft_correct rows columns width sizes ⟨arguments, valid.1⟩
    have target := integerHermiteRowStep_correct rows columns width sizes ⟨arguments, valid.1⟩
    have branch : IntegerMatrix.hermiteRowStep
        (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
        (arguments 0) (arguments 1) (arguments 2) (arguments 3).val (arguments 4).val =
        IntegerMatrix.rowRemainderWithLeft
          (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (arguments 0) (arguments 1) (arguments 2) (arguments 3).val (arguments 4).val := by
      simp only [IntegerMatrix.hermiteRowStep, ite_eq_left divides]
    have equal := source.trans (branch.symm.trans target.symm)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst equal)) (Subtype.ext (congrArg Prod.snd equal))

  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have ready := (integerBezoutRowsWithLeft_realizable rows columns width).withPrecondition allowed
      (by intro sizes arguments valid; exact valid.1.1)
    apply ready.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have notDivides : ¬(arguments 3).val (arguments 0) (arguments 2) ∣
        (arguments 3).val (arguments 1) (arguments 2) := of_decide_eq_false valid.2
    have source := integerBezoutRowsWithLeft_compute rows columns width sizes ⟨arguments, valid.1.1⟩
    have target := integerHermiteRowStep_correct rows columns width sizes ⟨arguments, valid.1⟩
    have branch : IntegerMatrix.hermiteRowStep
        (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
        (arguments 0) (arguments 1) (arguments 2) (arguments 3).val (arguments 4).val =
        IntegerMatrix.bezoutRowsWithLeft
          (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (arguments 0) (arguments 1) (arguments 2) (arguments 3).val (arguments 4).val := by
      simp only [IntegerMatrix.hermiteRowStep, ite_eq_right notDivides]
    have equal := source.trans (branch.symm.trans target.symm)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst equal)) (Subtype.ext (congrArg Prod.snd equal))

end Polytime2.Computation
