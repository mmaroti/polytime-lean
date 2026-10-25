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

import Polytime2.Arithmetic.NormalizedBezout
import Polytime2.Matrices.BezoutMath

/-! # Certified coefficients for a Bézout row transformation

This private record prepares four runtime coefficients for the existing
simultaneous row operation. One normalized extended-gcd result is retained.
The zero-gcd branch returns the identity, and only the nonzero branch divides.
-/

namespace Polytime2.Computation.Realizable.Internal.BezoutCoefficients

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def coefficientWidth (width : MvPolynomial Parameter ℕ) := 2 * width + 1
noncomputable def domain (width : MvPolynomial Parameter ℕ) := record 4 (fun _ => binaryIntegers (coefficientWidth width))

private def entry (matrix : Matrix (Fin 2) (Fin 2) ℤ) : Fin 4 → ℤ :=
  ![matrix 0 0, matrix 0 1, matrix 1 0, matrix 1 1]

noncomputable def computation (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := domain width
  precondition _ _ := True
  compute sizes arguments index := ⟨entry (IntegerMatrix.bezoutMatrix (arguments.val false).val
    (arguments.val true).val) index, by
      have bound := IntegerMatrix.bezoutMatrix_bound (MvPolynomial.eval sizes width)
        (arguments.val false).val (arguments.val true).val (arguments.val false).property (arguments.val true).property
      fin_cases index
      all_goals simpa [entry, coefficientWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using bound _ _⟩

noncomputable def host (width : MvPolynomial Parameter ℕ) : Bool ⊕ Unit → EncodedDomain Parameter :=
  Sum.elim (computation width).inputDomains (fun _ => (integerNormalizedExtendedGcd width).outputDomain)

def consistent (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (host width name).Carrier sizes) : Prop :=
  arguments (.inr ()) = (integerNormalizedExtendedGcd width).compute sizes
    ⟨(fun name => arguments (.inl name)), trivial⟩

private theorem divisor_eq (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (host width name).Carrier sizes) (valid : consistent width sizes arguments) :
    (arguments (.inr ())).1.val = (Int.gcd (arguments (.inl false)).val (arguments (.inl true)).val : ℤ) :=
  (congrArg (fun result => result.1.val) valid).trans
    (integerNormalizedExtendedGcd_correct width sizes (fun name => arguments (.inl name))).1

noncomputable def stage (width : MvPolynomial Parameter ℕ) : Computation Parameter (Bool ⊕ Unit) where
  inputDomains := host width
  outputDomain := domain width
  precondition := consistent width
  compute sizes arguments := (computation width).compute sizes
    ⟨(fun name => arguments.val (.inl name)), trivial⟩

def nonzeroAllowed (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (host width name).Carrier sizes) : Prop :=
  consistent width sizes arguments ∧ (arguments (.inr ())).1.val ≠ 0

noncomputable def nonzeroStage (width : MvPolynomial Parameter ℕ) :=
  (stage width).withPrecondition (nonzeroAllowed width) (fun _ _ valid => valid.1)

theorem nonzeroStage_realizable (width : MvPolynomial Parameter ℕ) : (nonzeroStage width).Realizable := by
  let domains := host width
  let allowed := nonzeroAllowed width
  let capacity := coefficientWidth width
  let coefficients := (binaryIntegers capacity).prod (binaryIntegers capacity)
  have widen := integerWidenTo_realizable width (width + 1) capacity (by dsimp [capacity, coefficientWidth]; ring)
  have divisor := (pairProjection_realizable (binaryIntegers width) coefficients false).withArguments domains
    (MultiTape.oneTape (.inr ())) (fun _ => rfl)
  have coefficient (choice : Bool) : (Computation.mk domains (binaryIntegers capacity) allowed
      (fun _ arguments => if choice then (arguments.val (.inr ())).2.2 else (arguments.val (.inr ())).2.1)).Realizable := by
    have projection : (Computation.mk (fun _ : Unit => coefficients) (binaryIntegers capacity) (fun _ _ => True)
        (fun _ arguments => if choice then (arguments.val ()).2 else (arguments.val ()).1)).Realizable := by
      cases choice
      · exact pairProjection_realizable (binaryIntegers capacity) (binaryIntegers capacity) false
      · exact pairProjection_realizable (binaryIntegers capacity) (binaryIntegers capacity) true
    exact (((pairProjection_realizable (binaryIntegers width) coefficients true).followedBy projection rfl
      (by intros; trivial)).withArguments domains (MultiTape.oneTape (.inr ())) (fun _ => rfl)).withPrecondition
        allowed (by intros; trivial)
  let quotient (choice : Bool) sizes (arguments : {arguments : ∀ name, (domains name).Carrier sizes // allowed sizes arguments}) :=
    (integerQuotient width).compute sizes
      ⟨(fun name => if name then (arguments.val (.inr ())).1 else arguments.val (.inl choice)), arguments.property.2⟩
  have quotientReady (choice : Bool) :
      (Computation.mk domains (binaryIntegers width) allowed (quotient choice)).Realizable :=
    (integerQuotient_realizable width).onResults domains allowed
      (fun name _ arguments => if name then (arguments.val (.inr ())).1 else arguments.val (.inl choice))
      (fun _ arguments => arguments.property.2) (by
        intro name
        cases name
        · exact Realizable.argument domains (.inl choice) allowed
        · exact divisor.withPrecondition allowed (by intros; trivial))
  have lowerLeft := ((quotientReady true).followedBy (integerNegate_realizable width) rfl
    (by intros; trivial)).followedBy widen rfl (by intros; trivial)
  have lowerRight := (quotientReady false).followedBy widen rfl (by intros; trivial)
  let results (index : Fin 4) sizes (arguments : {arguments : ∀ name, (domains name).Carrier sizes // allowed sizes arguments}) :
      (binaryIntegers capacity).Carrier sizes := match index with
    | 0 => (arguments.val (.inr ())).2.1
    | 1 => (arguments.val (.inr ())).2.2
    | 2 => ⟨-(quotient true sizes arguments).val, by
        simpa only [Int.natAbs_neg] using ((quotient true sizes arguments).property.trans_le
          (pow_le_pow_right₀ (by decide) (by
            simp only [capacity, coefficientWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat]; omega)))⟩
    | 3 => ⟨(quotient false sizes arguments).val, (quotient false sizes arguments).property.trans_le
        (pow_le_pow_right₀ (by decide) (by
          simp only [capacity, coefficientWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat]; omega))⟩
  have assembled := Realizable.recordOutputs domains 4 (fun _ => binaryIntegers capacity) allowed results (by
    intro index
    fin_cases index
    · exact coefficient false
    · exact coefficient true
    · exact lowerLeft
    · exact lowerRight)
  apply assembled.withSpecification allowed (nonzeroStage width).compute (by intros; assumption)
  intro sizes arguments valid
  funext index
  apply Subtype.ext
  have divisorEq := divisor_eq width sizes arguments valid.1
  have gcdNonzero : Int.gcd (arguments (.inl false)).val (arguments (.inl true)).val ≠ 0 := by
    intro zero
    apply valid.2
    rw [divisorEq, zero, Int.natCast_zero]
  have leftEq := congrArg (fun result => result.2.1.val) valid.1
  have rightEq := congrArg (fun result => result.2.2.val) valid.1
  fin_cases index <;> simp [results, quotient, nonzeroStage, Computation.withPrecondition,
    stage, computation, entry, IntegerMatrix.bezoutMatrix, gcdNonzero, divisorEq,
    leftEq, rightEq, Realizable.Internal.integerNormalizedExtendedGcd_compute, integerQuotient, integerDivision]

def zeroAllowed (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (host width name).Carrier sizes) : Prop :=
  consistent width sizes arguments ∧ (arguments (.inr ())).1.val = 0

noncomputable def zeroStage (width : MvPolynomial Parameter ℕ) :=
  (stage width).withPrecondition (zeroAllowed width) (fun _ _ valid => valid.1)

theorem zeroStage_realizable (width : MvPolynomial Parameter ℕ) : (zeroStage width).Realizable := by
  let domains := host width
  let allowed := zeroAllowed width
  let capacity := coefficientWidth width
  have widen := integerWidenTo_realizable 1 (2 * width) capacity (by dsimp [capacity, coefficientWidth]; ring)
  let fixed (index : Fin 4) (_ : Empty → Bool) : {value : ℤ // value.natAbs < 2} :=
    if index = 0 ∨ index = 3 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  let value (index : Fin 4) sizes (_arguments : {arguments : ∀ name, (domains name).Carrier sizes // allowed sizes arguments}) :=
    ((integerBooleanOperation (Parameter := Parameter) (fixed index)).followedBy
      (integerWidenTo 1 (2 * width) capacity (by dsimp [capacity, coefficientWidth]; ring)) rfl (by intros; trivial)).compute sizes
      ⟨Empty.elim, trivial⟩
  have assembled := Realizable.recordOutputs domains 4 (fun _ => binaryIntegers capacity) allowed value (by
    intro index
    exact ((((integerBooleanOperation_realizable (Parameter := Parameter) (fixed index)).followedBy widen rfl
      (by intros; trivial)).withArguments domains ⟨Empty.elim, by intro name; exact name.elim⟩
        (by intro name; exact name.elim)).withPrecondition allowed (by intros; trivial)))
  apply assembled.withSpecification allowed (zeroStage width).compute (by intros; assumption)
  intro sizes arguments valid
  funext index
  apply Subtype.ext
  have gcdZero : Int.gcd (arguments (.inl false)).val (arguments (.inl true)).val = 0 := by
    have equal := (divisor_eq width sizes arguments valid.1).symm.trans valid.2
    exact_mod_cast equal
  fin_cases index <;> simp [value, fixed, integerBooleanOperation, Computation.followedBy,
    integerWidenTo, encodingMap, unaryMap, zeroStage, Computation.withPrecondition,
    stage, computation, entry, IntegerMatrix.bezoutMatrix, gcdZero]

theorem stage_realizable (width : MvPolynomial Parameter ℕ) : (stage width).Realizable := by
  let domains := host width
  let allowed := consistent width
  have guard := (((pairProjection_realizable (binaryIntegers width)
    ((binaryIntegers (coefficientWidth width)).prod (binaryIntegers (coefficientWidth width))) false).followedBy
      (integerIsZero_realizable width) rfl (by intros; trivial)).withArguments domains
        (MultiTape.oneTape (.inr ())) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  apply Realizable.ofCases (computation := stage width) (fun _ arguments => decide ((arguments (.inr ())).1.val = 0)) guard
  · exact (zeroStage_realizable width).withPrecondition _ (by
      intro sizes arguments valid
      exact ⟨valid.1, by simpa using valid.2⟩)
  · exact (nonzeroStage_realizable width).withPrecondition _ (by
      intro sizes arguments valid
      exact ⟨valid.1, by simpa using valid.2⟩)

theorem realizable (width : MvPolynomial Parameter ℕ) : (computation width).Realizable := by
  have complete := (integerNormalizedExtendedGcd_realizable width).letThen (stage_realizable width)
    (fun _ => rfl) rfl (by intros; rfl)
  exact complete.withSpecification (fun _ _ => True) (computation width).compute
    (by intros; trivial) (by intros; rfl)


/-- Reconstructing the four entries gives exactly the mathematical Bézout matrix. -/
theorem compute_matrix (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (computation width).Arguments sizes // True}) :
    !![((computation width).compute sizes arguments 0).val, ((computation width).compute sizes arguments 1).val;
      ((computation width).compute sizes arguments 2).val, ((computation width).compute sizes arguments 3).val] =
        IntegerMatrix.bezoutMatrix (arguments.val false).val (arguments.val true).val := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

end Polytime2.Computation.Realizable.Internal.BezoutCoefficients
