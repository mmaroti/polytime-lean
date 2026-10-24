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

import Polytime2.Arithmetic.NormalizedBezoutMath
import Polytime2.Arithmetic.SignedExtendedGcd
import Polytime2.Computation.Conditional

/-! # Certified normalization of Bézout coefficients

A shared polynomial workspace holds the original integers, their gcd, and the
extended-gcd coefficient. The nonzero branch uses exact division, remainder,
and the existing bounded multiply-subtract. The final coefficients are narrowed
to the linear width proved independently of this implementation.
-/

namespace Polytime2.Computation.Realizable.Internal.NormalizedBezout

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def resultWidth (width : MvPolynomial Parameter ℕ) := 2 * width + 1
noncomputable def rawWidth (width : MvPolynomial Parameter ℕ) := 1 + (2 * width + 1) * (width + 1)
noncomputable def workspaceWidth (width : MvPolynomial Parameter ℕ) := rawWidth width + resultWidth width + width

noncomputable def inputs (width : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter :=
  fun _ => binaryIntegers (workspaceWidth width)

def admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs width name).Carrier sizes) : Prop :=
  (arguments 0).val.natAbs < 2 ^ MvPolynomial.eval sizes width ∧
  (arguments 1).val.natAbs < 2 ^ MvPolynomial.eval sizes width ∧
  (arguments 2).val = (Int.gcd (arguments 0).val (arguments 1).val : ℤ) ∧
  (arguments 3).val = (ExtendedGcd.result (arguments 0).val (arguments 1).val).2.1

def nonzeroAllowed (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs width name).Carrier sizes) : Prop :=
  admissible width sizes arguments ∧ (arguments 1).val ≠ 0

omit [Fintype Parameter] in
private theorem width_le_workspace (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes width ≤ MvPolynomial.eval sizes (workspaceWidth width) := by
  simp only [workspaceWidth, map_add]
  omega

omit [Fintype Parameter] in
private theorem result_le_workspace (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes (resultWidth width) ≤ MvPolynomial.eval sizes (workspaceWidth width) := by
  simp only [workspaceWidth, map_add]
  omega

private noncomputable def quotient (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    (binaryIntegers (workspaceWidth width)).Carrier sizes :=
  ⟨(arguments.val 1).val / (arguments.val 2).val,
    (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments.val 1).property⟩

private theorem quotient_ne_zero (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    (quotient width sizes arguments).val ≠ 0 := by
  change (arguments.val 1).val / (arguments.val 2).val ≠ 0
  rw [arguments.property.1.2.2.1]
  exact ExtendedGcd.gcd_quotient_ne_zero_right _ _ arguments.property.2

private theorem remainder_bound (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    ((arguments.val 3).val % (quotient width sizes arguments).val).natAbs < 2 ^ MvPolynomial.eval sizes width := by
  change ((arguments.val 3).val % ((arguments.val 1).val / (arguments.val 2).val)).natAbs < _
  rw [arguments.property.1.2.2.1, arguments.property.1.2.2.2]
  exact ExtendedGcd.normalized_remainder_bound _ _ _ arguments.property.1.2.1 arguments.property.2

private noncomputable def remainder (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    (binaryIntegers (workspaceWidth width)).Carrier sizes :=
  ⟨(arguments.val 3).val % (quotient width sizes arguments).val,
    (remainder_bound width sizes arguments).trans_le
      (pow_le_pow_right₀ (by decide) (width_le_workspace width sizes))⟩

private theorem numerator_bound (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    ((arguments.val 2).val - (arguments.val 0).val * (remainder width sizes arguments).val).natAbs <
      2 ^ MvPolynomial.eval sizes (resultWidth width) := by
  change ((arguments.val 2).val - (arguments.val 0).val *
    ((arguments.val 3).val % ((arguments.val 1).val / (arguments.val 2).val))).natAbs < _
  rw [arguments.property.1.2.2.1, arguments.property.1.2.2.2]
  simpa only [resultWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
    ExtendedGcd.normalized_numerator_bound _ _ _ arguments.property.1.1 arguments.property.1.2.1 arguments.property.2

private noncomputable def numerator (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    (binaryIntegers (workspaceWidth width)).Carrier sizes :=
  ⟨(arguments.val 2).val - (arguments.val 0).val * (remainder width sizes arguments).val,
    (numerator_bound width sizes arguments).trans_le
      (pow_le_pow_right₀ (by decide) (result_le_workspace width sizes))⟩

private noncomputable def rightCoefficient (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs width name).Carrier sizes // nonzeroAllowed width sizes arguments}) :
    (binaryIntegers (workspaceWidth width)).Carrier sizes :=
  ⟨(numerator width sizes arguments).val / (arguments.val 1).val,
    (Int.natAbs_ediv_le_natAbs _ _).trans_lt (numerator width sizes arguments).property⟩

noncomputable def stage (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) where
  inputDomains := inputs width
  outputDomain := (binaryIntegers (resultWidth width)).prod (binaryIntegers (resultWidth width))
  precondition := admissible width
  compute sizes arguments :=
    let coefficients := ExtendedGcd.normalizedCoefficients (arguments.val 0).val (arguments.val 1).val
    let bounded := ExtendedGcd.normalizedCoefficients_bound (MvPolynomial.eval sizes width)
      (arguments.val 0).val (arguments.val 1).val arguments.property.1 arguments.property.2.1
    (⟨coefficients.1, by simpa only [resultWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using bounded.1⟩,
      ⟨coefficients.2, by simpa only [resultWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using bounded.2⟩)

noncomputable def nonzeroStage (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) :=
  (stage width).withPrecondition (nonzeroAllowed width) (fun _ _ valid => valid.1)

theorem nonzeroStage_realizable (width : MvPolynomial Parameter ℕ) : (nonzeroStage width).Realizable := by
  let domains := inputs width
  let allowed := nonzeroAllowed width
  let capacity := workspaceWidth width
  have quotientReady : (Computation.mk domains (binaryIntegers capacity) allowed (quotient width)).Realizable :=
    (integerQuotient_realizable capacity).onArguments domains allowed
      (fun choice => if choice then 2 else 1) (by intro choice; cases choice <;> rfl) (by
        intro sizes arguments
        change (arguments.val 2).val ≠ 0
        rw [arguments.property.1.2.2.1]
        intro zero
        have gcdZero : Int.gcd (arguments.val 0).val (arguments.val 1).val = 0 := by exact_mod_cast zero
        exact arguments.property.2 (Int.eq_zero_of_gcd_eq_zero_right gcdZero))
  have remainderReady : (Computation.mk domains (binaryIntegers capacity) allowed (remainder width)).Realizable :=
    (integerRemainder_realizable capacity).onResults domains allowed
      (fun choice sizes arguments => if choice then quotient width sizes arguments else arguments.val 3)
      (quotient_ne_zero width) (by
        intro choice
        cases choice
        · exact Realizable.argument domains 3 allowed
        · exact quotientReady)
  have numeratorReady : (Computation.mk domains (binaryIntegers capacity) allowed (numerator width)).Realizable :=
    (integerMultiplySubtract_realizable capacity).onResults domains allowed
      (fun name sizes arguments => match name with
        | 0 => arguments.val 2
        | 1 => arguments.val 0
        | 2 => remainder width sizes arguments)
      (by intro sizes arguments; exact (numerator width sizes arguments).property) (by
        intro name
        fin_cases name
        · exact Realizable.argument domains 2 allowed
        · exact Realizable.argument domains 0 allowed
        · exact remainderReady)
  have rightReady : (Computation.mk domains (binaryIntegers capacity) allowed (rightCoefficient width)).Realizable :=
    (integerQuotient_realizable capacity).onResults domains allowed
      (fun choice sizes arguments => if choice then arguments.val 1 else numerator width sizes arguments)
      (fun _ arguments => arguments.property.2) (by
        intro choice
        cases choice
        · exact numeratorReady
        · exact Realizable.argument domains 1 allowed)
  have leftNarrow := remainderReady.followedBy (integerNarrowAtWidths_realizable capacity (resultWidth width)
    (result_le_workspace width)) rfl (by
      intro sizes arguments valid
      exact (remainder_bound width sizes ⟨arguments, valid⟩).trans_le
        (pow_le_pow_right₀ (by decide) (by
          simp only [resultWidth, map_add, map_one, map_mul, MvPolynomial.eval_ofNat]
          omega)))
  have rightNarrow := rightReady.followedBy (integerNarrowAtWidths_realizable capacity (resultWidth width)
    (result_le_workspace width)) rfl (by
      intro sizes arguments valid
      exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (numerator_bound width sizes ⟨arguments, valid⟩))
  apply (leftNarrow.prodMk rightNarrow).withSpecification allowed (nonzeroStage width).compute (by intros; assumption)
  intro sizes arguments valid
  apply Prod.ext <;> apply Subtype.ext
  · change (arguments 3).val % ((arguments 1).val / (arguments 2).val) = _
    simp [nonzeroStage, Computation.withPrecondition, stage, ExtendedGcd.normalizedCoefficients, valid.2,
      valid.1.2.2.1, valid.1.2.2.2]
  · change ((arguments 2).val - (arguments 0).val *
      ((arguments 3).val % ((arguments 1).val / (arguments 2).val))) / (arguments 1).val = _
    simp [nonzeroStage, Computation.withPrecondition, stage, ExtendedGcd.normalizedCoefficients, valid.2,
      valid.1.2.2.1, valid.1.2.2.2]


def zeroAllowed (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs width name).Carrier sizes) : Prop :=
  admissible width sizes arguments ∧ (arguments 1).val = 0

noncomputable def zeroStage (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) :=
  (stage width).withPrecondition (zeroAllowed width) (fun _ _ valid => valid.1)

private theorem zero_coefficient (first : ℤ) :
    (if SignedEncoding.negative first then (-1 : ℤ) else 1) = if first = 0 then 1 else first.sign := by
  by_cases negative : first < 0
  · simp [SignedEncoding.negative, negative, ne_of_lt negative, Int.sign_eq_neg_one_of_neg negative]
  · by_cases zero : first = 0
    · simp [zero, SignedEncoding.negative]
    · have positive : 0 < first := by omega
      simp [SignedEncoding.negative, negative, zero, Int.sign_eq_one_of_pos positive]

theorem zeroStage_realizable (width : MvPolynomial Parameter ℕ) : (zeroStage width).Realizable := by
  let domains := inputs width
  let allowed := zeroAllowed width
  let capacity := resultWidth width
  have sameWidth : capacity = 1 + 2 * width := by dsimp [capacity, resultWidth]; ring
  have widen := integerWidenTo_realizable 1 (2 * width) capacity sameWidth
  let signValue (flags : Unit → Bool) : {value : ℤ // value.natAbs < 2} :=
    if flags () then ⟨-1, by decide⟩ else ⟨1, by decide⟩
  have negative := ((integerNegative_realizable (workspaceWidth width)).withArguments domains
    (MultiTape.oneTape 0) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  have signed := (negative.followedBy (integerBooleanOperation_realizable signValue) rfl (by intros; trivial)).followedBy
    widen rfl (by intros; trivial)
  have zero := (((integerBooleanOperation_realizable (Parameter := Parameter) (Argument := Empty)
    (fun _ => ⟨0, by decide⟩)).followedBy widen rfl (by intros; trivial)).withArguments domains
      ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)).withPrecondition allowed
        (by intros; trivial)
  apply (signed.prodMk zero).withSpecification allowed (zeroStage width).compute (by intros; assumption)
  intro sizes arguments valid
  apply Prod.ext <;> apply Subtype.ext
  · have correct := zero_coefficient (arguments 0).val
    cases negative : SignedEncoding.negative (arguments 0).val <;>
      simpa [zeroStage, Computation.withPrecondition, stage, ExtendedGcd.normalizedCoefficients,
        valid.2, Computation.followedBy, Computation.withArguments, integerBooleanOperation,
        signValue, integerWidenTo, encodingMap, unaryMap, integerNegative, negative] using correct
  · simp [zeroStage, Computation.withPrecondition, stage, ExtendedGcd.normalizedCoefficients, valid.2,
      Computation.followedBy, Computation.withArguments, integerBooleanOperation,
      integerWidenTo, encodingMap, unaryMap]

theorem stage_realizable (width : MvPolynomial Parameter ℕ) : (stage width).Realizable := by
  let domains := inputs width
  let allowed := admissible width
  have guard := ((integerIsZero_realizable (workspaceWidth width)).withArguments domains
    (MultiTape.oneTape 1) (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
  apply Realizable.ofCases (computation := stage width) (fun _ arguments => decide ((arguments 1).val = 0)) guard
  · exact (zeroStage_realizable width).withPrecondition _ (by
      intro sizes arguments valid
      exact ⟨valid.1, by simpa using valid.2⟩)
  · exact (nonzeroStage_realizable width).withPrecondition _ (by
      intro sizes arguments valid
      exact ⟨valid.1, by simpa using valid.2⟩)

end Polytime2.Computation.Realizable.Internal.NormalizedBezout

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Extended gcd with actual normalized coefficients at derived linear width.
All signed pairs are admissible, including the zero pair, whose coefficients
are `(1,0)`. The gcd retains the input magnitude width. -/
noncomputable def integerNormalizedExtendedGcd (width : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (binaryIntegers width).prod
    ((binaryIntegers (2 * width + 1)).prod (binaryIntegers (2 * width + 1)))
  precondition _ _ := True
  compute sizes arguments :=
    let raw := ExtendedGcd.result (arguments.val false).val (arguments.val true).val
    let coefficients := ExtendedGcd.normalizedCoefficients (arguments.val false).val (arguments.val true).val
    let rawBound := ExtendedGcd.result_bounds (MvPolynomial.eval sizes width) _ _
      (arguments.val false).property (arguments.val true).property
    let coefficientBound := ExtendedGcd.normalizedCoefficients_bound (MvPolynomial.eval sizes width) _ _
      (arguments.val false).property (arguments.val true).property
    (⟨(raw.1 : ℤ), by simpa only [Int.natAbs_natCast] using rawBound.1⟩,
      ⟨coefficients.1, by simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using coefficientBound.1⟩,
      ⟨coefficients.2, by simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using coefficientBound.2⟩)

theorem integerNormalizedExtendedGcd_realizable (width : MvPolynomial Parameter ℕ) :
    (integerNormalizedExtendedGcd width).Realizable := by
  let source := integerExtendedGcd width
  let domains := Sum.elim source.inputDomains (fun _ : Unit => source.outputDomain)
  let allowed sizes (arguments : ∀ name, (domains name).Carrier sizes) :=
    arguments (.inr ()) = source.compute sizes ⟨(fun name => arguments (.inl name)), trivial⟩
  let capacity := Realizable.Internal.NormalizedBezout.workspaceWidth width
  let coefficientWidth := Realizable.Internal.NormalizedBezout.resultWidth width
  let rawWidth := Realizable.Internal.NormalizedBezout.rawWidth width
  have inputEqual : capacity = width + (rawWidth + coefficientWidth) := by
    dsimp [capacity, Realizable.Internal.NormalizedBezout.workspaceWidth, rawWidth, coefficientWidth]
    ring
  have rawEqual : capacity = rawWidth + (coefficientWidth + width) := by
    dsimp [capacity, Realizable.Internal.NormalizedBezout.workspaceWidth, rawWidth, coefficientWidth]
    ring
  let widenInput := Realizable.Internal.integerWidenTo width (rawWidth + coefficientWidth) capacity inputEqual
  let widenRaw := Realizable.Internal.integerWidenTo rawWidth (coefficientWidth + width) capacity rawEqual
  have inputReady := Realizable.Internal.integerWidenTo_realizable width (rawWidth + coefficientWidth) capacity inputEqual
  have rawReady := Realizable.Internal.integerWidenTo_realizable rawWidth (coefficientWidth + width) capacity rawEqual
  let values (name : Fin 4) sizes
      (arguments : {arguments : ∀ name, (domains name).Carrier sizes // allowed sizes arguments}) :
      (Realizable.Internal.NormalizedBezout.inputs width name).Carrier sizes :=
    match name with
    | 0 => widenInput.compute sizes ⟨(fun _ => arguments.val (.inl false)), trivial⟩
    | 1 => widenInput.compute sizes ⟨(fun _ => arguments.val (.inl true)), trivial⟩
    | 2 => widenInput.compute sizes ⟨(fun _ => (arguments.val (.inr ())).1), trivial⟩
    | 3 => widenRaw.compute sizes ⟨(fun _ => (arguments.val (.inr ())).2.1), trivial⟩
  have divisor := (pairProjection_realizable (binaryIntegers width)
    ((binaryIntegers rawWidth).prod (binaryIntegers rawWidth)) false).withArguments domains
      (MultiTape.oneTape (.inr ())) (fun _ => rfl)
  have leftCoefficient := ((pairProjection_realizable (binaryIntegers width)
    ((binaryIntegers rawWidth).prod (binaryIntegers rawWidth)) true).fst).withArguments domains (MultiTape.oneTape (.inr ())) (fun _ => rfl)
  have producers (name : Fin 4) : (Computation.mk domains
      (Realizable.Internal.NormalizedBezout.inputs width name) allowed (values name)).Realizable := by
    fin_cases name
    · exact (inputReady.withArguments domains (MultiTape.oneTape (.inl false)) (fun _ => rfl)).withPrecondition
        allowed (by intros; trivial)
    · exact (inputReady.withArguments domains (MultiTape.oneTape (.inl true)) (fun _ => rfl)).withPrecondition
        allowed (by intros; trivial)
    · exact (divisor.followedBy inputReady rfl (by intros; trivial)).withPrecondition allowed (by intros; trivial)
    · exact (leftCoefficient.followedBy rawReady rfl (by intros; trivial)).withPrecondition allowed (by intros; trivial)
  have compatible sizes arguments : (Realizable.Internal.NormalizedBezout.stage width).precondition sizes
      (fun name => values name sizes arguments) := by
    change Realizable.Internal.NormalizedBezout.admissible width sizes (fun name => values name sizes arguments)
    dsimp only [Realizable.Internal.NormalizedBezout.admissible, values, widenInput, widenRaw,
      Realizable.Internal.integerWidenTo, encodingMap, unaryMap]
    refine ⟨(arguments.val (.inl false)).property, (arguments.val (.inl true)).property, ?_, ?_⟩
    · exact (congrArg (fun result => result.1.val) arguments.property).trans
        (integerExtendedGcd_correct width sizes (fun name => arguments.val (.inl name))).2.1
    · exact congrArg (fun result => result.2.1.val) arguments.property
  have coefficients := (Realizable.Internal.NormalizedBezout.stage_realizable width).onResults
    domains allowed values compatible producers
  have packaged := (divisor.withPrecondition allowed (by intros; trivial)).prodMk coefficients
  have result := (integerExtendedGcd_realizable width).letThen packaged (fun _ => rfl) rfl (by intros; rfl)
  exact result.withSpecification (fun _ _ => True) (integerNormalizedExtendedGcd width).compute
    (by intros; trivial) (by intros; rfl)

theorem integerNormalizedExtendedGcd_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerNormalizedExtendedGcd width).Arguments sizes) :
    let result := (integerNormalizedExtendedGcd width).compute sizes ⟨arguments, trivial⟩
    result.1.val = (Int.gcd (arguments false).val (arguments true).val : ℤ) ∧
      (arguments false).val * result.2.1.val + (arguments true).val * result.2.2.val = result.1.val := by
  have gcdCorrect := (ExtendedGcd.result_correct (arguments false).val (arguments true).val).1
  constructor
  · exact congrArg (fun value : ℕ => (value : ℤ)) gcdCorrect
  · simpa only [integerNormalizedExtendedGcd, gcdCorrect] using
      ExtendedGcd.normalizedCoefficients_correct (arguments false).val (arguments true).val

end Polytime2.Computation
