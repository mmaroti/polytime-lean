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

import Polytime2.Arithmetic.SignedExtendedGcdMath
import Polytime2.Arithmetic.SignedMultiplySubtract
import Polytime2.Arithmetic.SignedDivision
import Polytime2.Computation.While

/-! # Certified extended gcd of signed integers

All pairs of integers at magnitude width `w` are admissible. The result is a
nonnegative gcd at width `w` and two actual integer Bézout coefficients at a
quadratic width derived from `w`. Euclidean progress, every coefficient bound,
and the bit costs of constituent arithmetic are included in the certificate.
-/

namespace Polytime2.Computation.Realizable.Internal.IntegerExtendedGcd

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def coefficientWidth (width : MvPolynomial Parameter ℕ) : MvPolynomial Parameter ℕ :=
  1 + (2 * width + 1) * (width + 1)

omit [Fintype Parameter] in
@[simp] theorem eval_coefficientWidth (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes (coefficientWidth width) = ExtendedGcd.coefficientWidth (MvPolynomial.eval sizes width) := by
  simp [coefficientWidth, ExtendedGcd.coefficientWidth, Nat.add_comm]

private theorem width_le (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    MvPolynomial.eval sizes width ≤ MvPolynomial.eval sizes (coefficientWidth width) := by
  simp only [eval_coefficientWidth, ExtendedGcd.coefficientWidth]
  nlinarith

/-- Homogeneous private storage keeps all six live coordinates at one capacity. -/
noncomputable def state (width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  EncodedDomain.record 6 (fun _ => binaryIntegers (coefficientWidth width))

def forget (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : ExtendedGcd.Value :=
  (((value 0).val.natAbs, (value 1).val.natAbs),
    (((value 2).val, (value 3).val), ((value 4).val, (value 5).val)))

def admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : Prop :=
  0 ≤ (value 0).val ∧ 0 ≤ (value 1).val ∧
    ExtendedGcd.admissible (MvPolynomial.eval sizes width) (forget width sizes value)

noncomputable def pack (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : ExtendedGcd.Value) (valid : ExtendedGcd.admissible (MvPolynomial.eval sizes width) value) :
    (state width).Carrier sizes :=
  let coefficientBound := ExtendedGcd.coefficient_capacity (MvPolynomial.eval sizes width) value valid
  let wider : 2 ^ MvPolynomial.eval sizes width ≤ 2 ^ MvPolynomial.eval sizes (coefficientWidth width) :=
    pow_le_pow_right₀ (by decide) (width_le width sizes)
  ![⟨(value.1.1 : ℤ), by simpa only [Int.natAbs_natCast] using valid.1.1.trans_le wider⟩,
    ⟨(value.1.2 : ℤ), by simpa only [Int.natAbs_natCast] using valid.1.2.trans_le wider⟩,
    ⟨value.2.1.1, by simpa only [eval_coefficientWidth] using coefficientBound.1⟩,
    ⟨value.2.1.2, by simpa only [eval_coefficientWidth] using coefficientBound.2.1⟩,
    ⟨value.2.2.1, by simpa only [eval_coefficientWidth] using coefficientBound.2.2.1⟩,
    ⟨value.2.2.2, by simpa only [eval_coefficientWidth] using coefficientBound.2.2.2⟩]

@[simp] theorem forget_pack (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : ExtendedGcd.Value) (valid : ExtendedGcd.admissible (MvPolynomial.eval sizes width) value) :
    forget width sizes (pack width sizes value valid) = value := by
  rcases value with ⟨⟨first, second⟩, ⟨⟨left, right⟩, ⟨nextLeft, nextRight⟩⟩⟩
  simp [forget, pack]

theorem pack_admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : ExtendedGcd.Value) (valid : ExtendedGcd.admissible (MvPolynomial.eval sizes width) value) :
    admissible width sizes (pack width sizes value valid) := by
  exact ⟨Int.natCast_nonneg _, Int.natCast_nonneg _, by simpa only [forget_pack] using valid⟩

theorem pack_forget (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) (valid : admissible width sizes value) :
    pack width sizes (forget width sizes value) valid.2.2 = value := by
  funext index
  apply Subtype.ext
  fin_cases index
  · exact Int.natAbs_of_nonneg valid.1
  · exact Int.natAbs_of_nonneg valid.2.1
  all_goals rfl

def condition (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : Bool := Gcd.condition (forget width sizes value).1

noncomputable def advance (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes // admissible width sizes value ∧ condition width sizes value = true}) :
    (state width).Carrier sizes :=
  pack width sizes (ExtendedGcd.advance (forget width sizes value.val))
    (ExtendedGcd.advance_admissible _ _ value.property.1.2.2 value.property.2)

private theorem quotient_eq (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) (valid : admissible width sizes value) :
    (value 0).val / (value 1).val =
      ((forget width sizes value).1.1 / (forget width sizes value).1.2 : ℕ) := by
  calc
    _ = ((value 0).val.natAbs : ℤ) / ((value 1).val.natAbs : ℤ) :=
      congrArg₂ (fun first second : ℤ => first / second) (Int.natAbs_of_nonneg valid.1).symm
        (Int.natAbs_of_nonneg valid.2.1).symm
    _ = _ := (Int.natCast_ediv _ _).symm

private theorem remainder_eq (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) (valid : admissible width sizes value) :
    (value 0).val % (value 1).val =
      ((forget width sizes value).1.1 % (forget width sizes value).1.2 : ℕ) := by
  calc
    _ = ((value 0).val.natAbs : ℤ) % ((value 1).val.natAbs : ℤ) :=
      congrArg₂ (fun first second : ℤ => first % second) (Int.natAbs_of_nonneg valid.1).symm
        (Int.natAbs_of_nonneg valid.2.1).symm
    _ = _ := (Int.natCast_emod _ _).symm

def active (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : Prop :=
  admissible width sizes value ∧ condition width sizes value = true

noncomputable def quotient (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (state width) (binaryIntegers (coefficientWidth width)) (active width)
    (fun sizes value => ⟨((forget width sizes value.val).1.1 / (forget width sizes value.val).1.2 : ℕ), by
      simpa only [Int.natAbs_natCast, forget] using
        (Nat.div_le_self (value.val 0).val.natAbs (value.val 1).val.natAbs).trans_lt (value.val 0).property⟩)

private theorem division_realizable (width : MvPolynomial Parameter ℕ) :
    (unaryMap (state width)
      ((binaryIntegers (coefficientWidth width)).prod (binaryIntegers (coefficientWidth width))) (active width)
      (fun sizes value => ((quotient width).compute sizes ⟨(fun _ => value.val), value.property⟩,
        advance width sizes value 1))).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => state width
  let allowed := fun sizes (arguments : Unit → (state width).Carrier sizes) => active width sizes (arguments ())
  have divided := (integerDivision_realizable (coefficientWidth width)).onResults inputs allowed
    (fun name _ arguments => arguments.val () (if name then 1 else 0)) (by
      intro sizes arguments
      change (arguments.val () 1).val ≠ 0
      exact Int.natAbs_ne_zero.mp (of_decide_eq_true arguments.property.2)) (by
      intro name
      exact (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width))
        (if name then 1 else 0)).withPrecondition allowed (by intros; trivial))
  exact divided.withSpecification allowed _ (by intros; assumption) (by
    intro sizes arguments valid
    apply Prod.ext
    · exact Subtype.ext (quotient_eq width sizes (arguments ()) valid.1)
    · exact Subtype.ext (remainder_eq width sizes (arguments ()) valid.1))

theorem quotient_realizable (width : MvPolynomial Parameter ℕ) : (quotient width).Realizable :=
  (division_realizable width).followedBy
    (pairProjection_realizable (binaryIntegers (coefficientWidth width)) (binaryIntegers (coefficientWidth width)) false)
    rfl (by intros; trivial)

theorem remainder_realizable (width : MvPolynomial Parameter ℕ) :
    (unaryMap (state width) (binaryIntegers (coefficientWidth width)) (active width)
      (fun sizes value => advance width sizes value 1)).Realizable :=
  (division_realizable width).followedBy
    (pairProjection_realizable (binaryIntegers (coefficientWidth width)) (binaryIntegers (coefficientWidth width)) true)
    rfl (by intros; trivial)

theorem coefficient_realizable (width : MvPolynomial Parameter ℕ) (second : Bool) :
    (unaryMap (state width) (binaryIntegers (coefficientWidth width)) (active width)
      (fun sizes value => advance width sizes value (if second then 5 else 4))).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => state width
  let allowed := fun sizes (arguments : Unit → (state width).Carrier sizes) => active width sizes (arguments ())
  let sources (sizes : Parameter → ℕ) (arguments : {arguments : Unit → (state width).Carrier sizes // allowed sizes arguments}) :
      Fin 3 → (binaryIntegers (coefficientWidth width)).Carrier sizes :=
    ![arguments.val () (if second then 3 else 2), arguments.val () (if second then 5 else 4),
      (quotient width).compute sizes arguments]
  have update := (integerMultiplySubtract_realizable (coefficientWidth width)).onResults inputs allowed (fun name sizes arguments => sources sizes arguments name) (by
    intro sizes arguments
    have bounded := ExtendedGcd.coefficient_capacity (MvPolynomial.eval sizes width)
      (ExtendedGcd.advance (forget width sizes (arguments.val ())))
      (ExtendedGcd.advance_admissible _ _ arguments.property.1.2.2 arguments.property.2)
    cases second
    · change ((arguments.val () 2).val - (arguments.val () 4).val *
        ((forget width sizes (arguments.val ())).1.1 / (forget width sizes (arguments.val ())).1.2 : ℕ)).natAbs < _
      simpa only [eval_coefficientWidth, ExtendedGcd.advance, forget, mul_comm] using bounded.2.2.1
    · change ((arguments.val () 3).val - (arguments.val () 5).val *
        ((forget width sizes (arguments.val ())).1.1 / (forget width sizes (arguments.val ())).1.2 : ℕ)).natAbs < _
      simpa only [eval_coefficientWidth, ExtendedGcd.advance, forget, mul_comm] using bounded.2.2.2) (by
    intro name
    fin_cases name
    · exact (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width))
        (if second then 3 else 2)).withPrecondition allowed (by intros; trivial)
    · exact (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width))
        (if second then 5 else 4)).withPrecondition allowed (by intros; trivial)
    · exact quotient_realizable width)
  exact update.withSpecification allowed _ (by intros; assumption) (by
    intro sizes arguments valid
    apply Subtype.ext
    cases second
    · change (arguments () 2).val - (arguments () 4).val *
        ((forget width sizes (arguments ())).1.1 / (forget width sizes (arguments ())).1.2 : ℕ) =
        (arguments () 2).val - ((forget width sizes (arguments ())).1.1 /
          (forget width sizes (arguments ())).1.2 : ℕ) * (arguments () 4).val
      ring
    · change (arguments () 3).val - (arguments () 5).val *
        ((forget width sizes (arguments ())).1.1 / (forget width sizes (arguments ())).1.2 : ℕ) =
        (arguments () 3).val - ((forget width sizes (arguments ())).1.1 /
          (forget width sizes (arguments ())).1.2 : ℕ) * (arguments () 5).val
      ring)

theorem advance_realizable (width : MvPolynomial Parameter ℕ) :
    (unaryMap (state width) (state width) (active width) (advance width)).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => state width
  let allowed := fun sizes (arguments : Unit → (state width).Carrier sizes) => active width sizes (arguments ())
  exact (recordConstructor_realizable 6 (fun _ => binaryIntegers (coefficientWidth width))).onResults inputs allowed
    (fun index sizes arguments => advance width sizes ⟨arguments.val (), arguments.property⟩ index)
    (by intros; trivial) (by
      intro index
      fin_cases index
      · have projection := (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 1).withPrecondition allowed
          (by intros; trivial)
        exact projection.withSpecification allowed _ (by intros; assumption) (by
          intro sizes arguments valid
          apply Subtype.ext
          exact (Int.natAbs_of_nonneg valid.1.2.1).symm)
      · exact remainder_realizable width
      · exact (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 4).withPrecondition allowed
          (by intros; trivial)
      · exact (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 5).withPrecondition allowed
          (by intros; trivial)
      · exact coefficient_realizable width false
      · exact coefficient_realizable width true)

private noncomputable def smallWiden (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryIntegers 1) (binaryIntegers (coefficientWidth width)) (fun sizes value =>
    ⟨value.val, value.property.trans_le (pow_le_pow_right₀ (by decide) (by
      simp only [map_one, eval_coefficientWidth, ExtendedGcd.coefficientWidth]
      omega))⟩)

private theorem smallWiden_realizable (width : MvPolynomial Parameter ℕ) : (smallWiden width).Realizable := by
  exact integerWiden_realizable 1 ((2 * width + 1) * (width + 1))

private theorem magnitude_realizable (width : MvPolynomial Parameter ℕ) :
    (encodingMap (binaryIntegers width) (binaryIntegers (coefficientWidth width))
      (fun sizes value => ⟨(value.val.natAbs : ℤ), by
        simpa only [Int.natAbs_natCast] using value.property.trans_le
          (pow_le_pow_right₀ (by decide) (width_le width sizes))⟩)).Realizable := by
  have magnitude := ((integerMagnitude_realizable width).followedBy (integerOfMagnitude_realizable width) rfl
    (by intros; trivial)).followedBy (integerWiden_realizable width (2 * width * (width + 1) + 2)) rfl
      (by intros; trivial)
  have sameWidth : coefficientWidth width = width + (2 * width * (width + 1) + 2) := by
    unfold coefficientWidth
    ring
  exact magnitude.withEncodedOutput (binaryIntegers (coefficientWidth width)) _
    (by intro sizes; change (binaryIntegers (coefficientWidth width)).width sizes =
        (binaryIntegers (width + (2 * width * (width + 1) + 2))).width sizes
        rw [sameWidth]) (by
      intro sizes arguments
      exact congrArg CallingConvention.tape
        (binaryIntegers_encode_congr _ _ sameWidth sizes _ _ rfl))

private theorem sign_realizable (width : MvPolynomial Parameter ℕ) :
    (encodingMap (binaryIntegers width) (binaryIntegers (coefficientWidth width))
      (fun sizes value => ⟨value.val.sign, by
        have positive : 1 < 2 ^ MvPolynomial.eval sizes (coefficientWidth width) := by
          apply Nat.one_lt_pow _ (by decide)
          simp only [eval_coefficientWidth, ExtendedGcd.coefficientWidth]
          omega
        rw [Int.natAbs_sign]
        split <;> omega⟩)).Realizable := by
  let operation (flags : Bool → Bool) : {value : ℤ // value.natAbs < 2} :=
    if flags true then ⟨0, by decide⟩ else if flags false then ⟨-1, by decide⟩ else ⟨1, by decide⟩
  have signs := (integerBooleanOperation_realizable (Parameter := Parameter) operation).onResults
    (fun _ : Unit => binaryIntegers width) (fun _ _ => True)
    (fun name _ arguments => if name then decide ((arguments.val ()).val = 0)
      else SignedEncoding.negative (arguments.val ()).val) (by intros; trivial) (by
      intro name
      cases name
      · exact integerNegative_realizable width
      · exact integerIsZero_realizable width)
  have widened := signs.followedBy (smallWiden_realizable width) rfl (by intros; trivial)
  exact widened.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
    intro sizes arguments valid
    apply Subtype.ext
    change (operation (fun name => if name then decide ((arguments ()).val = 0)
      else SignedEncoding.negative (arguments ()).val)).val = (arguments ()).val.sign
    rcases lt_trichotomy (arguments ()).val 0 with negative | zero | positive
    · simp [operation, SignedEncoding.negative, negative, ne_of_lt negative,
        Int.sign_eq_neg_one_of_neg negative]
    · simp [operation, zero]
    · simp [operation, SignedEncoding.negative, ne_of_gt positive, not_lt_of_gt positive,
        Int.sign_eq_one_of_pos positive])

noncomputable def initialState (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := state width
  precondition _ _ := True
  compute sizes arguments := pack width sizes (ExtendedGcd.initial (arguments.val false).val (arguments.val true).val)
    (ExtendedGcd.initial_admissible _ _ _ (arguments.val false).property (arguments.val true).property)

theorem initialState_realizable (width : MvPolynomial Parameter ℕ) : (initialState width).Realizable := by
  let inputs := (initialState width).inputDomains
  have zero := (integerBooleanOperation_realizable (Parameter := Parameter) (Argument := Empty)
    (fun _ => ⟨0, by decide⟩)).followedBy (smallWiden_realizable width) rfl (by intros; trivial)
  have zeroReady := zero.withArguments inputs
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  exact (recordConstructor_realizable 6 (fun _ => binaryIntegers (coefficientWidth width))).onResults inputs (fun _ _ => True)
    (fun index sizes arguments => (initialState width).compute sizes arguments index) (by intros; trivial) (by
      intro index
      fin_cases index
      · exact (magnitude_realizable width).withArguments inputs (MultiTape.oneTape false) (fun _ => rfl)
      · exact (magnitude_realizable width).withArguments inputs (MultiTape.oneTape true) (fun _ => rfl)
      · exact (sign_realizable width).withArguments inputs (MultiTape.oneTape false) (fun _ => rfl)
      · exact zeroReady
      · exact zeroReady
      · exact (sign_realizable width).withArguments inputs (MultiTape.oneTape true) (fun _ => rfl))

noncomputable def answer (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes // admissible width sizes value}) : (state width).Carrier sizes :=
  pack width sizes (ExtendedGcd.run (forget width sizes value.val))
    (ExtendedGcd.run_admissible _ _ value.property.2.2)

theorem answer_admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes // admissible width sizes value}) :
    admissible width sizes (answer width sizes value) :=
  pack_admissible width sizes (ExtendedGcd.run (forget width sizes value.val))
    (ExtendedGcd.run_admissible _ _ value.property.2.2)

theorem initialState_admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {_arguments : (initialState width).Arguments sizes // True}) :
    admissible width sizes ((initialState width).compute sizes arguments) :=
  pack_admissible width sizes (ExtendedGcd.initial (arguments.val false).val (arguments.val true).val)
    (ExtendedGcd.initial_admissible _ _ _ (arguments.val false).property (arguments.val true).property)

theorem loop_realizable (width : MvPolynomial Parameter ℕ) :
    (unaryMap (state width) (state width) (admissible width) (answer width)).Realizable := by
  refine Realizable.whileLoop (state width) (admissible width) (condition width) (advance width) (answer width)
    (fun sizes value => Gcd.measure (forget width sizes value).1) ?_ (advance_realizable width) ?_ ?_ ?_ ?_ ?_
  · have guard := (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 1).followedBy
      (integerIsZero_realizable (coefficientWidth width)) rfl (by intros; trivial)
    have inverted := guard.followedBy
      (booleanOperation_realizable (Parameter := Parameter) (Argument := Unit) (fun flags => !flags ()))
      rfl (by intros; trivial)
    exact inverted.withSpecification (fun sizes arguments => admissible width sizes (arguments ())) _ (by intros; trivial) (by
      intro sizes arguments valid
      change (!decide ((arguments () 1).val = 0)) = decide ((arguments () 1).val.natAbs ≠ 0)
      simp)
  · intro sizes value
    exact pack_admissible width sizes _ _
  · intro sizes value
    change Gcd.measure (forget width sizes (pack width sizes _ _)).1 < _
    rw [forget_pack]
    exact Gcd.decreases _ value.property.2
  · intro sizes value
    unfold answer
    congr 1
    change ExtendedGcd.run (forget width sizes (advance width sizes value)) = _
    rw [advance, forget_pack]
    exact ExtendedGcd.run_step _ value.property.2
  · intro sizes value stopped
    have terminal : ExtendedGcd.run (forget width sizes value.val) = forget width sizes value.val := by
      rw [ExtendedGcd.run]
      have stoppedGuard : Gcd.condition (forget width sizes value.val).1 = false := stopped
      simp only [stoppedGuard, Bool.false_eq_true, ↓reduceDIte]
    unfold answer
    refine Eq.trans ?_ (pack_forget width sizes value.val value.property)
    congr 1
  · refine ⟨2 * width + 1, ?_⟩
    intro sizes value valid
    simpa only [map_add, map_mul, map_ofNat, map_one] using
      Gcd.measure_bound (MvPolynomial.eval sizes width) (forget width sizes value).1 valid.2.2.1

noncomputable def extract (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (state width) ((binaryIntegers width).prod
    ((binaryIntegers (coefficientWidth width)).prod (binaryIntegers (coefficientWidth width)))) (admissible width)
    (fun _ value => (⟨(value.val 0).val, value.property.2.2.1.1⟩, value.val 2, value.val 3))

theorem extract_realizable (width : MvPolynomial Parameter ℕ) : (extract width).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => state width
  let allowed := fun sizes (arguments : Unit → (state width).Carrier sizes) => admissible width sizes (arguments ())
  have first := ((recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 0).withPrecondition
    allowed (by intros; trivial)).followedBy (integerNarrowAtWidths_realizable (coefficientWidth width) width
      (width_le width)) rfl (by intro sizes arguments valid; exact valid.2.2.1.1)
  have left := (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 2).withPrecondition
    allowed (by intros; trivial)
  have right := (recordProjection_realizable 6 (fun _ => binaryIntegers (coefficientWidth width)) 3).withPrecondition
    allowed (by intros; trivial)
  have coefficients := Realizable.pairOutputs inputs (binaryIntegers (coefficientWidth width))
    (binaryIntegers (coefficientWidth width)) allowed _ _ left right
  exact Realizable.pairOutputs inputs (binaryIntegers width)
    ((binaryIntegers (coefficientWidth width)).prod (binaryIntegers (coefficientWidth width))) allowed _ _ first coefficients

end Polytime2.Computation.Realizable.Internal.IntegerExtendedGcd



namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Extended gcd returns the nonnegative gcd and bounded Bézout coefficients.
Every operand pair is admissible, including `(0,0)`. -/
noncomputable def integerExtendedGcd (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := (binaryIntegers width).prod
    ((binaryIntegers (1 + (2 * width + 1) * (width + 1))).prod
      (binaryIntegers (1 + (2 * width + 1) * (width + 1))))
  precondition _ _ := True
  compute sizes arguments :=
    let result := ExtendedGcd.result (arguments.val false).val (arguments.val true).val
    let bound := ExtendedGcd.result_bounds (MvPolynomial.eval sizes width)
      (arguments.val false).val (arguments.val true).val (arguments.val false).property (arguments.val true).property
    (⟨(result.1 : ℤ), by simpa only [Int.natAbs_natCast] using bound.1⟩,
      ⟨result.2.1, by simpa [ExtendedGcd.coefficientWidth, Nat.add_comm] using bound.2.1⟩,
      ⟨result.2.2, by simpa [ExtendedGcd.coefficientWidth, Nat.add_comm] using bound.2.2⟩)

theorem integerExtendedGcd_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerExtendedGcd width).Arguments sizes) :
    let result := (integerExtendedGcd width).compute sizes ⟨arguments, trivial⟩
    0 ≤ result.1.val ∧ result.1.val = (Int.gcd (arguments false).val (arguments true).val : ℤ) ∧
      result.2.1.val * (arguments false).val + result.2.2.val * (arguments true).val = result.1.val := by
  have correct := ExtendedGcd.result_correct (arguments false).val (arguments true).val
  exact ⟨Int.natCast_nonneg _, congrArg (fun number : ℕ => (number : ℤ)) correct.1, correct.2⟩

theorem integerExtendedGcd_realizable (width : MvPolynomial Parameter ℕ) :
    (integerExtendedGcd width).Realizable := by
  have loop := (Realizable.Internal.IntegerExtendedGcd.initialState_realizable width).followedBy
    (Realizable.Internal.IntegerExtendedGcd.loop_realizable width) rfl (by
      intro sizes arguments valid
      exact Realizable.Internal.IntegerExtendedGcd.initialState_admissible width sizes ⟨arguments, valid⟩)
  have complete := loop.followedBy (Realizable.Internal.IntegerExtendedGcd.extract_realizable width) rfl (by
    intro sizes arguments valid
    apply Realizable.Internal.IntegerExtendedGcd.answer_admissible)
  exact complete.withSpecification (fun _ _ => True) (integerExtendedGcd width).compute
    (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
