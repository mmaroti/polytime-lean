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

import Polytime2.Arithmetic.NaturalShifts
import Polytime2.Arithmetic.SignedDivision
import Polytime2.Arithmetic.SignedWidth

/-! # Exact signed left shifts

Every integer of magnitude width `w` is admissible. A shift count `s` is a
mathematical size polynomial; the result is multiplication by `2^s` and has
magnitude width `w+s`. Output construction is included in the runtime bound.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerShiftLeft (width amount : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryIntegers width) (binaryIntegers (width + amount)) (fun sizes value =>
    ⟨value.val * (2 ^ MvPolynomial.eval sizes amount : ℕ), by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast, map_add, pow_add] using
        Nat.mul_lt_mul_of_pos_right value.property (show 0 < 2 ^ MvPolynomial.eval sizes amount by positivity)⟩)

theorem integerShiftLeft_correct (width amount : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerShiftLeft width amount).Arguments sizes) :
    ((integerShiftLeft width amount).compute sizes ⟨arguments, trivial⟩).val =
      (arguments ()).val <<< MvPolynomial.eval sizes amount := by
  exact (Int.shiftLeft_eq' (arguments ()).val (MvPolynomial.eval sizes amount)).symm

theorem integerShiftLeft_realizable (width amount : MvPolynomial Parameter ℕ) :
    (integerShiftLeft width amount).Realizable := by
  have magnitude := (integerMagnitude_realizable width).followedBy
    (Realizable.Internal.naturalShiftLeft_realizable width amount) rfl (by intros; trivial)
  have constructed := ((integerNegative_realizable width).prodMk magnitude).followedBy (Realizable.Internal.integerOfParts_realizable (width + amount)) rfl (by
    intro sizes arguments valid
    change SignedEncoding.negative (arguments ()).val = true →
      (arguments ()).val.natAbs * 2 ^ MvPolynomial.eval sizes amount ≠ 0
    intro negative
    apply Nat.mul_ne_zero
    · exact Int.natAbs_ne_zero.mpr (ne_of_lt (of_decide_eq_true negative))
    · positivity)
  exact constructed.withSpecification (fun _ _ => True) (integerShiftLeft width amount).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (if SignedEncoding.negative (arguments ()).val
        then -(((arguments ()).val.natAbs * 2 ^ MvPolynomial.eval sizes amount : ℕ) : ℤ)
        else (((arguments ()).val.natAbs * 2 ^ MvPolynomial.eval sizes amount : ℕ) : ℤ)) =
          (arguments ()).val * (2 ^ MvPolynomial.eval sizes amount : ℕ)
      simp only [Nat.cast_mul, ← neg_mul]
      split <;> rename_i sign
      · have restored := SignedEncoding.restore (arguments ()).val
        rw [ite_eq_left sign] at restored
        rw [restored]
      · have restored := SignedEncoding.restore (arguments ()).val
        rw [ite_eq_right sign] at restored
        rw [restored])

/-- Right shift uses the ordinary floor quotient, including negative inputs. -/
noncomputable def integerShiftRight (width amount : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryIntegers width) (binaryIntegers width) (fun sizes value =>
    ⟨value.val / (2 ^ MvPolynomial.eval sizes amount : ℕ),
      (Int.natAbs_ediv_le_natAbs _ _).trans_lt value.property⟩)

theorem integerShiftRight_correct (width amount : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerShiftRight width amount).Arguments sizes) :
    ((integerShiftRight width amount).compute sizes ⟨arguments, trivial⟩).val =
      (arguments ()).val >>> MvPolynomial.eval sizes amount := by
  simpa only [integerShiftRight, encodingMap, unaryMap, Nat.cast_pow, Nat.cast_ofNat] using
    (Int.shiftRight_eq_div_pow (arguments ()).val (MvPolynomial.eval sizes amount)).symm

private theorem integerOne_realizable :
    (Computation.mk (Parameter := Parameter) (InputName := Empty) Empty.elim (binaryIntegers 1)
      (fun _ _ => True) (fun _ _ => ⟨1, by simp⟩)).Realizable := by
  exact (Realizable.Internal.integerBooleanOperation_realizable (Parameter := Parameter) (Argument := Empty)
    (fun _ => ⟨1, by decide⟩)).withArguments Empty.elim (Function.Embedding.refl Empty)
      (by intro impossible; exact impossible.elim)

theorem integerShiftRight_realizable (width amount : MvPolynomial Parameter ℕ) :
    (integerShiftRight width amount).Realizable := by
  let inputs := (integerShiftRight width amount).inputDomains
  let capacity := width + (1 + amount)
  have one := integerOne_realizable (Parameter := Parameter)
  have divisor := (one.followedBy (Realizable.Internal.integerWiden_realizable 1 width) rfl
    (by intros; trivial)).followedBy (integerShiftLeft_realizable (1 + width) amount) rfl
      (by intros; trivial)
  have divisorReady := divisor.withArguments inputs
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  have numeratorReady := Realizable.Internal.integerWiden_realizable width (1 + amount)
  have quotient := (integerQuotient_realizable capacity).onResults inputs (fun _ _ => True)
    (fun name sizes arguments => if name then
      ⟨(2 ^ MvPolynomial.eval sizes amount : ℕ), by
        simp only [Int.natAbs_natCast]
        apply Nat.pow_lt_pow_right (by decide)
        dsimp [capacity]
        simp only [map_add, map_one]
        omega⟩
      else ⟨(arguments.val ()).val, by
        exact (arguments.val ()).property.trans_le (pow_le_pow_right₀ (by decide)
          (by dsimp [capacity]; simp only [map_add]; omega))⟩)
    (by intro sizes arguments; change (2 ^ MvPolynomial.eval sizes amount : ℕ) ≠ (0 : ℤ); positivity)
    (by
      intro name
      cases name
      · exact numeratorReady
      · have sameWidth : (1 + width) + amount = capacity := by dsimp [capacity]; ring
        have transported := divisorReady.reinterpretOutput (binaryIntegers capacity)
          (fun sizes value => ⟨value.val, by simpa only [sameWidth] using value.property⟩)
          (by intro sizes; change (binaryIntegers capacity).width sizes =
              (binaryIntegers ((1 + width) + amount)).width sizes
              rw [sameWidth])
          (fun sizes value => binaryIntegers_encode_congr _ _ sameWidth.symm sizes _ _ rfl)
        exact transported.withSpecification (fun _ _ => True) _ (by intros; trivial) (by
          intros
          apply Subtype.ext
          exact one_mul _))
  have narrowed := quotient.followedBy (Realizable.Internal.integerNarrow_realizable width (1 + amount)) rfl (by
    intro sizes arguments valid
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments ()).property)
  exact narrowed.withSpecification (fun _ _ => True) (integerShiftRight width amount).compute
    (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
