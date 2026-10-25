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

import Polytime2.Arithmetic.SignedAddition
import Polytime2.Arithmetic.SignedMultiplication
import Polytime2.Arithmetic.SignedGcd
import Polytime2.Arithmetic.SignedDivision
import Polytime2.Arithmetic.SignedBitLength
import Polytime2.Arithmetic.SignedExtendedGcd
import Polytime2.Arithmetic.NormalizedBezout
import Polytime2.TM0.Computation

/-! # Signed codec boundaries and certified sign/magnitude extraction -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.Integers

open Polytime2.Computation Polytime2.EncodedDomain

example : (integerLess (MvPolynomial.X ())).Realizable := integerLess_realizable _
example : (integerEqual (MvPolynomial.X ())).Realizable := integerEqual_realizable _
example : (integerLessEqual (MvPolynomial.X ())).Realizable := integerLessEqual_realizable _
example : (integerAdd (MvPolynomial.X ())).Realizable := integerAdd_realizable _
example : (integerSubtract (MvPolynomial.X ())).Realizable := integerSubtract_realizable _
example : (integerLess (MvPolynomial.X ())).TM0Realizable := (integerLess_realizable _).tm0
example : (integerEqual (MvPolynomial.X ())).TM0Realizable := (integerEqual_realizable _).tm0
example : (integerLessEqual (MvPolynomial.X ())).TM0Realizable := (integerLessEqual_realizable _).tm0
example : (integerAdd (MvPolynomial.X ())).TM0Realizable := (integerAdd_realizable _).tm0
example : (integerSubtract (MvPolynomial.X ())).TM0Realizable := (integerSubtract_realizable _).tm0

example : (integerDivision (MvPolynomial.X ())).Realizable := integerDivision_realizable _
example : (integerQuotient (MvPolynomial.X ())).Realizable := integerQuotient_realizable _
example : (integerRemainder (MvPolynomial.X ())).Realizable := integerRemainder_realizable _
example : (integerDivision (MvPolynomial.X ())).TM0Realizable := (integerDivision_realizable _).tm0
example : (integerQuotient (MvPolynomial.X ())).TM0Realizable := (integerQuotient_realizable _).tm0
example : (integerRemainder (MvPolynomial.X ())).TM0Realizable := (integerRemainder_realizable _).tm0

example : (integerMultiply (MvPolynomial.X ())).Realizable := integerMultiply_realizable _
example : (integerGcd (MvPolynomial.X ())).Realizable := integerGcd_realizable _
example : (integerMultiply (MvPolynomial.X ())).TM0Realizable := (integerMultiply_realizable _).tm0
example : (integerGcd (MvPolynomial.X ())).TM0Realizable := (integerGcd_realizable _).tm0

example : (integerIsZero (MvPolynomial.X ())).Realizable := integerIsZero_realizable _
example : (integerNegate (MvPolynomial.X ())).Realizable := integerNegate_realizable _
example : (integerIsZero (MvPolynomial.X ())).TM0Realizable := (integerIsZero_realizable _).tm0
example : (integerNegate (MvPolynomial.X ())).TM0Realizable := (integerNegate_realizable _).tm0

example : (integerNegative (MvPolynomial.X ())).Realizable := integerNegative_realizable _
example : (integerMagnitude (MvPolynomial.X ())).Realizable := integerMagnitude_realizable _
example : (integerNegative (MvPolynomial.X ())).TM0Realizable := (integerNegative_realizable _).tm0
example : (integerMagnitude (MvPolynomial.X ())).TM0Realizable := (integerMagnitude_realizable _).tm0

example : (integerNegative (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨-15, by norm_num⟩)), trivial⟩ = true := rfl
example : (integerNegative (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨15, by norm_num⟩)), trivial⟩ = false := rfl
example : (integerNegative (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩ = false := rfl

example : ((integerMagnitude (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨-15, by norm_num⟩)), trivial⟩).val = 15 := rfl

example : ((binaryIntegers (MvPolynomial.X ())).encode (fun _ => 4)
    (by exact ⟨3, by norm_num⟩)).toNat = 6 := by
  simp only [binaryIntegers, reindex, restrict]
  simp [booleans, fixed, SignedEncoding.negative, SignedEncoding.representationEquiv,
    binaryNaturalsOfWidth, boundedIndexOfWidth, ofCodec]
  decide
example : ((binaryIntegers (MvPolynomial.X ())).encode (fun _ => 4)
    (by exact ⟨-3, by norm_num⟩)).toNat = 7 := by
  simp only [binaryIntegers, reindex, restrict]
  simp [booleans, fixed, SignedEncoding.negative, SignedEncoding.representationEquiv,
    binaryNaturalsOfWidth, boundedIndexOfWidth, ofCodec]
  decide

-- The decoder rejects the negative-zero word, rather than normalizing it.
example : (binaryIntegers (MvPolynomial.X ())).decode (fun _ : Unit => 4)
    ((booleans.prod (binaryNaturalsOfWidth (MvPolynomial.X ()))).encode (fun _ => 4)
      (true, ⟨0, by simp⟩)) = none := by
  classical
  simp only [binaryIntegers, reindex]
  have rejected := restrict_decode_rejected
    (booleans.prod (binaryNaturalsOfWidth (MvPolynomial.X ())))
    (fun _ parts => parts.1 = true → parts.2.val ≠ 0)
    (fun _ : Unit => 4) (true, ⟨0, by simp⟩) (by simp)
  exact congrArg (Option.map (SignedEncoding.representationEquiv
    (MvPolynomial.eval (fun _ : Unit => 4) (MvPolynomial.X ()))).symm) rejected

example (value : (binaryIntegers (MvPolynomial.X ())).Carrier (fun _ => 0)) : value.val = 0 := by
  have bound : value.val.natAbs < 1 := by simpa using value.property
  have zero : value.val.natAbs = 0 := by omega
  exact Int.natAbs_eq_zero.mp zero

example : (integerIsZero (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩ = true := rfl
example : (integerIsZero (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨fun _ => (by exact ⟨-15, by norm_num⟩), trivial⟩ = false := rfl
example : ((integerNegate (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩).val = 0 := rfl

example : (integerLess (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨-3, by norm_num⟩)), trivial⟩ = true := rfl
example : (integerLess (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-3, by norm_num⟩) | true => (by exact ⟨-15, by norm_num⟩)), trivial⟩ = false := rfl
example : (integerLess (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-3, by norm_num⟩) | true => (by exact ⟨0, by norm_num⟩)), trivial⟩ = true := rfl
example : (integerEqual (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨fun _ => (by exact ⟨-15, by norm_num⟩), trivial⟩ = true := rfl
example : (integerLessEqual (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩ = true := rfl
example : ((integerAdd (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨15, by norm_num⟩)), trivial⟩).val = 0 := rfl
example : ((integerAdd (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩).val = 0 := rfl

-- Results grow to derived widths instead of wrapping or requiring spare bits.
example : ((integerAdd (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨fun _ => (by exact ⟨-15, by norm_num⟩), trivial⟩).val = -30 := rfl

example : ((integerSubtract (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨15, by norm_num⟩) | true => (by exact ⟨-15, by norm_num⟩)),
      trivial⟩).val = 30 := rfl

example : ((integerMultiply (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨fun _ => (by exact ⟨-15, by norm_num⟩), trivial⟩).val = 225 := rfl

example : ((integerNegate (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨fun _ => (by exact ⟨-15, by norm_num⟩), trivial⟩).val = 15 := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-13, by norm_num⟩) | true => (by exact ⟨5, by norm_num⟩)),
        by change (5 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (-3, 2) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-13, by norm_num⟩) | true => (by exact ⟨-5, by norm_num⟩)),
        by change (-5 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (3, 2) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨13, by norm_num⟩) | true => (by exact ⟨-5, by norm_num⟩)),
        by change (-5 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (-2, 3) := rfl

example : ((integerMultiply (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨15, by norm_num⟩)), trivial⟩).val = -225 := rfl
example : ((integerMultiply (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨0, by norm_num⟩)), trivial⟩).val = 0 := rfl
example : ((integerMultiply (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩).val = 0 := rfl
example : ((integerGcd (MvPolynomial.X ())).compute (fun _ => 5)
    ⟨(fun | false => (by exact ⟨-12, by norm_num⟩) | true => (by exact ⟨18, by norm_num⟩)), trivial⟩).val = 6 := rfl
example : ((integerGcd (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨0, by norm_num⟩) | true => (by exact ⟨-15, by norm_num⟩)), trivial⟩).val = 15 := rfl
example : ((integerGcd (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨fun _ => (by exact ⟨0, by norm_num⟩), trivial⟩).val = 0 := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨-1, by norm_num⟩)),
        by change (-1 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (15, 0) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨15, by norm_num⟩) | true => (by exact ⟨-1, by norm_num⟩)),
        by change (-1 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (-15, 0) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-1, by norm_num⟩) | true => (by exact ⟨15, by norm_num⟩)),
        by change (15 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (-1, 14) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-1, by norm_num⟩) | true => (by exact ⟨-15, by norm_num⟩)),
        by change (-15 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (1, 14) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨-15, by norm_num⟩) | true => (by exact ⟨2, by norm_num⟩)),
        by change (2 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (-8, 1) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨0, by norm_num⟩) | true => (by exact ⟨-15, by norm_num⟩)),
        by change (-15 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (0, 0) := rfl

example :
    let answer := (integerDivision (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun | false => (by exact ⟨15, by norm_num⟩) | true => (by exact ⟨15, by norm_num⟩)),
        by change (15 : ℤ) ≠ 0; decide⟩
    (answer.1.val, answer.2.val) = (1, 0) := rfl

example : ((integerRemainder (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun | false => (by exact ⟨-13, by norm_num⟩) | true => (by exact ⟨-5, by norm_num⟩)),
      by change (-5 : ℤ) ≠ 0; decide⟩).val = 2 := rfl

example (arguments : (integerDivision (MvPolynomial.X ())).Arguments (fun _ => 0)) :
    ¬ (integerDivision (MvPolynomial.X ())).precondition (fun _ => 0) arguments := by
  intro nonzero
  have bound : (arguments true).val.natAbs < 1 := by simpa using (arguments true).property
  exact nonzero (Int.natAbs_eq_zero.mp (by omega))

-- Euclidean correction of the unsigned magnitude division.
example : (Realizable.Internal.SignedDivision.quotientMagnitude (-13) 5,
    Realizable.Internal.SignedDivision.remainderMagnitude (-13) 5) = (3, 2) := rfl
example : (Realizable.Internal.SignedDivision.quotientMagnitude (-13) (-5),
    Realizable.Internal.SignedDivision.remainderMagnitude (-13) (-5)) = (3, 2) := rfl
example : (Realizable.Internal.SignedDivision.quotientMagnitude (-10) 5,
    Realizable.Internal.SignedDivision.remainderMagnitude (-10) 5) = (2, 0) := rfl
example : (Realizable.Internal.SignedDivision.quotientMagnitude 0 (-5),
    Realizable.Internal.SignedDivision.remainderMagnitude 0 (-5)) = (0, 0) := rfl

example : (integerShiftLeft (MvPolynomial.X false) (MvPolynomial.X true)).Realizable :=
  integerShiftLeft_realizable _ _
example : (integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).Realizable :=
  integerShiftRight_realizable _ _
example : (integerShiftLeft (MvPolynomial.X false) (MvPolynomial.X true)).TM0Realizable :=
  (integerShiftLeft_realizable _ _).tm0
example : (integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).TM0Realizable :=
  (integerShiftRight_realizable _ _).tm0

example : ((integerShiftLeft (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 3 else 4)
    ⟨(fun _ => (by exact ⟨-15, by norm_num⟩)), trivial⟩).val = -120 := by
  erw [integerShiftLeft_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftLeft (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 0 else 4)
    ⟨(fun _ => (by exact ⟨15, by norm_num⟩)), trivial⟩).val = 15 := by
  erw [integerShiftLeft_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftLeft (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 7 else 0)
    ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩).val = 0 := by
  erw [integerShiftLeft_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 1 else 4)
    ⟨(fun _ => (by exact ⟨-3, by norm_num⟩)), trivial⟩).val = -2 := by
  erw [integerShiftRight_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 7 else 4)
    ⟨(fun _ => (by exact ⟨-1, by norm_num⟩)), trivial⟩).val = -1 := by
  erw [integerShiftRight_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 7 else 4)
    ⟨(fun _ => (by exact ⟨15, by norm_num⟩)), trivial⟩).val = 0 := by
  erw [integerShiftRight_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 0 else 4)
    ⟨(fun _ => (by exact ⟨-15, by norm_num⟩)), trivial⟩).val = -15 := by
  erw [integerShiftRight_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]
example : ((integerShiftRight (MvPolynomial.X false) (MvPolynomial.X true)).compute
    (fun flag => if flag then 7 else 0)
    ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩).val = 0 := by
  erw [integerShiftRight_correct]
  norm_num [Int.shiftLeft_eq', Int.shiftRight_eq_div_pow]

example : (integerBitLength (MvPolynomial.X ())).Realizable := integerBitLength_realizable _
example : (integerBitLength (MvPolynomial.X ())).TM0Realizable := (integerBitLength_realizable _).tm0

example : ((integerBitLength (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨-15, by norm_num⟩)), trivial⟩).val = 4 := rfl
example : ((integerBitLength (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨8, by norm_num⟩)), trivial⟩).val = 4 := rfl
example : ((integerBitLength (MvPolynomial.X ())).compute (fun _ => 4)
    ⟨(fun _ => (by exact ⟨7, by norm_num⟩)), trivial⟩).val = 3 := rfl
example : ((integerBitLength (MvPolynomial.X ())).compute (fun _ => 0)
    ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩).val = 0 := rfl

example : Polytime2.ExtendedGcd.result (-30) 21 = (3, 2, 3) := by
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.ExtendedGcd.advance, Polytime2.Gcd.condition]
  decide
example : Polytime2.ExtendedGcd.result 0 0 = (0, 0, 0) := by
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.Gcd.condition]
example : Polytime2.ExtendedGcd.coefficientWidth 0 = 2 := rfl

example : (integerExtendedGcd (MvPolynomial.X ())).Realizable := integerExtendedGcd_realizable _
example : (integerExtendedGcd (MvPolynomial.X ())).TM0Realizable := (integerExtendedGcd_realizable _).tm0

example :
    let result := (integerExtendedGcd (MvPolynomial.X ())).compute (fun _ => 5)
      ⟨(fun flag => if flag then (by exact ⟨21, by norm_num⟩) else (by exact ⟨-30, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (3, 2, 3) := by
  dsimp only
  rw [integerExtendedGcd_value]
  change (((Polytime2.ExtendedGcd.result (-30) (21)).1 : ℤ),
    (Polytime2.ExtendedGcd.result (-30) (21)).2.1,
    (Polytime2.ExtendedGcd.result (-30) (21)).2.2) = (3, 2, 3)
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.ExtendedGcd.advance, Polytime2.Gcd.condition]
  decide
example :
    let result := (integerExtendedGcd (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun flag => if flag then (by exact ⟨8, by norm_num⟩) else (by exact ⟨13, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (1, -3, 5) := by
  dsimp only
  rw [integerExtendedGcd_value]
  change (((Polytime2.ExtendedGcd.result (13) (8)).1 : ℤ),
    (Polytime2.ExtendedGcd.result (13) (8)).2.1,
    (Polytime2.ExtendedGcd.result (13) (8)).2.2) = (1, -3, 5)
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.ExtendedGcd.advance, Polytime2.Gcd.condition]
  decide
example :
    let result := (integerExtendedGcd (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun flag => if flag then (by exact ⟨0, by norm_num⟩) else (by exact ⟨-15, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (15, -1, 0) := by
  dsimp only
  rw [integerExtendedGcd_value]
  change (((Polytime2.ExtendedGcd.result (-15) (0)).1 : ℤ),
    (Polytime2.ExtendedGcd.result (-15) (0)).2.1,
    (Polytime2.ExtendedGcd.result (-15) (0)).2.2) = (15, -1, 0)
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.Gcd.condition]
example :
    let result := (integerExtendedGcd (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun flag => if flag then (by exact ⟨-15, by norm_num⟩) else (by exact ⟨0, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (15, 0, -1) := by
  dsimp only
  rw [integerExtendedGcd_value]
  change (((Polytime2.ExtendedGcd.result (0) (-15)).1 : ℤ),
    (Polytime2.ExtendedGcd.result (0) (-15)).2.1,
    (Polytime2.ExtendedGcd.result (0) (-15)).2.2) = (15, 0, -1)
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.ExtendedGcd.advance, Polytime2.Gcd.condition]
example :
    let result := (integerExtendedGcd (MvPolynomial.X ())).compute (fun _ => 0)
      ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (0, 0, 0) := by
  dsimp only
  rw [integerExtendedGcd_value]
  change (((Polytime2.ExtendedGcd.result (0) (0)).1 : ℤ),
    (Polytime2.ExtendedGcd.result (0) (0)).2.1,
    (Polytime2.ExtendedGcd.result (0) (0)).2.2) = (0, 0, 0)
  norm_num [Polytime2.ExtendedGcd.result, Polytime2.ExtendedGcd.initial,
    Polytime2.ExtendedGcd.run, Polytime2.Gcd.condition]


example : (integerNormalizedExtendedGcd (MvPolynomial.X ())).TM0Realizable :=
  (integerNormalizedExtendedGcd_realizable _).tm0

example :
    let result := (integerNormalizedExtendedGcd (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun flag => if flag then (by exact ⟨8, by norm_num⟩) else (by exact ⟨13, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (1, 5, -8) := by
  dsimp only
  rw [integerNormalizedExtendedGcd_value]
  decide +kernel

example :
    let result := (integerNormalizedExtendedGcd (MvPolynomial.X ())).compute (fun _ => 5)
      ⟨(fun flag => if flag then (by exact ⟨-18, by norm_num⟩) else (by exact ⟨30, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (6, 2, 3) := by
  dsimp only
  rw [integerNormalizedExtendedGcd_value]
  decide +kernel

example :
    let result := (integerNormalizedExtendedGcd (MvPolynomial.X ())).compute (fun _ => 0)
      ⟨(fun _ => (by exact ⟨0, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (0, 1, 0) := by
  dsimp only
  rw [integerNormalizedExtendedGcd_value]
  decide +kernel

example :
    let result := (integerNormalizedExtendedGcd (MvPolynomial.X ())).compute (fun _ => 4)
      ⟨(fun flag => if flag then (by exact ⟨0, by norm_num⟩) else (by exact ⟨-15, by norm_num⟩)), trivial⟩
    (result.1.val, result.2.1.val, result.2.2.val) = (15, -1, 0) := by
  dsimp only
  rw [integerNormalizedExtendedGcd_value]
  decide +kernel

end Polytime2.Examples.Integers
