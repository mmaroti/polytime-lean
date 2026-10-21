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

import Polytime2.Arithmetic.SignedShifts
import Polytime2.Computation.While

/-! # Magnitude bit length of a signed integer

The input is an ordinary signed integer at magnitude width `w`. The result is
`Nat.size z.natAbs`, an ordinary natural in `Fin (w+1)`. Zero has bit length
zero. A loop halves a nonnegative magnitude and increments a bounded counter;
it executes at most `w` iterations, independently of numeric magnitude.
-/

namespace Polytime2.Computation.Realizable.Internal.IntegerBitLength

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def state (width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (binaryIntegers width).prod (binaryNaturalsOfWidth (width + 1))

def admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : Prop :=
  0 ≤ value.1.val ∧ value.2.val + Nat.size value.1.val.natAbs ≤ MvPolynomial.eval sizes width

def condition (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (state width).Carrier sizes) : Bool := decide (value.1.val ≠ 0)

noncomputable def advance (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes //
      admissible width sizes value ∧ condition width sizes value = true}) : (state width).Carrier sizes :=
  (⟨value.val.1.val / 2, (Int.natAbs_ediv_le_natAbs _ _).trans_lt value.val.1.property⟩,
    ⟨(value.val.2.val + 1) % 2 ^ MvPolynomial.eval sizes (width + 1), Nat.mod_lt _ (by positivity)⟩)

private theorem next_count (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes //
      admissible width sizes value ∧ condition width sizes value = true}) :
    (advance width sizes value).2.val = value.val.2.val + 1 := by
  have nonzero : value.val.1.val.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (of_decide_eq_true value.property.2)
  have positive := Nat.size_pos.mpr (Nat.pos_of_ne_zero nonzero)
  have capacity := Nat.lt_two_pow_self (n := MvPolynomial.eval sizes width + 1)
  change (value.val.2.val + 1) % 2 ^ MvPolynomial.eval sizes (width + 1) = _
  apply Nat.mod_eq_of_lt
  simp only [map_add, map_one]
  have bound := value.property.1.2
  exact (show value.val.2.val + 1 ≤ MvPolynomial.eval sizes width + 1 by omega).trans_lt capacity

private theorem next_size (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes //
      admissible width sizes value ∧ condition width sizes value = true}) :
    Nat.size (advance width sizes value).1.val.natAbs + 1 = Nat.size value.val.1.val.natAbs := by
  have quotient : (value.val.1.val / 2).natAbs = value.val.1.val.natAbs / 2 := by
    simpa using Int.natAbs_ediv_of_nonneg (b := 2) value.property.1.1
  change Nat.size (value.val.1.val / 2).natAbs + 1 = _
  rw [quotient]
  exact Gcd.size_half _ (Int.natAbs_ne_zero.mpr (of_decide_eq_true value.property.2))

theorem preserves (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes //
      admissible width sizes value ∧ condition width sizes value = true}) :
    admissible width sizes (advance width sizes value) := by
  refine ⟨Int.ediv_nonneg value.property.1.1 (by norm_num), ?_⟩
  have count := next_count width sizes value
  have length := next_size width sizes value
  have bounded := value.property.1.2
  change (advance width sizes value).2.val + Nat.size (advance width sizes value).1.val.natAbs ≤ _
  omega

noncomputable def answer (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : {value : (state width).Carrier sizes // admissible width sizes value}) : (state width).Carrier sizes :=
  (⟨0, by positivity⟩, ⟨value.val.2.val + Nat.size value.val.1.val.natAbs, by
    have capacity := Nat.lt_two_pow_self (n := MvPolynomial.eval sizes width + 1)
    change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
    simp only [map_add, map_one]
    exact value.property.2.trans_lt ((Nat.lt_succ_self _).trans capacity)⟩)

theorem loop_realizable (width : MvPolynomial Parameter ℕ) :
    (unaryMap (state width) (state width) (admissible width) (answer width)).Realizable := by
  refine Realizable.whileLoop (state width) (admissible width) (condition width) (advance width) (answer width)
    (fun _ value => Nat.size value.1.val.natAbs) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have guard := (pairProjection_realizable (binaryIntegers width) (binaryNaturalsOfWidth (width + 1)) false).followedBy
      (integerIsZero_realizable width) rfl (by intros; trivial)
    have inverted := guard.followedBy
      (booleanOperation_realizable (Parameter := Parameter) (Argument := Unit) (fun flags => !flags ()))
      rfl (by intros; trivial)
    exact inverted.withSpecification (fun sizes arguments => admissible width sizes (arguments ())) _ (by intros; trivial) (by
      intro sizes arguments valid
      change (!decide ((arguments ()).1.val = 0)) = decide ((arguments ()).1.val ≠ 0)
      simp)
  · let allowed := fun sizes (arguments : Unit → (state width).Carrier sizes) =>
      admissible width sizes (arguments ()) ∧ condition width sizes (arguments ()) = true
    have current := ((pairProjection_realizable (binaryIntegers width) (binaryNaturalsOfWidth (width + 1)) false).followedBy
      (integerShiftRight_realizable width 1) rfl (by intros; trivial)).withPrecondition allowed (by intros; trivial)
    have count := ((pairProjection_realizable (binaryIntegers width) (binaryNaturalsOfWidth (width + 1)) true).followedBy
      (naturalIncrement_realizable (width + 1)) rfl (by intros; trivial)).withPrecondition allowed (by intros; trivial)
    have paired := Realizable.pairOutputs (fun _ : Unit => state width) (binaryIntegers width)
      (binaryNaturalsOfWidth (width + 1)) allowed _ _ current count
    exact paired.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments valid
      apply Prod.ext
      · apply Subtype.ext
        change (arguments ()).1.val / (2 ^ MvPolynomial.eval sizes 1 : ℕ) = (arguments ()).1.val / 2
        simp
      · rfl)
  · exact preserves width
  · intro sizes value
    have smaller := next_size width sizes value
    omega
  · intro sizes value
    apply Prod.ext
    · rfl
    · apply Fin.ext
      have count := next_count width sizes value
      have length := next_size width sizes value
      change (advance width sizes value).2.val + Nat.size (advance width sizes value).1.val.natAbs =
        value.val.2.val + Nat.size value.val.1.val.natAbs
      omega
  · intro sizes value stopped
    have zero : value.val.1.val = 0 := by simpa [condition] using stopped
    apply Prod.ext
    · exact Subtype.ext zero.symm
    · apply Fin.ext
      change value.val.2.val + Nat.size value.val.1.val.natAbs = value.val.2.val
      simp [zero]
  · refine ⟨width, ?_⟩
    intro sizes value valid
    exact Nat.size_le.mpr value.1.property

end Polytime2.Computation.Realizable.Internal.IntegerBitLength

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Magnitude bit length is an ordinary bounded natural, including zero. -/
noncomputable def integerBitLength (width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryIntegers width) (boundedIndex (width + 1)) (fun sizes value =>
    ⟨Nat.size value.val.natAbs, by
      change _ < MvPolynomial.eval sizes (width + 1)
      simp only [map_add, map_one]
      exact Nat.lt_succ_of_le (Nat.size_le.mpr value.property)⟩)

theorem integerBitLength_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerBitLength width).Arguments sizes) :
    ((integerBitLength width).compute sizes ⟨arguments, trivial⟩).val = Nat.size (arguments ()).val.natAbs := rfl

theorem integerBitLength_realizable (width : MvPolynomial Parameter ℕ) :
    (integerBitLength width).Realizable := by
  let inputs := (integerBitLength width).inputDomains
  have magnitude := (integerMagnitude_realizable width).followedBy
    (Realizable.Internal.integerOfMagnitude_realizable width) rfl (by intros; trivial)
  have zeros := (zeroBits_realizable (width + 1)).withEncodedOutput (binaryNaturalsOfWidth (width + 1))
    (fun _ _ => ⟨0, by positivity⟩) (by intros; rfl) (by intros; rfl)
  have count := zeros.withArguments inputs
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  have initial := Realizable.pairOutputs inputs (binaryIntegers width) (binaryNaturalsOfWidth (width + 1))
    (fun _ _ => True) _ _ magnitude count
  have loop := initial.followedBy (Realizable.Internal.IntegerBitLength.loop_realizable width) rfl (by
    intro sizes arguments valid
    change 0 ≤ ((arguments ()).val.natAbs : ℤ) ∧
      0 + Nat.size ((arguments ()).val.natAbs : ℤ).natAbs ≤ MvPolynomial.eval sizes width
    exact ⟨Int.natCast_nonneg _, by simpa only [Int.natAbs_natCast, Nat.zero_add] using Nat.size_le.mpr (arguments ()).property⟩)
  have projected := loop.followedBy
    (pairProjection_realizable (binaryIntegers width) (binaryNaturalsOfWidth (width + 1)) true) rfl
    (by intros; trivial)
  exact projected.withEncodedOutput (boundedIndex (width + 1)) (integerBitLength width).compute
    (by intros; rfl) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      simp [integerBitLength, encodingMap, unaryMap, followedBy, zeroBits,
        pairProjection, Realizable.Internal.IntegerBitLength.answer,
        integerMagnitude, Realizable.Internal.integerOfMagnitude, boundedIndex,
        binaryNaturalsOfWidth, boundedIndexOfWidth])

end Polytime2.Computation
