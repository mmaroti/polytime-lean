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

import Polytime2.Encoding.Binary
import Polytime2.Encoding.EncodedArray
import Mathlib.Data.Nat.Bitwise

/-! # Canonical encodings of bounded binary natural numbers

These lemmas connect the little-endian mathematical arithmetic used by the
controllers to the unique bit-vector encoding of bounded natural domains.
-/

namespace Polytime2.Binary

/-- Encoding the natural value of a fixed-width binary word recovers its bits. -/
theorem bits_value {width : ℕ} (bits : List Bool) (sameLength : bits.length = width) :
    List.ofFn (fun index : Fin width =>
      (BitVec.ofNat width (value bits)).getLsbD index.val) = bits := by
  subst width
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis =>
    have decomposition : value (bit :: bits) = Nat.bit bit (value bits) := by
      cases bit <;> simp [value, Nat.bit_val, Nat.add_comm]
    rw [List.ofFn_succ]
    congr 1
    · simp only [BitVec.getLsbD_ofNat, decomposition, List.length_cons, Fin.val_zero,
        Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.testBit_bit_zero]
    · have tail : (fun index : Fin bits.length =>
          (BitVec.ofNat (bit :: bits).length (value (bit :: bits))).getLsbD index.succ.val) =
          fun index : Fin bits.length => (BitVec.ofNat bits.length (value bits)).getLsbD index.val := by
        funext index
        simp only [BitVec.getLsbD_ofNat, decomposition, List.length_cons, Fin.val_succ,
          Nat.add_lt_add_iff_right, index.isLt, decide_true, Bool.true_and, Nat.testBit_bit_succ]
      rw [tail]
      exact hypothesis

/-- The numeric value of an encoded bit vector is its bounded natural value. -/
theorem value_bits {width : ℕ} (bits : BitVec width) :
    value (List.ofFn (fun index : Fin width => bits.getLsbD index.val)) = bits.toNat := by
  let digits := List.ofFn (fun index : Fin width => bits.getLsbD index.val)
  have equality : List.ofFn (fun index : Fin width =>
      (BitVec.ofNat width (value digits)).getLsbD index.val) = digits := by
    exact bits_value digits (by simp [digits])
  have functions := List.ofFn_injective equality
  have vectors : BitVec.ofNat width (value digits) = bits := by
    apply BitVec.eq_of_getLsbD_eq
    intro index bounded
    exact congrFun functions ⟨index, bounded⟩
  have bounded : value digits < 2 ^ width := by
    simpa [digits] using value_lt_pow_length digits
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using congrArg BitVec.toNat vectors

def prefixValue (bits : List Bool) (initial : ℕ) : ℕ :=
  bits.foldl (fun previous bit => bit.toNat + 2 * previous) initial

@[simp] theorem prefixValue_reverse (bits : List Bool) (initial : ℕ) :
    prefixValue bits.reverse initial = value bits + 2 ^ bits.length * initial := by
  induction bits with
  | nil => simp [prefixValue, value]
  | cons bit bits hypothesis =>
    simp only [prefixValue, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil] at hypothesis ⊢
    rw [hypothesis]
    simp only [value, List.length_cons, pow_succ]
    ring

theorem prefixValue_mod (bits : List Bool) (initial divisor : ℕ) :
    prefixValue bits (initial % divisor) % divisor = prefixValue bits initial % divisor := by
  induction bits generalizing initial with
  | nil => simp [prefixValue]
  | cons bit bits hypothesis =>
    have next : (bit.toNat + 2 * (initial % divisor)) % divisor =
        (bit.toNat + 2 * initial) % divisor := by simp [Nat.add_mod, Nat.mul_mod]
    change prefixValue bits (bit.toNat + 2 * (initial % divisor)) % divisor =
      prefixValue bits (bit.toNat + 2 * initial) % divisor
    rw [← hypothesis (bit.toNat + 2 * (initial % divisor)), next, hypothesis]

/-- A binary word is nonzero exactly when one of its digits is set. -/
theorem any_iff_positive (bits : List Bool) : bits.any id = true ↔ 0 < value bits := by
  induction bits with
  | nil => simp [value]
  | cons bit bits hypothesis => cases bit <;> simp [value, hypothesis]

end Polytime2.Binary

namespace Polytime2.EncodedDomain

-- parameterLevel: names of the runtime size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- A size parameter fixes digit capacity, while numeric magnitude may be
exponential in that capacity. Zero digits still encode the natural number zero. -/
noncomputable def binaryNaturals (parameter : Parameter) : EncodedDomain Parameter :=
  ofCodec (fun assignment => Fin (2 ^ assignment parameter)) (MvPolynomial.X parameter)
    (fun assignment => assignment parameter) (by intro assignment; simp)
    (fun _ => BitVec.ofFin) (fun _ bits => some bits.toFin)
    (by intros; rfl) (by intro assignment bits value hypothesis; cases hypothesis; rfl)

@[simp] theorem binaryNaturals_width (parameter : Parameter) (assignment : Parameter → ℕ) :
    (binaryNaturals parameter).width assignment = assignment parameter := by
  simp [binaryNaturals, ofCodec]

/-- A bounded coordinate with a chosen exact polynomial binary width. -/
noncomputable def boundedIndexOfWidth (length : (Parameter → ℕ) → ℕ) (width : MvPolynomial Parameter ℕ)
    (fits : ∀ sizes, length sizes ≤ 2 ^ MvPolynomial.eval sizes width) :
    EncodedDomain Parameter where
  Carrier sizes := Fin (length sizes)
  widthPolynomial := width
  encode sizes index := BitVec.ofNatLT index.val (index.isLt.trans_le (fits sizes))
  decode sizes bits := if within : bits.toNat < length sizes then some ⟨bits.toNat, within⟩ else none
  decode_encode sizes index := by simp [index.isLt]
  encode_decode sizes bits index accepted := by
    split at accepted
    · cases Option.some.inj accepted
      exact BitVec.eq_of_toNat_eq (by simp)
    · simp at accepted

@[simp] theorem boundedIndexOfWidth_value (length : (Parameter → ℕ) → ℕ)
    (width : MvPolynomial Parameter ℕ) (fits : ∀ sizes, length sizes ≤ 2 ^ MvPolynomial.eval sizes width)
    (sizes : Parameter → ℕ) (index : (boundedIndexOfWidth length width fits).Carrier sizes) :
    Binary.value (ArrayEncoding.bits ((boundedIndexOfWidth length width fits).encode sizes index)) = index.val :=
  (Binary.value_bits _).trans (by simp only [boundedIndexOfWidth, BitVec.toNat_ofNatLT])

/-- Array coordinates use their mathematical bound as the exact binary width.
The empty bound has no coordinates; decoding rejects out-of-range words. -/
noncomputable def boundedIndex (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  boundedIndexOfWidth (fun sizes => MvPolynomial.eval sizes length) length (fun _ => (Nat.lt_two_pow_self).le)

@[simp] theorem boundedIndex_value (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : (boundedIndex length).Carrier sizes) :
    Binary.value (ArrayEncoding.bits ((boundedIndex length).encode sizes index)) = index.val := by
  exact (Binary.value_bits _).trans (by simp [boundedIndex, boundedIndexOfWidth])

/-- Row and column coordinates correspond to their row-major array coordinate. -/
noncomputable def matrixCoordinateEquiv (rows columns : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (Fin (MvPolynomial.eval sizes rows) × Fin (MvPolynomial.eval sizes columns)) ≃
      Fin (MvPolynomial.eval sizes (rows * columns)) :=
  finProdFinEquiv.trans (finCongr (by simp only [MvPolynomial.eval_mul]))

/-- A mathematical matrix coordinate is a row and column pair. Its codec uses
the existing bounded row-major coordinate and introduces no runtime conversion. -/
noncomputable def matrixCoordinates (rows columns : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (boundedIndex (rows * columns)).reindex
    (fun sizes => Fin (MvPolynomial.eval sizes rows) × Fin (MvPolynomial.eval sizes columns))
    (matrixCoordinateEquiv rows columns)

/-- Binary naturals with an exact polynomial word width. -/
noncomputable abbrev binaryNaturalsOfWidth (width : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  boundedIndexOfWidth (fun sizes => 2 ^ MvPolynomial.eval sizes width) width (fun _ => le_rfl)

@[simp] theorem binaryNaturalsOfWidth_width (width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) :
    (binaryNaturalsOfWidth width).width sizes = MvPolynomial.eval sizes width := rfl

/-- Polynomial-width naturals retain the canonical bits of their ordinary finite value. -/
@[simp] theorem binaryNaturalsOfWidth_encode_bits (width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (value : (binaryNaturalsOfWidth width).Carrier sizes) :
    ArrayEncoding.bits ((binaryNaturalsOfWidth width).encode sizes value) =
      ArrayEncoding.bits (BitVec.ofFin value) := by
  simp only [binaryNaturalsOfWidth, boundedIndexOfWidth, ofCodec, ArrayEncoding.bits_cast,
    BitVec.ofNatLT_finVal]

/-- Boolean results use one canonical bit, with no unused labels. -/
noncomputable def booleans : EncodedDomain Parameter := fixed finTwoEquiv.symm

@[simp] theorem booleans_width (sizes : Parameter → ℕ) : (booleans : EncodedDomain Parameter).width sizes = 1 := by
  simp [booleans, fixed, ofCodec]
  decide

end Polytime2.EncodedDomain
