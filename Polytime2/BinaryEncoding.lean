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

import Polytime2.Binary
import Polytime2.EncodedDomain
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

/-- Boolean results use one canonical bit, with no unused labels. -/
noncomputable def booleans : EncodedDomain Parameter := fixed finTwoEquiv.symm

end Polytime2.EncodedDomain
