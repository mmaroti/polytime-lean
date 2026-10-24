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

import Polytime2.Encoding.Integers
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Canonical bounded cyclic and free coordinates

Store a bounded natural modulus and a bounded actual ZMod value. At modulus
zero the coordinate is an integer and its sign is retained. At positive
moduli use the unique nonnegative representative below the modulus. The
codec reuses the existing unsigned/signed pair and excludes noncanonical
representatives. No runtime tags or extra structures enter the carrier.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Canonical integer representatives, including all integers at modulus zero. -/
def cyclicRepresentativeCanonical (modulus : ℕ) (value : ℤ) : Prop :=
  modulus = 0 ∨ 0 ≤ value ∧ value < (modulus : ℤ)

/-- Casting a coordinate back to integers preserves its magnitude measure. -/
theorem cyclic_cast_natAbs (modulus : ℕ) (value : ZMod modulus) :
    (ZMod.cast value : ℤ).natAbs = value.val := by
  cases modulus with
  | zero => simp [ZMod.cast, ZMod.val]
  | succ modulus => rw [ZMod.cast_eq_val]; exact Int.natAbs_natCast _

/-- The ordinary integer representative is canonical for every modulus. -/
theorem cyclic_cast_canonical (modulus : ℕ) (value : ZMod modulus) :
    cyclicRepresentativeCanonical modulus (ZMod.cast value : ℤ) := by
  cases modulus with
  | zero => exact Or.inl rfl
  | succ modulus =>
    right
    rw [ZMod.cast_eq_val]
    exact ⟨by positivity, by exact_mod_cast value.val_lt⟩

/-- Reading back a canonical integer representative is the identity. -/
theorem cyclic_cast_intCast (modulus : ℕ) (value : ℤ)
    (canonical : cyclicRepresentativeCanonical modulus value) :
    (ZMod.cast (value : ZMod modulus) : ℤ) = value := by
  rcases canonical with zero | ⟨nonnegative, smaller⟩
  · subst modulus
    change (Int.cast value : ℤ) = value
    exact Int.cast_id
  · have nonzero : modulus ≠ 0 := by omega
    have : NeZero modulus := ⟨nonzero⟩
    rw [ZMod.cast_eq_val, ZMod.val_intCast]
    exact Int.emod_eq_of_lt nonnegative smaller

private noncomputable def raw (modulusWidth valueWidth : MvPolynomial Parameter ℕ) : EncodedDomain Parameter := by
  classical
  exact ((binaryNaturalsOfWidth modulusWidth).prod (binaryIntegers valueWidth)).restrict
    (fun _ pair => cyclicRepresentativeCanonical pair.1.val pair.2.val)

private noncomputable def coordinateEquiv (modulusWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    ((modulus : Fin (2 ^ MvPolynomial.eval sizes modulusWidth)) ×
      {value : ZMod modulus.val // value.val < 2 ^ MvPolynomial.eval sizes valueWidth}) ≃
        (raw modulusWidth valueWidth).Carrier sizes where
  toFun value := ⟨(value.1, ⟨(ZMod.cast value.2.val : ℤ), by
    rw [cyclic_cast_natAbs]
    exact value.2.property⟩), cyclic_cast_canonical value.1.val value.2.val⟩
  invFun value := ⟨value.val.1, ⟨(value.val.2.val : ZMod value.val.1.val), by
    rw [← cyclic_cast_natAbs, cyclic_cast_intCast _ _ value.property]
    exact value.val.2.property⟩⟩
  left_inv := by
    rintro ⟨modulus, value⟩
    apply congrArg (Sigma.mk modulus)
    apply Subtype.ext
    exact ZMod.intCast_zmod_cast value.val
  right_inv := by
    intro value
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact cyclic_cast_intCast _ _ value.property

/-- Actual bounded cyclic/free coordinates, with their natural modulus retained. -/
noncomputable def boundedCyclic (modulusWidth valueWidth : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (raw modulusWidth valueWidth).reindex
    (fun sizes => (modulus : Fin (2 ^ MvPolynomial.eval sizes modulusWidth)) ×
      {value : ZMod modulus.val // value.val < 2 ^ MvPolynomial.eval sizes valueWidth})
    (coordinateEquiv modulusWidth valueWidth)

/-- Construct a coordinate from a known canonical signed representative. -/
noncomputable def boundedCyclicOfRepresentative (modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (modulus : (binaryNaturalsOfWidth modulusWidth).Carrier sizes)
    (value : (binaryIntegers valueWidth).Carrier sizes)
    (canonical : cyclicRepresentativeCanonical modulus.val value.val) :
    (boundedCyclic modulusWidth valueWidth).Carrier sizes :=
  ⟨modulus, ⟨(value.val : ZMod modulus.val), by
    rw [← cyclic_cast_natAbs, cyclic_cast_intCast _ _ canonical]
    exact value.property⟩⟩

/-- The mathematical coordinate retains the pair's exact canonical words. -/
theorem boundedCyclicOfRepresentative_encode_bits (modulusWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (modulus : (binaryNaturalsOfWidth modulusWidth).Carrier sizes)
    (value : (binaryIntegers valueWidth).Carrier sizes)
    (canonical : cyclicRepresentativeCanonical modulus.val value.val) :
    ArrayEncoding.bits ((boundedCyclic modulusWidth valueWidth).encode sizes
      (boundedCyclicOfRepresentative modulusWidth valueWidth sizes modulus value canonical)) =
    ArrayEncoding.bits (((binaryNaturalsOfWidth modulusWidth).prod (binaryIntegers valueWidth)).encode sizes (modulus, value)) := by
  have same : coordinateEquiv modulusWidth valueWidth sizes
      (boundedCyclicOfRepresentative modulusWidth valueWidth sizes modulus value canonical) =
      (⟨(modulus, value), canonical⟩ : (raw modulusWidth valueWidth).Carrier sizes) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact cyclic_cast_intCast _ _ canonical
  change ArrayEncoding.bits ((raw modulusWidth valueWidth).encode sizes _) = _
  rw [same]
  rfl

end Polytime2.EncodedDomain
