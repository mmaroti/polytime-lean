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

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.BitVec
import Mathlib.Data.Nat.Log

/-! # Bounded mathematical domains with canonical bit encodings

A domain may be constructed from any fixed specialization. Its carrier and
exact width vary with size assignments; a concrete polynomial gives the width.
These presentations specify meaning, not the runtime of encoding or decoding.
Working tape layouts and scratch remain separate representation relations.
-/

namespace Polytime2

-- parameterLevel: size parameter names; carrierLevel: mathematical elements.
universe parameterLevel carrierLevel

/-- A mathematical family with a unique accepted encoding for each element. -/
structure EncodedDomain (Parameter : Type parameterLevel) [Fintype Parameter] where
  Carrier : (Parameter → ℕ) → Type carrierLevel
  widthPolynomial : MvPolynomial Parameter ℕ
  encode : ∀ assignment, Carrier assignment →
    BitVec (MvPolynomial.eval assignment widthPolynomial)
  decode : ∀ assignment, BitVec (MvPolynomial.eval assignment widthPolynomial) →
    Option (Carrier assignment)
  decode_encode : ∀ assignment value, decode assignment (encode assignment value) = some value
  encode_decode : ∀ assignment bits value,
    decode assignment bits = some value → encode assignment value = bits

namespace EncodedDomain

variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The exact number of bits, obtained by evaluating the domain's polynomial. -/
@[simp] noncomputable abbrev width (domain : EncodedDomain Parameter) (assignment : Parameter → ℕ) : ℕ :=
  MvPolynomial.eval assignment domain.widthPolynomial

/-- Construct a domain from a codec whose width equals the chosen polynomial.
The equality only transports vector types; it is not stored in the domain. -/
noncomputable abbrev ofCodec (Carrier : (Parameter → ℕ) → Type carrierLevel)
    (widthPolynomial : MvPolynomial Parameter ℕ) (width : (Parameter → ℕ) → ℕ)
    (width_eq : ∀ assignment, width assignment = MvPolynomial.eval assignment widthPolynomial)
    (encode : ∀ assignment, Carrier assignment → BitVec (width assignment))
    (decode : ∀ assignment, BitVec (width assignment) → Option (Carrier assignment))
    (decode_encode : ∀ assignment value, decode assignment (encode assignment value) = some value)
    (encode_decode : ∀ assignment bits value,
      decode assignment bits = some value → encode assignment value = bits) :
    EncodedDomain Parameter where
  Carrier := Carrier
  widthPolynomial := widthPolynomial
  encode assignment value := (encode assignment value).cast (width_eq assignment)
  decode assignment bits := decode assignment (bits.cast (width_eq assignment).symm)
  decode_encode assignment value := by simpa using decode_encode assignment value
  encode_decode assignment bits value accepted := by
    simpa using congrArg (fun value => value.cast (width_eq assignment))
      (encode_decode assignment _ value accepted)

/-- A chosen finite enumeration fixes labels and width before runtime sizes. -/
noncomputable def fixed {Carrier : Type carrierLevel} {cardinality : ℕ}
    (enumeration : Carrier ≃ Fin cardinality) : EncodedDomain Parameter :=
  ofCodec (fun _ => Carrier) (MvPolynomial.C (Nat.clog 2 cardinality))
    (fun _ => Nat.clog 2 cardinality) (by intro assignment; simp)
    (fun _ value => BitVec.ofNatLT (enumeration value).val
      (lt_of_lt_of_le (enumeration value).isLt (Nat.le_pow_clog (by decide) cardinality)))
    (fun _ bits => if valid : bits.toNat < cardinality then
      some (enumeration.symm ⟨bits.toNat, valid⟩) else none)
    (by intro assignment value; simp [BitVec.toNat_ofNatLT, (enumeration value).isLt])
    (by
      intro assignment bits value hypothesis
      split at hypothesis
      next valid =>
        have equality := Option.some.inj hypothesis
        subst value
        apply BitVec.eq_of_toNat_eq
        simp
      next invalid => simp at hypothesis)

/-- A specialization-fixed presentation can be used alongside any runtime size
parameters without changing its carrier, width, or encoding. -/
noncomputable def constant (domain : EncodedDomain.{0, carrierLevel} Empty) : EncodedDomain Parameter :=
  ofCodec (fun _ => domain.Carrier Empty.elim) (MvPolynomial.C (domain.width Empty.elim))
    (fun _ => domain.width Empty.elim) (by intro assignment; simp)
    (fun _ => domain.encode Empty.elim) (fun _ => domain.decode Empty.elim)
    (fun _ => domain.decode_encode Empty.elim) (fun _ => domain.encode_decode Empty.elim)

/-- A size input has exactly the assigned number of unary ones. Its value is
already fixed by the assignment, so its mathematical carrier is a singleton. -/
noncomputable def unary (parameter : Parameter) : EncodedDomain Parameter :=
  ofCodec (fun _ => PUnit.{carrierLevel + 1}) (MvPolynomial.X parameter)
    (fun assignment => assignment parameter) (by intro assignment; simp)
    (fun assignment _ => BitVec.allOnes (assignment parameter))
    (fun assignment bits => if bits = BitVec.allOnes (assignment parameter) then some PUnit.unit else none)
    (by intro assignment value; cases value; simp)
    (by
      intro assignment bits value valid
      split at valid
      next equal => exact equal.symm
      next different => simp at valid)

/-- Restrict a mathematical carrier while preserving its accepted canonical bits. -/
noncomputable def restrict (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (predicate : ∀ sizes, domain.Carrier sizes → Prop)
    [∀ sizes, DecidablePred (predicate sizes)] : EncodedDomain Parameter where
  Carrier sizes := {value : domain.Carrier sizes // predicate sizes value}
  widthPolynomial := domain.widthPolynomial
  encode sizes value := domain.encode sizes value.val
  decode sizes bits := do
    let value ← domain.decode sizes bits
    if valid : predicate sizes value then some ⟨value, valid⟩ else none
  decode_encode sizes value := by simp [domain.decode_encode, value.property]
  encode_decode sizes bits value accepted := by
    simp only [Bind.bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨decoded, decodedEq, accepted⟩ := accepted
    split at accepted
    · cases Option.some.inj accepted
      exact domain.encode_decode sizes bits decoded decodedEq
    · contradiction

/-- Words for excluded values are rejected, rather than normalized. -/
theorem restrict_decode_rejected
    (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (predicate : ∀ sizes, domain.Carrier sizes → Prop)
    [∀ sizes, DecidablePred (predicate sizes)]
    (sizes : Parameter → ℕ) (value : domain.Carrier sizes) (invalid : ¬ predicate sizes value) :
    (domain.restrict predicate).decode sizes (domain.encode sizes value) = none := by
  simp only [restrict, domain.decode_encode]
  simp [invalid]

/-- Change the mathematical carrier while retaining its canonical bit layout. -/
def reindex (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (Carrier' : (Parameter → ℕ) → Type carrierLevel)
    (equivalence : ∀ assignment, Carrier' assignment ≃ domain.Carrier assignment) :
    EncodedDomain Parameter where
  Carrier := Carrier'
  widthPolynomial := domain.widthPolynomial
  encode assignment value := domain.encode assignment (equivalence assignment value)
  decode assignment bits := (domain.decode assignment bits).map (equivalence assignment).symm
  decode_encode assignment value := by
    simp [domain.decode_encode]
  encode_decode assignment bits value accepted := by
    cases decoding : domain.decode assignment bits with
    | none => simp [decoding] at accepted
    | some oldValue =>
      simp [decoding] at accepted
      have valuesEqual : oldValue = equivalence assignment value := by
        simpa using congrArg (equivalence assignment) accepted
      have oldAccepted : domain.decode assignment bits = some (equivalence assignment value) := by
        rw [decoding, valuesEqual]
      exact domain.encode_decode assignment bits (equivalence assignment value) oldAccepted

@[simp] theorem fixed_widthPolynomial {Carrier : Type carrierLevel} {cardinality : ℕ}
    (enumeration : Carrier ≃ Fin cardinality) :
    (fixed (Parameter := Parameter) enumeration).widthPolynomial = MvPolynomial.C (Nat.clog 2 cardinality) := rfl

@[simp] theorem constant_widthPolynomial (domain : EncodedDomain.{0, carrierLevel} Empty) :
    (domain.constant (Parameter := Parameter)).widthPolynomial = MvPolynomial.C (domain.width Empty.elim) := rfl

theorem reindex_widthPolynomial (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (Carrier' : (Parameter → ℕ) → Type carrierLevel)
    (equivalence : ∀ assignment, Carrier' assignment ≃ domain.Carrier assignment) :
    (domain.reindex Carrier' equivalence).widthPolynomial = domain.widthPolynomial := rfl

end EncodedDomain
end Polytime2
