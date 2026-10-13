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
exact width vary with size assignments; one polynomial bounds every width.
These presentations specify meaning, not the runtime of encoding or decoding.
Working tape layouts and scratch remain separate representation relations.
-/

namespace Polytime2

-- parameterLevel: size parameter names; carrierLevel: mathematical elements.
universe parameterLevel carrierLevel

/-- A mathematical family with a unique accepted encoding for each element. -/
structure EncodedDomain (Parameter : Type parameterLevel) [Fintype Parameter] where
  Carrier : (Parameter → ℕ) → Type carrierLevel
  width : (Parameter → ℕ) → ℕ
  encode : ∀ assignment, Carrier assignment → BitVec (width assignment)
  decode : ∀ assignment, BitVec (width assignment) → Option (Carrier assignment)
  decode_encode : ∀ assignment value, decode assignment (encode assignment value) = some value
  encode_decode : ∀ assignment bits value,
    decode assignment bits = some value → encode assignment value = bits
  polynomial_width : ∃ bound : MvPolynomial Parameter ℕ,
    ∀ assignment, width assignment ≤ MvPolynomial.eval assignment bound

namespace EncodedDomain

variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- A chosen finite enumeration fixes labels and width before runtime sizes. -/
def fixed {Carrier : Type carrierLevel} {cardinality : ℕ}
    (enumeration : Carrier ≃ Fin cardinality) : EncodedDomain Parameter where
  Carrier _ := Carrier
  width _ := Nat.clog 2 cardinality
  encode _ value := BitVec.ofNatLT (enumeration value).val
    (lt_of_lt_of_le (enumeration value).isLt (Nat.le_pow_clog (by decide) cardinality))
  decode _ bits := if valid : bits.toNat < cardinality then
    some (enumeration.symm ⟨bits.toNat, valid⟩) else none
  decode_encode _ value := by simp [BitVec.toNat_ofNatLT, (enumeration value).isLt]
  encode_decode _ bits value hypothesis := by
    split at hypothesis
    next valid =>
      have equality := Option.some.inj hypothesis
      subst value
      apply BitVec.eq_of_toNat_eq
      simp
    next invalid => simp at hypothesis
  polynomial_width := ⟨MvPolynomial.C (Nat.clog 2 cardinality), by intro assignment; simp⟩

/-- A specialization-fixed presentation can be used alongside any runtime size
parameters without changing its carrier, width, or encoding. -/
def constant (domain : EncodedDomain.{0, carrierLevel} Empty) : EncodedDomain Parameter where
  Carrier _ := domain.Carrier Empty.elim
  width _ := domain.width Empty.elim
  encode _ := domain.encode Empty.elim
  decode _ := domain.decode Empty.elim
  decode_encode _ := domain.decode_encode Empty.elim
  encode_decode _ := domain.encode_decode Empty.elim
  polynomial_width := ⟨MvPolynomial.C (domain.width Empty.elim), by intro assignment; simp⟩

/-- A size input has exactly the assigned number of unary ones. Its value is
already fixed by the assignment, so its mathematical carrier is a singleton. -/
def unary (parameter : Parameter) : EncodedDomain Parameter where
  Carrier _ := PUnit.{carrierLevel + 1}
  width assignment := assignment parameter
  encode assignment _ := BitVec.allOnes (assignment parameter)
  decode assignment bits := if bits = BitVec.allOnes (assignment parameter) then some PUnit.unit else none
  decode_encode assignment value := by cases value; simp
  encode_decode assignment bits value valid := by
    split at valid
    next equal => exact equal.symm
    next different => simp at valid
  polynomial_width := ⟨MvPolynomial.X parameter, by intro assignment; simp⟩

/-- Change the mathematical carrier while retaining its canonical bit layout. -/
def reindex (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (Carrier' : (Parameter → ℕ) → Type carrierLevel)
    (equivalence : ∀ assignment, Carrier' assignment ≃ domain.Carrier assignment) :
    EncodedDomain Parameter where
  Carrier := Carrier'
  width := domain.width
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
  polynomial_width := domain.polynomial_width

end EncodedDomain
end Polytime2
