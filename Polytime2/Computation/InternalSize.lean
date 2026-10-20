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

import Polytime2.Computation.Substitution

/-! # Hiding a counter-capacity size behind two public dimensions

A certified call uses the internal assignment `[K + L + 1, K, L]`. The new
capacity header is constructed at runtime in private storage, and polynomial
bounds are substituted at the unchanged public assignment.
-/

namespace Polytime2

namespace Computation.Realizable.Internal

open MultiTape CallingConvention

/-- The first source size is private; the other two remain independent. -/
def internalSizes (sizes : Fin 2 → ℕ) : Fin 3 → ℕ :=
  ![sizes 0 + sizes 1 + 1, sizes 0, sizes 1]

noncomputable def internalPolynomials : Fin 3 → MvPolynomial (Fin 2) ℕ :=
  ![MvPolynomial.X 0 + MvPolynomial.X 1 + 1, MvPolynomial.X 0, MvPolynomial.X 1]

noncomputable abbrev internalBound (bound : MvPolynomial (Fin 3) ℕ) :
    MvPolynomial (Fin 2) ℕ := SizeSubstitution.polynomial internalPolynomials bound

theorem internalBound_eval (bound : MvPolynomial (Fin 3) ℕ) (sizes : Fin 2 → ℕ) :
    MvPolynomial.eval sizes (internalBound bound) = MvPolynomial.eval (internalSizes sizes) bound := by
  rw [internalBound, SizeSubstitution.polynomial_eval]
  have equal : SizeSubstitution.assignment internalPolynomials sizes = internalSizes sizes := by
    funext parameter
    fin_cases parameter <;> simp [SizeSubstitution.assignment, internalPolynomials, internalSizes]
  rw [equal]

/-- One private capacity accommodates both dimensions and their product. -/
theorem internalCapacity_fits (sizes : Fin 2 → ℕ) :
    sizes 0 < 2 ^ (sizes 0 + sizes 1 + 1) ∧
      sizes 1 < 2 ^ (sizes 0 + sizes 1 + 1) ∧
      sizes 0 * sizes 1 ≤ 2 ^ (sizes 0 + sizes 1 + 1) := by
  have rows := (sizes 0).lt_two_pow_self
  have columns := (sizes 1).lt_two_pow_self
  have rowsPower : 2 ^ sizes 0 ≤ 2 ^ (sizes 0 + sizes 1 + 1) :=
    pow_le_pow_right₀ (by decide) (by omega)
  have columnsPower : 2 ^ sizes 1 ≤ 2 ^ (sizes 0 + sizes 1 + 1) :=
    pow_le_pow_right₀ (by decide) (by omega)
  refine ⟨rows.trans_le rowsPower, columns.trans_le columnsPower, ?_⟩
  calc
    sizes 0 * sizes 1 ≤ 2 ^ sizes 0 * 2 ^ sizes 1 := Nat.mul_le_mul rows.le columns.le
    _ = 2 ^ (sizes 0 + sizes 1) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (sizes 0 + sizes 1 + 1) := pow_le_pow_right₀ (by decide) (by omega)

end Computation.Realizable.Internal

namespace EncodedDomain

-- carrierLevel: mathematical values in the original and specialized domains.
universe carrierLevel

/-- Substitute the private capacity while retaining the original encoded bits. -/
noncomputable def withInternalSize (domain : EncodedDomain.{0, carrierLevel} (Fin 3)) :
    EncodedDomain (Fin 2) :=
  ofCodec (fun sizes => domain.Carrier (Computation.Realizable.Internal.internalSizes sizes))
    (Computation.Realizable.Internal.internalBound domain.widthPolynomial)
    (fun sizes => domain.width (Computation.Realizable.Internal.internalSizes sizes))
    (fun sizes => (Computation.Realizable.Internal.internalBound_eval domain.widthPolynomial sizes).symm)
    (fun sizes => domain.encode (Computation.Realizable.Internal.internalSizes sizes))
    (fun sizes => domain.decode (Computation.Realizable.Internal.internalSizes sizes))
    (fun sizes => domain.decode_encode (Computation.Realizable.Internal.internalSizes sizes))
    (fun sizes => domain.encode_decode (Computation.Realizable.Internal.internalSizes sizes))

@[simp] theorem withInternalSize_width (domain : EncodedDomain.{0, carrierLevel} (Fin 3))
    (sizes : Fin 2 → ℕ) : domain.withInternalSize.width sizes =
      domain.width (Computation.Realizable.Internal.internalSizes sizes) :=
  Computation.Realizable.Internal.internalBound_eval domain.widthPolynomial sizes

/-- Private size substitution retains the canonical binary word. -/
@[simp] theorem withInternalSize_encode_bits (domain : EncodedDomain.{0, carrierLevel} (Fin 3))
    (sizes : Fin 2 → ℕ) (value : domain.Carrier (Computation.Realizable.Internal.internalSizes sizes)) :
    ArrayEncoding.bits (domain.withInternalSize.encode sizes value) =
      ArrayEncoding.bits (domain.encode (Computation.Realizable.Internal.internalSizes sizes) value) := by
  simp only [withInternalSize, ofCodec, ArrayEncoding.bits_cast]

/-- Substituting private sizes preserves the canonical tape. -/
@[simp] theorem encoded_withInternalSize (domain : EncodedDomain.{0, carrierLevel} (Fin 3))
    (sizes : Fin 2 → ℕ) (value : domain.Carrier (Computation.Realizable.Internal.internalSizes sizes)) :
    CallingConvention.encoded domain.withInternalSize sizes value =
      CallingConvention.encoded domain (Computation.Realizable.Internal.internalSizes sizes) value := by
  exact congrArg CallingConvention.tape (withInternalSize_encode_bits domain sizes value)

end EncodedDomain

namespace Computation

open MultiTape CallingConvention Realizable.Internal

universe carrierLevel
variable {InputName : Type} [Fintype InputName]

/-- Replace a caller-supplied counter capacity with a certified private size.
The two public sizes are the original row and column dimensions. -/
noncomputable def withInternalSize (computation : Computation.{carrierLevel} (Fin 3) InputName) :
    Computation (Fin 2) InputName where
  inputDomains name := (computation.inputDomains name).withInternalSize
  outputDomain := computation.outputDomain.withInternalSize
  precondition sizes := computation.precondition (internalSizes sizes)
  compute sizes := computation.compute (internalSizes sizes)

namespace Realizable

/-- The generated unary header, all private storage, and substituted runtime
witnesses stay inside the certificate. Its construction is charged. -/
theorem withInternalSize {computation : Computation.{carrierLevel} (Fin 3) InputName}
    (realizable : computation.Realizable) : computation.withInternalSize.Realizable := by
  let domainAt (assignment : (Fin 2 → ℕ) → Fin 3 → ℕ)
      (compatible : ∀ bound sizes, MvPolynomial.eval sizes (internalBound bound) =
        MvPolynomial.eval (assignment sizes) bound)
      (domain : EncodedDomain.{0, carrierLevel} (Fin 3)) : EncodedDomain (Fin 2) :=
    EncodedDomain.ofCodec (fun sizes => domain.Carrier (assignment sizes))
      (internalBound domain.widthPolynomial) (fun sizes => domain.width (assignment sizes))
      (fun sizes => (compatible domain.widthPolynomial sizes).symm)
      (fun sizes => domain.encode (assignment sizes))
      (fun sizes => domain.decode (assignment sizes))
      (fun sizes => domain.decode_encode (assignment sizes))
      (fun sizes => domain.encode_decode (assignment sizes))
  let computationAt assignment compatible : Computation (Fin 2) InputName :=
    ⟨(fun name => domainAt assignment compatible (computation.inputDomains name)),
      domainAt assignment compatible computation.outputDomain,
      (fun sizes => computation.precondition (assignment sizes)),
      (fun sizes => computation.compute (assignment sizes))⟩
  have transfer : ∀ assignment compatible,
      assignment = SizeSubstitution.assignment internalPolynomials →
      (computationAt assignment compatible).Realizable := by
    intro assignment compatible equal
    subst assignment
    exact realizable.substitute internalPolynomials
  apply transfer internalSizes internalBound_eval
  funext sizes parameter
  fin_cases parameter <;>
    simp [SizeSubstitution.assignment, internalPolynomials, internalSizes]


end Realizable
end Computation
end Polytime2
