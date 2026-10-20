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

import Polytime2.Encoding.EncodedArray
import Mathlib.Algebra.MvPolynomial.Rename

/-! # Renaming size parameters without changing mathematical payloads -/

namespace Polytime2.EncodedDomain

universe carrierLevel

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Interpret a domain using selected size names in a larger parameter family.
The carrier uses the direct projection, while the exact width is renamed. -/
noncomputable def renameParameters (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) : EncodedDomain NewParameter :=
  ofCodec (fun sizes => domain.Carrier (sizes ∘ names)) (MvPolynomial.rename names domain.widthPolynomial)
    (fun sizes => domain.width (sizes ∘ names))
    (fun sizes => (MvPolynomial.eval_rename names sizes domain.widthPolynomial).symm)
    (fun sizes => domain.encode (sizes ∘ names)) (fun sizes => domain.decode (sizes ∘ names))
    (fun sizes => domain.decode_encode (sizes ∘ names)) (fun sizes => domain.encode_decode (sizes ∘ names))

@[simp] theorem renameParameters_widthPolynomial (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) :
    (domain.renameParameters names).widthPolynomial = MvPolynomial.rename names domain.widthPolynomial := rfl

@[simp] theorem renameParameters_width (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) (sizes : NewParameter → ℕ) :
    (domain.renameParameters names).width sizes = domain.width (sizes ∘ names) := by
  change MvPolynomial.eval sizes (MvPolynomial.rename names domain.widthPolynomial) = _
  exact MvPolynomial.eval_rename names sizes domain.widthPolynomial

@[simp] theorem renameParameters_bits (domain : EncodedDomain.{0, carrierLevel} Parameter)
    (names : Parameter → NewParameter) (sizes : NewParameter → ℕ) (value : domain.Carrier (sizes ∘ names)) :
    ArrayEncoding.bits ((domain.renameParameters names).encode sizes value) =
      ArrayEncoding.bits (domain.encode (sizes ∘ names) value) := by
  simp only [renameParameters, ofCodec, ArrayEncoding.bits_cast]

end Polytime2.EncodedDomain
