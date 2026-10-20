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

import Polytime2.Encoding.Records

/-! # Bounded dependent pairs without changing mathematical carriers

The index is encoded first, followed by a dependent payload with binary zero
padding to a polynomial capacity. Decoding rejects nonzero padding.
-/

namespace Polytime2.EncodedDomain

variable {Parameter IndexName : Type} [Fintype Parameter] [Fintype IndexName]

/-- Zero extension preserves the exact payload prefix and adds only binary zeros. -/
theorem bits_setWidth {width capacity : ℕ} (bits : BitVec width) (fits : width ≤ capacity) :
    ArrayEncoding.bits (bits.setWidth capacity) =
      ArrayEncoding.bits bits ++ List.replicate (capacity - width) false := by
  apply List.ext_getElem
  · simp only [ArrayEncoding.bits, List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro position leftWithin rightWithin
    by_cases inside : position < width
    · simp [ArrayEncoding.bits, inside]
    · have outside : width ≤ position := Nat.le_of_not_gt inside
      simp [ArrayEncoding.bits, List.getElem_append, inside, BitVec.getLsbD_of_ge bits position outside]

/-- Truncation retains exactly the requested prefix of the canonical bits. -/
theorem bits_setWidth_take {width length : ℕ} (bits : BitVec width) (fits : length ≤ width) :
    ArrayEncoding.bits (bits.setWidth length) = (ArrayEncoding.bits bits).take length := by
  apply List.ext_getElem
  · simp [ArrayEncoding.bits, Nat.min_eq_left fits]
  · intro position leftWithin rightWithin
    simp [ArrayEncoding.bits, -BitVec.getLsbD_eq_getElem]

/-- Polynomial-capacity zero padding retains every mathematical payload. -/
theorem encode_setWidth_injective (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (capacity : ℕ) (fits : domain.width sizes ≤ capacity) :
    Function.Injective (fun value => (domain.encode sizes value).setWidth capacity) := by
  intro first second equal
  have exactBits := congrArg (fun bits : BitVec capacity => bits.setWidth (domain.width sizes)) equal
  simp only [BitVec.setWidth_setWidth_of_le _ fits, BitVec.setWidth_eq] at exactBits
  have decoded := congrArg (domain.decode sizes) exactBits
  simpa only [domain.decode_encode, Option.some.injEq] using decoded

/-- Named fields use the existing record codec in a fixed specialization order.
-/
noncomputable def namedRecord (fields : IndexName → EncodedDomain Parameter) : EncodedDomain Parameter :=
  (record (Fintype.card IndexName) (fun index => fields ((Fintype.equivFin IndexName).symm index))).reindex
    (fun sizes => ∀ name, (fields name).Carrier sizes)
    (fun sizes => (Equiv.piCongrLeft (fun name => (fields name).Carrier sizes)
      (Fintype.equivFin IndexName).symm).symm)

/-- A bounded dependent codec retains the exact mathematical payload family.
Only the storage width is padded to the caller's polynomial capacity. -/
noncomputable abbrev ofBoundedCodec (index : EncodedDomain Parameter)
    (Payload : ∀ sizes, index.Carrier sizes → Type)
    (width : ∀ sizes, index.Carrier sizes → ℕ)
    (encodePayload : ∀ sizes value, Payload sizes value → BitVec (width sizes value))
    (decodePayload : ∀ sizes value, BitVec (width sizes value) → Option (Payload sizes value))
    (decodeEncode : ∀ sizes value payload, decodePayload sizes value (encodePayload sizes value payload) = some payload)
    (capacity : MvPolynomial Parameter ℕ)
    (fits : ∀ sizes value, width sizes value ≤ MvPolynomial.eval sizes capacity) : EncodedDomain Parameter :=
  let storage := index.prod (bitVectors capacity)
  { Carrier := fun sizes => Σ value : index.Carrier sizes, Payload sizes value
    widthPolynomial := storage.widthPolynomial
    encode := fun sizes value => storage.encode sizes
      (value.1, (encodePayload sizes value.1 value.2).setWidth (MvPolynomial.eval sizes capacity))
    decode := fun sizes bits => do
      let value ← storage.decode sizes bits
      let decoded ← decodePayload sizes value.1 (value.2.setWidth (width sizes value.1))
      if (encodePayload sizes value.1 decoded).setWidth (MvPolynomial.eval sizes capacity) = value.2
        then some ⟨value.1, decoded⟩ else none
    decode_encode := by
      intro sizes value
      simp only [Bind.bind, storage.decode_encode, Option.bind_some,
        BitVec.setWidth_setWidth_of_le _ (fits sizes value.1), BitVec.setWidth_eq,
        decodeEncode, ↓reduceIte]
    encode_decode := by
      intro sizes bits value accepted
      cases stored : storage.decode sizes bits with
      | none => simp [stored] at accepted
      | some pair =>
        simp only [Bind.bind, stored, Option.bind_some] at accepted
        cases decoded : decodePayload sizes pair.1 (pair.2.setWidth (width sizes pair.1)) with
        | none => simp [decoded] at accepted
        | some answer =>
          simp only [decoded, Option.bind_some] at accepted
          split at accepted
          · cases Option.some.inj accepted
            have same := storage.encode_decode sizes bits pair stored
            simpa only [‹(encodePayload sizes pair.1 answer).setWidth
              (MvPolynomial.eval sizes capacity) = pair.2›] using same
          · contradiction }

variable {NewParameter : Type} [Fintype NewParameter]

/-- A dependent payload reparameterized by the decoded index is one bounded
codec family. Its mathematical carrier and canonical bits are unchanged. -/
noncomputable def boundedSigma (index : EncodedDomain Parameter)
    (assignment : ∀ sizes, index.Carrier sizes → NewParameter → ℕ)
    (payload : EncodedDomain NewParameter) (capacity : MvPolynomial Parameter ℕ)
    (fits : ∀ sizes value, payload.width (assignment sizes value) ≤ MvPolynomial.eval sizes capacity) :
    EncodedDomain Parameter :=
  ofBoundedCodec index (fun sizes value => payload.Carrier (assignment sizes value))
    (fun sizes value => payload.width (assignment sizes value))
    (fun sizes value => payload.encode (assignment sizes value))
    (fun sizes value => payload.decode (assignment sizes value))
    (fun sizes value => payload.decode_encode (assignment sizes value)) capacity fits

end Polytime2.EncodedDomain
