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

import Polytime2.Computation.Unary
import Polytime2.Computation.Arguments
import Polytime2.Computation.Width
import Polytime2.Computation.Reindex
import Polytime2.Encoding.Records

/-! # Certified bit-preserving maps and polynomial zero words -/

namespace Polytime2.Computation

open CallingConvention

variable {Parameter : Type} [Fintype Parameter]

/-- A total mathematical map implemented by copying the same canonical bits. -/
def encodingMap (source target : EncodedDomain Parameter)
    (compute : ∀ sizes, source.Carrier sizes → target.Carrier sizes) : Computation Parameter Unit :=
  unaryMap source target (fun _ _ => True) (fun sizes value => compute sizes value.val)

/-- A fixed finite-memory bit transducer realizes its mathematical word map. -/
theorem bitTransducer_realizable {Memory : Type} [Fintype Memory]
    (update : Memory → Bool → Memory × Bool) (memory : Memory)
    (source target : EncodedDomain Parameter)
    (compute : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (sameWidth : ∀ sizes, target.width sizes = source.width sizes)
    (correct : ∀ sizes value,
      (BinaryScan.run update memory (EncodedDomain.ArrayEncoding.bits (source.encode sizes value))).2 =
        EncodedDomain.ArrayEncoding.bits (target.encode sizes (compute sizes value))) :
    (encodingMap source target compute).Realizable := by
  refine Realizable.Internal.ofUnaryRealizes _ (StandardBinaryScan.algorithm update)
    (.inl (.inl memory)) (.inr ()) ?_
  exact (StandardBinaryScan.contract update memory source target sameWidth
    (fun _ _ => True) compute (fun sizes value _ => correct sizes value)).postcondition
      (by intro sizes input output equal; exact ⟨trivial, equal⟩)

/-- Bit-preserving carrier maps need no inverse or additional representation. -/
theorem encodingMap_realizable (source target : EncodedDomain Parameter)
    (compute : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (sameWidth : ∀ sizes, target.width sizes = source.width sizes)
    (sameBits : ∀ sizes value,
      EncodedDomain.ArrayEncoding.bits (source.encode sizes value) =
        EncodedDomain.ArrayEncoding.bits (target.encode sizes (compute sizes value))) :
    (encodingMap source target compute).Realizable :=
  bitTransducer_realizable BinaryScan.copy () source target compute sameWidth
    (by intro sizes value; simpa only [BinaryScan.copy_run] using sameBits sizes value)

/-- The canonical encoding itself is a polynomial-time computation. -/
theorem encode_realizable (domain : EncodedDomain Parameter) :
    (encodingMap domain (EncodedDomain.bitVectors domain.widthPolynomial) domain.encode).Realizable :=
  encodingMap_realizable _ _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- Modular increment at an arbitrary polynomial bit width. -/
noncomputable def incrementBits (polynomial : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (EncodedDomain.bitVectors polynomial) (EncodedDomain.bitVectors polynomial)
    (fun sizes value => BitVec.ofNat (MvPolynomial.eval sizes polynomial) (value.toNat + 1))

theorem incrementBits_realizable (polynomial : MvPolynomial Parameter ℕ) :
    (incrementBits polynomial).Realizable := by
  apply bitTransducer_realizable BinaryScan.increment true _ _ _ (by intros; rfl)
  intro sizes value
  let bits := EncodedDomain.ArrayEncoding.bits value
  have length : (BinaryScan.run BinaryScan.increment true bits).2.length = (MvPolynomial.eval sizes polynomial) := by
    simp [bits, EncodedDomain.ArrayEncoding.bits]
  have resultValue : Binary.value (BinaryScan.run BinaryScan.increment true bits).2 =
      (value.toNat + 1) % 2 ^ (MvPolynomial.eval sizes polynomial) := by
    rw [BinaryScan.increment_value]
    simp only [bits, EncodedDomain.ArrayEncoding.bits, List.length_ofFn, Binary.value_bits]
  have encoded := Binary.bits_value (BinaryScan.run BinaryScan.increment true bits).2 length
  rw [resultValue] at encoded
  have normalized : BitVec.ofNat (MvPolynomial.eval sizes polynomial)
      ((value.toNat + 1) % 2 ^ MvPolynomial.eval sizes polynomial) =
      BitVec.ofNat (MvPolynomial.eval sizes polynomial) (value.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp
  simpa only [normalized] using encoded.symm

/-- Allocate an exact polynomial number of zero bits, with no data input. -/
noncomputable def zeroBits (polynomial : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.bitVectors polynomial
  precondition _ _ := True
  compute _ _ := 0

theorem zeroBits_realizable (polynomial : MvPolynomial Parameter ℕ) : (zeroBits polynomial).Realizable := by
  let source : EncodedDomain Parameter := EncodedDomain.unaryOfLength polynomial
  let target := EncodedDomain.bitVectors polynomial
  have clearing := bitTransducer_realizable BinaryScan.clear () source target (fun _ _ => 0)
    (fun _ => rfl) (by
      intro sizes value
      change (BinaryScan.run BinaryScan.clear () _).2 =
        EncodedDomain.ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes polynomial))
      simp [BinaryScan.clear_run, EncodedDomain.ArrayEncoding.bits, BitVec.getLsbD,
        source, EncodedDomain.unaryOfLength])
  apply Realizable.withComputedWidth (zeroBits polynomial) polynomial
  exact clearing.withArguments (zeroBits polynomial |>.withUnaryWidth polynomial).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (fun _ => rfl)

/-- Initialize a polynomial-length array of polynomial-width zero words. -/
noncomputable def zeroBitArray (width length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := (EncodedDomain.bitVectors width).arrayOfLength length
  precondition _ _ := True
  compute sizes _ := fun _ => BitVec.ofNat (MvPolynomial.eval sizes width) 0

set_option backward.isDefEq.respectTransparency false in
theorem zeroBitArray_realizable (width length : MvPolynomial Parameter ℕ) :
    (zeroBitArray width length).Realizable := by
  let raw := EncodedDomain.bitVectors width
  exact (zeroBits_realizable (length * width)).withEncodedOutput (raw.arrayOfLength length)
    (zeroBitArray width length).compute (by intros; rfl) (by
      intro sizes arguments
      apply congrArg (fun bits => CallingConvention.buffer (Binary.word bits))
      change EncodedDomain.ArrayEncoding.bits ((raw.arrayOfLength length).encode sizes
        (fun _ => BitVec.ofNat (MvPolynomial.eval sizes width) 0)) =
        EncodedDomain.ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes (length * width)))
      rw [EncodedDomain.arrayOfLength_encode_bits, EncodedDomain.ArrayEncoding.bits_encode]
      simp [raw, EncodedDomain.ArrayEncoding.bits, BitVec.getLsbD, BitVec.toNat_ofNat])

end Polytime2.Computation
