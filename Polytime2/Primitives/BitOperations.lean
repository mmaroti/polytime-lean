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
import Polytime2.Encoding.Records

/-! # Certified bit-preserving maps and polynomial zero words -/

namespace Polytime2.Computation

open CallingConvention

variable {Parameter : Type} [Fintype Parameter]

/-- A total mathematical map implemented by copying the same canonical bits. -/
def encodingMap (source target : EncodedDomain Parameter)
    (compute : ∀ sizes, source.Carrier sizes → target.Carrier sizes) : Computation Parameter Unit :=
  unaryMap source target (fun _ _ => True) (fun sizes value => compute sizes value.val)

private theorem scan_realizable {Memory : Type} [Fintype Memory]
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
  scan_realizable BinaryScan.copy () source target compute sameWidth
    (by intro sizes value; simpa only [BinaryScan.copy_run] using sameBits sizes value)

/-- The canonical encoding itself is a polynomial-time computation. -/
theorem encode_realizable (domain : EncodedDomain Parameter) :
    (encodingMap domain (EncodedDomain.bitVectors domain.widthPolynomial) domain.encode).Realizable :=
  encodingMap_realizable _ _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- Allocate an exact polynomial number of zero bits, with no data input. -/
noncomputable def zeroBits (polynomial : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := EncodedDomain.bitVectors polynomial
  precondition _ _ := True
  compute _ _ := 0

theorem zeroBits_realizable (polynomial : MvPolynomial Parameter ℕ) : (zeroBits polynomial).Realizable := by
  let source : EncodedDomain Parameter := EncodedDomain.unaryOfLength polynomial
  let target := EncodedDomain.bitVectors polynomial
  have clearing := scan_realizable BinaryScan.clear () source target (fun _ _ => 0)
    (fun _ => rfl) (by
      intro sizes value
      change (BinaryScan.run BinaryScan.clear () _).2 =
        EncodedDomain.ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes polynomial))
      simp [BinaryScan.clear_run, EncodedDomain.ArrayEncoding.bits, BitVec.getLsbD,
        source, EncodedDomain.unaryOfLength])
  apply Realizable.withComputedWidth (zeroBits polynomial) polynomial
  exact clearing.withArguments (zeroBits polynomial |>.withUnaryWidth polynomial).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (fun _ => rfl)

end Polytime2.Computation
