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
import Polytime2.Primitives.BitOperations

/-! # Private extra-bit arithmetic workspace

Shared preparation and extraction for binary arithmetic controllers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

namespace Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Natural magnitudes widen by a derived polynomial number of zero bits. -/
noncomputable def naturalWiden (width extra : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (EncodedDomain.binaryNaturalsOfWidth width)
    (EncodedDomain.binaryNaturalsOfWidth (width + extra)) (fun sizes value =>
      ⟨value.val, value.isLt.trans_le (pow_le_pow_right₀ (by decide)
        (by simp only [map_add]; omega))⟩)

theorem naturalWiden_realizable (width extra : MvPolynomial Parameter ℕ) :
    (naturalWiden width extra).Realizable := by
  apply zeroExtendEncoding_realizable (EncodedDomain.binaryNaturalsOfWidth width)
    (EncodedDomain.binaryNaturalsOfWidth (width + extra)) extra
  · intro sizes
    simp
  · intro sizes value
    simp only [EncodedDomain.binaryNaturalsOfWidth_encode_bits]
    have widened := EncodedDomain.bits_ofFin_widen value
      (⟨value.val, value.isLt.trans_le (pow_le_pow_right₀ (by decide)
        (by simp only [map_add]; omega))⟩ : Fin (2 ^ MvPolynomial.eval sizes (width + extra))) rfl
      (by simp only [map_add]; omega)
    simpa only [map_add, Nat.add_sub_cancel_left] using widened

noncomputable def extraBitSizes : Unit → MvPolynomial Unit ℕ :=
  fun _ => MvPolynomial.X () + 1

theorem extraBitSizes_eval (sizes : Unit → ℕ) :
    SizeSubstitution.assignment extraBitSizes sizes () = sizes () + 1 := by
  simp [SizeSubstitution.assignment, extraBitSizes]

noncomputable def extraBitDomain : EncodedDomain Unit :=
  (EncodedDomain.binaryNaturals ()).substitute extraBitSizes

def extraBitWiden (sizes : Unit → ℕ) (value : Fin (2 ^ sizes ())) :
    extraBitDomain.Carrier sizes :=
  ⟨value.val, by
    rw [extraBitSizes_eval]
    exact value.isLt.trans_le (pow_le_pow_right₀ (by decide) (by omega))⟩

theorem extraBitWiden_realizable :
    (encodingMap (EncodedDomain.binaryNaturals ()) extraBitDomain extraBitWiden).Realizable := by
  refine zeroExtendEncoding_realizable (EncodedDomain.binaryNaturals ()) extraBitDomain 1 extraBitWiden ?_ ?_
  · intro sizes
    simpa only [extraBitDomain, EncodedDomain.substitute_width, EncodedDomain.binaryNaturals_width, map_one]
      using extraBitSizes_eval sizes
  · intro sizes value
    simp only [extraBitDomain, EncodedDomain.substitute, EncodedDomain.binaryNaturals,
      EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast]
    have widened := EncodedDomain.bits_ofFin_widen value (extraBitWiden sizes value) rfl
      (by rw [extraBitSizes_eval]; omega)
    simpa [extraBitSizes_eval] using widened

noncomputable def extraBitNarrow : Computation Unit Unit :=
  encodingMap extraBitDomain (EncodedDomain.binaryNaturals ())
    (fun sizes value => ((BitVec.ofFin value).setWidth (sizes ())).toFin)

theorem extraBitNarrow_realizable : extraBitNarrow.Realizable := by
  apply Realizable.Internal.fieldProjection extraBitDomain (EncodedDomain.binaryNaturals ()) 0
    (fun _ _ => True) (fun sizes value => ((BitVec.ofFin value.val).setWidth (sizes ())).toFin)
  intro sizes value
  refine ⟨[], (EncodedDomain.ArrayEncoding.bits (BitVec.ofFin value.val)).drop (sizes ()), ?_, by simp⟩
  simp only [extraBitDomain, EncodedDomain.substitute, EncodedDomain.binaryNaturals,
    EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast, BitVec.ofFin_toFin, List.nil_append]
  rw [EncodedDomain.bits_setWidth_take _ (by rw [extraBitSizes_eval]; omega)]
  simpa only [EncodedDomain.ArrayEncoding.bits_cast] using
    (List.take_append_drop (sizes ()) (EncodedDomain.ArrayEncoding.bits (BitVec.ofFin value.val))).symm

end Realizable.Internal

end Polytime2.Computation
