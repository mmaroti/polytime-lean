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

import Polytime2.Computation.ComputedFrame

/-! # Singleton argument records in computed-size call frames -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Prepare the ordinary singleton argument record expected by a computed-size
call. This adapter copies identical canonical bits and adds no representation. -/
noncomputable def recordComputedFrame (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) : Computation Parameter Unit :=
  encodingMap (atComputedSizeDomain bounds payload)
    (atComputedSizeDomain bounds (namedRecord (fun _ : Unit => payload)))
    (fun _ frame => ⟨frame.1, fun _ => frame.2⟩)

theorem recordComputedFrame_realizable (bounds : NewParameter → MvPolynomial Parameter ℕ)
    (payload : EncodedDomain NewParameter) : (recordComputedFrame bounds payload).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp only [EncodedDomain.width, atComputedSizeDomain, boundedSigma_widthPolynomial,
      namedRecord_unit_widthPolynomial]
  · intro sizes frame
    change (Σ assignment : (computedSizeDomain bounds).Carrier sizes,
      payload.Carrier (computedSizeAssignment bounds sizes assignment)) at frame
    simp only [atComputedSizeDomain, boundedSigma_encode_bits]
    have widths := congrArg
      (fun polynomial => MvPolynomial.eval sizes (SizeSubstitution.polynomial bounds polynomial))
      (namedRecord_unit_widthPolynomial payload)
    exact congrArg (fun bits => ArrayEncoding.bits ((computedSizeDomain bounds).encode sizes frame.1) ++ bits)
      (ArrayEncoding.bits_setWidth_congr_of_eq
        (namedRecord_unit_bits payload _ frame.2).symm widths.symm)

end Polytime2.Computation
