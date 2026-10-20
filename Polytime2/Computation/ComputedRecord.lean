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

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

theorem namedRecord_unit_widthPolynomial (domain : EncodedDomain Parameter) :
    (namedRecord (fun _ : Unit => domain)).widthPolynomial = domain.widthPolynomial := by
  change (record (Fintype.card Unit) (fun _ => domain)).widthPolynomial = _
  rw [record_widthPolynomial]
  simp

theorem namedRecord_unit_bits (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (value : domain.Carrier sizes) :
    ArrayEncoding.bits ((namedRecord (fun _ : Unit => domain)).encode sizes (fun _ => value)) =
      ArrayEncoding.bits (domain.encode sizes value) := by
  change ArrayEncoding.bits ((record (Fintype.card Unit) (fun _ => domain)).encode sizes (fun _ => value)) = _
  rw [bits_record_encode]
  simp

end Polytime2.EncodedDomain

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
    change MvPolynomial.eval sizes ((computedSizeDomain bounds).widthPolynomial +
      SizeSubstitution.polynomial bounds (namedRecord (fun _ : Unit => payload)).widthPolynomial) = _
    rw [namedRecord_unit_widthPolynomial]
    rfl
  · intro sizes frame
    let assignment := computedSizeAssignment bounds sizes frame.1
    let singleton := namedRecord (fun _ : Unit => payload)
    let capacity := SizeSubstitution.polynomial bounds payload.widthPolynomial
    change ArrayEncoding.bits (((computedSizeDomain bounds).prod (bitVectors capacity)).encode sizes
      (frame.1, (payload.encode assignment frame.2).setWidth (MvPolynomial.eval sizes capacity))) =
      ArrayEncoding.bits (((computedSizeDomain bounds).prod
        (bitVectors (SizeSubstitution.polynomial bounds singleton.widthPolynomial))).encode sizes
        (frame.1, (singleton.encode assignment (fun _ => frame.2)).setWidth _))
    rw [bits_prod_encode, bits_prod_encode]
    have capacityEq : SizeSubstitution.polynomial bounds singleton.widthPolynomial = capacity := by
      simp only [singleton, namedRecord_unit_widthPolynomial, capacity]
    rw [capacityEq]
    exact congrArg (fun bits => ArrayEncoding.bits ((computedSizeDomain bounds).encode sizes frame.1) ++ bits)
      (ArrayEncoding.bits_setWidth_congr (namedRecord_unit_bits payload assignment frame.2).symm)

end Polytime2.Computation
