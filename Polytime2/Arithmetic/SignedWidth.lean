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

import Polytime2.Arithmetic.SignedConstruction

/-! # Private widening and exact narrowing of signed integer words

Widening preserves the ordinary integer and appends only high zero magnitude
bits. Narrowing also preserves the integer and requires that its magnitude fit
the target width. Applications derive this bound internally; neither operation
introduces modular signed arithmetic or an invalid output alternative.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerWiden (width extra : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryIntegers width) (binaryIntegers (width + extra)) (fun sizes value =>
    ⟨value.val, value.property.trans_le (pow_le_pow_right₀ (by decide)
      (by simp only [map_add]; omega))⟩)

theorem integerWiden_realizable (width extra : MvPolynomial Parameter ℕ) :
    (integerWiden width extra).Realizable := by
  apply zeroExtendEncoding_realizable (binaryIntegers width) (binaryIntegers (width + extra)) extra
  · intro sizes
    simp [Nat.add_assoc]
  · intro sizes value
    erw [binaryIntegers_encode_bits (width + extra) sizes _, binaryIntegers_encode_bits width sizes value]
    erw [binaryNaturalsOfWidth_encode_bits (width + extra) sizes _,
      binaryNaturalsOfWidth_encode_bits width sizes _]
    let result := (integerWiden width extra).compute sizes ⟨(fun _ => value), trivial⟩
    have widened := bits_ofFin_widen
      (⟨value.val.natAbs, value.property⟩ : Fin (2 ^ MvPolynomial.eval sizes width))
      (⟨value.val.natAbs, result.property⟩ : Fin (2 ^ MvPolynomial.eval sizes (width + extra)))
      rfl (by simp only [map_add]; omega)
    simpa only [map_add, Nat.add_sub_cancel_left, List.append_assoc] using
      congrArg (fun payload => ArrayEncoding.bits (booleans.encode sizes (SignedEncoding.negative value.val)) ++ payload) widened

noncomputable def integerNarrowAtWidths (sourceWidth width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (binaryIntegers sourceWidth) (binaryIntegers width)
    (fun sizes value => value.val.natAbs < 2 ^ MvPolynomial.eval sizes width)
    (fun _ value => ⟨value.val.val, value.property⟩)

theorem integerNarrowAtWidths_realizable (sourceWidth width : MvPolynomial Parameter ℕ)
    (fits : ∀ sizes, MvPolynomial.eval sizes width ≤ MvPolynomial.eval sizes sourceWidth) :
    (integerNarrowAtWidths sourceWidth width).Realizable := by
  apply fieldProjection (binaryIntegers sourceWidth) (binaryIntegers width) 0
  intro sizes value
  let source := ArrayEncoding.bits ((binaryIntegers sourceWidth).encode sizes value.val)
  let target := ArrayEncoding.bits ((binaryIntegers width).encode sizes ⟨value.val.val, value.property⟩)
  have initialBits : target = source.take ((binaryIntegers width).width sizes) := by
    dsimp only [target, source]
    erw [binaryIntegers_encode_bits width sizes _, binaryIntegers_encode_bits sourceWidth sizes value.val]
    erw [binaryNaturalsOfWidth_encode_bits width sizes _,
      binaryNaturalsOfWidth_encode_bits sourceWidth sizes _]
    simp only [binaryIntegers_width]
    let sign := ArrayEncoding.bits (booleans.encode sizes (SignedEncoding.negative value.val.val))
    have signLength : sign.length = 1 := by
      simp only [sign, ArrayEncoding.bits, List.length_ofFn]
      exact booleans_width sizes
    have narrowed := bits_ofFin_narrow
      (⟨value.val.val.natAbs, value.val.property⟩ : Fin (2 ^ MvPolynomial.eval sizes sourceWidth))
      (⟨value.val.val.natAbs, value.property⟩ : Fin (2 ^ MvPolynomial.eval sizes width))
      rfl (fits sizes)
    rw [List.take_append, List.take_of_length_le (by rw [signLength]; omega),
      show 1 + MvPolynomial.eval sizes width - sign.length = MvPolynomial.eval sizes width by rw [signLength]; omega,
      ← narrowed]
  refine ⟨[], source.drop ((binaryIntegers width).width sizes), ?_, by simp⟩
  change source = [] ++ target ++ source.drop ((binaryIntegers width).width sizes)
  rw [initialBits]
  simpa only [List.nil_append] using (List.take_append_drop ((binaryIntegers width).width sizes) source).symm

/-- Narrow a privately widened integer after proving its original bound. -/
noncomputable abbrev integerNarrow (width extra : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  integerNarrowAtWidths (width + extra) width

theorem integerNarrow_realizable (width extra : MvPolynomial Parameter ℕ) :
    (integerNarrow width extra).Realizable :=
  integerNarrowAtWidths_realizable (width + extra) width (by intro sizes; simp only [map_add]; omega)

end Polytime2.Computation.Realizable.Internal
