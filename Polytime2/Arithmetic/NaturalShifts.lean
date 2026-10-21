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

import Polytime2.Arithmetic.NaturalArithmetic

/-! # Natural left shifts by a mathematical size

An input of width `w` shifted left by `s` bits has exact output width `w+s`.
The shift count is a mathematical size polynomial, so the runtime includes
writing the requested output. Existing zero-word and product constructors
prepend the low zero bits; no numerical iteration or new controller is used.
-/

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def naturalShiftLeft (width amount : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth (width + amount))
    (fun sizes value => ⟨value.val * 2 ^ MvPolynomial.eval sizes amount, by
      exact lt_of_lt_of_eq (Nat.mul_lt_mul_of_pos_right value.isLt (by positivity))
        (by change 2 ^ MvPolynomial.eval sizes width * 2 ^ MvPolynomial.eval sizes amount =
          2 ^ MvPolynomial.eval sizes (width + amount); rw [map_add, pow_add])⟩)

theorem naturalShiftLeft_realizable (width amount : MvPolynomial Parameter ℕ) :
    (naturalShiftLeft width amount).Realizable := by
  let source := binaryNaturalsOfWidth width
  let zeros := bitVectors amount
  let inputs : Unit → EncodedDomain Parameter := fun _ => source
  have zeroReady := (zeroBits_realizable amount).withArguments inputs
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)
  have pair := Realizable.pairOutputs inputs zeros source (fun _ _ => True)
    (fun _ _ => 0) (fun _ arguments => arguments.val ()) zeroReady (copy_realizable source)
  have shifted := pair.reinterpretOutput (binaryNaturalsOfWidth (width + amount))
    (fun sizes parts => ((BitVec.ofFin parts.2 ++ parts.1).cast
      (by simp only [map_add])).toFin)
    (by intros; simp [source, zeros, EncodedDomain.width, Nat.add_comm]) (by
      intro sizes parts
      erw [binaryNaturalsOfWidth_encode_bits (width + amount) sizes _]
      rw [bits_prod_encode]
      simp only [BitVec.ofFin_toFin, ArrayEncoding.bits_cast, ArrayEncoding.bits_append]
      erw [binaryNaturalsOfWidth_encode_bits width sizes _])
  exact shifted.withSpecification (fun _ _ => True) (naturalShiftLeft width amount).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply Fin.ext
      change (BitVec.cast (show MvPolynomial.eval sizes width + MvPolynomial.eval sizes amount =
          MvPolynomial.eval sizes (width + amount) by rw [map_add]) (BitVec.ofFin (arguments ()) ++
        (0 : BitVec (MvPolynomial.eval sizes amount)))).toNat =
          (arguments ()).val * 2 ^ MvPolynomial.eval sizes amount
      rw [BitVec.toNat_cast, BitVec.toNat_append]
      change (arguments ()).val <<< MvPolynomial.eval sizes amount ||| 0 = _
      simp only [Nat.or_zero, Nat.shiftLeft_eq])

end Polytime2.Computation.Realizable.Internal
