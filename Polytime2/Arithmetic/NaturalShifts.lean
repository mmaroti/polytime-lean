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

open EncodedDomain CallingConvention

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
  exact pair.withEncodedOutput (binaryNaturalsOfWidth (width + amount)) (naturalShiftLeft width amount).compute
    (by intros; simp [source, zeros, EncodedDomain.width, Nat.add_comm]) (by
      intro sizes arguments
      apply congrArg tape
      change ArrayEncoding.bits ((binaryNaturalsOfWidth (width + amount)).encode sizes
          ((naturalShiftLeft width amount).compute sizes arguments)) =
        ArrayEncoding.bits ((zeros.prod source).encode sizes (0, arguments.val ()))
      rw [bits_prod_encode, binaryNaturalsOfWidth_encode_bits]
      let words := ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes amount)) ++
        ArrayEncoding.bits (BitVec.ofFin (arguments.val ()))
      have packedLength : words.length = MvPolynomial.eval sizes (width + amount) := by
        simp [words, ArrayEncoding.bits, Nat.add_comm]
      have packedValue : Binary.value words = (arguments.val ()).val * 2 ^ MvPolynomial.eval sizes amount := by
        have zeroValue : Binary.value (ArrayEncoding.bits (0 : BitVec (MvPolynomial.eval sizes amount))) = 0 :=
          Binary.value_bits (0 : BitVec (MvPolynomial.eval sizes amount))
        have payloadValue : Binary.value (ArrayEncoding.bits (BitVec.ofFin (arguments.val ()))) =
            (arguments.val ()).val := Binary.value_bits (BitVec.ofFin (arguments.val ()))
        dsimp only [words]
        rw [Binary.value_append, zeroValue, payloadValue]
        simp only [ArrayEncoding.bits, List.length_ofFn, Nat.zero_add, Nat.mul_comm]
      have canonical := Binary.bits_value words packedLength
      rw [packedValue] at canonical
      change ArrayEncoding.bits ((binaryNaturalsOfWidth (width + amount)).encode sizes
        ⟨(arguments.val ()).val * 2 ^ MvPolynomial.eval sizes amount, _⟩) = words
      erw [binaryNaturalsOfWidth_encode_bits (width + amount) sizes _]
      simpa only [ArrayEncoding.bits, BitVec.ofFin_eq_ofNat] using canonical)

end Polytime2.Computation.Realizable.Internal
