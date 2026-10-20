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

import Polytime2.Arrays.PackingBits
import Polytime2.Encoding.BoundedUnary

/-! # Unary active counts from the generic packing algorithm

Packing the mask itself yields a prefix of true bits followed by zero padding.
No separate binary-to-unary machine or counting implementation is needed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.ArrayPacking

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem boolean_false_zero (sizes : Parameter → ℕ) : booleans.encode sizes false = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [booleans, fixed, ofCodec]
  decide

/-- Active Boolean values are true; the unused raw blocks are false bits. -/
theorem rawPack_booleans {length : ℕ} (sizes : Parameter → ℕ) (flags : Fin length → Bool)
    (position : Fin length) :
    rawPack (booleans.encode sizes) flags flags position =
      booleans.encode sizes (decide (position.val < count flags)) := by
  unfold rawPack
  split
  next within =>
    have selected : pack flags flags ⟨position.val, within⟩ = true := selection_active flags _
    simp only [selected, decide_eq_true within]
  next outside =>
    simp only [decide_eq_false outside]
    exact (boolean_false_zero sizes).symm

/-- A bounded unary word is the Boolean indicator of its initial segment. -/
theorem unary_ofFn {length count : ℕ} (fits : count ≤ length) :
    List.ofFn (fun index : Fin length => decide (index.val < count)) = BoundedUnary.bits length count := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using (BoundedUnary.bits_length fits).symm
  · intro position leftWithin rightWithin
    by_cases inside : position < count
    · simp [BoundedUnary.bits, List.getElem_append, inside]
    · simp [BoundedUnary.bits, List.getElem_append, inside]

theorem rawPack_boolean_bits (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    ArrayEncoding.bits (((bitVectors booleans.widthPolynomial).arrayOfLength length).encode sizes
      (rawPack (booleans.encode sizes) flags flags)) =
      BoundedUnary.bits (MvPolynomial.eval sizes length) (count flags) := by
  rw [arrayOfLength_encode_bits]
  have packed : rawPack (booleans.encode sizes) flags flags =
      fun position => booleans.encode sizes (decide (position.val < count flags)) :=
    funext (rawPack_booleans sizes flags)
  rw [packed]
  rw [ArrayEncoding.bits_encode]
  have canonical := Computation.FirstFalse.boolean_bits length sizes
    (fun position => decide (position.val < count flags))
  rw [arrayOfLength_encode_bits, ArrayEncoding.bits_encode] at canonical
  exact canonical.trans (unary_ofFn (count_le flags))

end Polytime2.ArrayPacking

namespace Polytime2.Computation

open EncodedDomain ArrayPacking CallingConvention

variable {Parameter : Type} [Fintype Parameter]

/-- A mask's exact active count, as proper bounded unary data. -/
noncomputable def packingCount (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := booleans.arrayOfLength length
  outputDomain := boundedUnary length
  precondition _ _ := True
  compute _ arguments := ⟨count (arguments.val ()), Nat.lt_succ_of_le (count_le (arguments.val ()))⟩

theorem packingCount_realizable (length : MvPolynomial Parameter ℕ) : (packingCount length).Realizable := by
  let computation := packingCount length
  let source := arrayPackRaw booleans length
  let values (choice : Bool) sizes
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (source.inputDomains choice).Carrier sizes :=
    match choice with | false => arguments.val () | true => arguments.val ()
  have producers choice : (Computation.mk computation.inputDomains (source.inputDomains choice)
      computation.precondition (values choice)).Realizable := by
    cases choice <;> exact Realizable.argument computation.inputDomains () computation.precondition
  have packed := (arrayPackRaw_realizable booleans length).onResults computation.inputDomains computation.precondition
    values (by intros; trivial) producers
  apply packed.withEncodedOutput computation.outputDomain computation.compute
  · intro sizes
    simp [computation, packingCount, Computation.onResults, boundedUnary, source, arrayPackRaw, arrayOfLength,
      booleans, fixed, ofCodec, show Nat.clog 2 2 = 1 by decide]
  · intro sizes arguments
    apply congrArg tape
    change ArrayEncoding.bits (BoundedUnary.encode _ _) =
      ArrayEncoding.bits (((bitVectors booleans.widthPolynomial).arrayOfLength length).encode sizes
        (rawPack (booleans.encode sizes) (arguments.val ()) (arguments.val ())))
    rw [BoundedUnary.encode_bits, rawPack_boolean_bits]
    rfl

end Polytime2.Computation
