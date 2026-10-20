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

import Polytime2.Arrays.PackingCount
import Polytime2.Encoding.BoundedArray

/-! # Identifying the private packed bits with an exact-length array codec -/

namespace Polytime2.ArrayPacking

open EncodedDomain

/-- The packed capacity blocks are precisely the zero-extended encoding of the
exact mathematical packed array, including zero lengths and zero-width blocks. -/
theorem rawPack_encode_bits {Element : Type} {width length : ℕ}
    (encode : Element → BitVec width) (flags : Fin length → Bool) (values : Fin length → Element) :
    ArrayEncoding.bits (ArrayEncoding.encode id length (rawPack encode flags values)) =
      ArrayEncoding.bits ((ArrayEncoding.encode encode (count flags) (pack flags values)).setWidth (length * width)) := by
  rw [bits_setWidth _ (Nat.mul_le_mul_right width (count_le flags)), ArrayEncoding.bits_encode]
  change (List.ofFn (fun index => ArrayEncoding.bits (rawPack encode flags values index))).flatten = _
  rw [List.ofFn_comp' (rawPack encode flags values) ArrayEncoding.bits, rawPack_ofFn, List.map_append, List.map_replicate, List.flatten_append]
  have zero : ArrayEncoding.bits (0 : BitVec width) = List.replicate width false := by
    simp [ArrayEncoding.bits, BitVec.getLsbD, BitVec.toNat_zero]
  rw [zero, List.flatten_replicate_replicate, Nat.sub_mul, ArrayEncoding.bits_encode, List.map_ofFn]
  rfl

end Polytime2.ArrayPacking

namespace Polytime2.Computation

open EncodedDomain ArrayPacking CallingConvention

variable {Parameter : Type} [Fintype Parameter]

/-- Stable array packing exposes the active count and exactly its retained
mathematical values. All capacity padding and counters are private. -/
noncomputable def arrayPack (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains choice := if choice then element.arrayOfLength length else booleans.arrayOfLength length
  outputDomain := boundedArray element length
  precondition _ _ := True
  compute _ arguments := ⟨⟨count (arguments.val false), Nat.lt_succ_of_le (count_le (arguments.val false))⟩,
    pack (arguments.val false) (arguments.val true)⟩

theorem arrayPack_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayPack element length).Realizable := by
  let computation := arrayPack element length
  let countResult sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (boundedUnary length).Carrier sizes :=
    ⟨count (arguments.val false), Nat.lt_succ_of_le (count_le (arguments.val false))⟩
  have counted : (Computation.mk computation.inputDomains (boundedUnary length) computation.precondition countResult).Realizable :=
    (packingCount_realizable length).onResults computation.inputDomains computation.precondition
      (fun _ _ arguments => arguments.val false) (by intros; trivial)
      (fun _ => Realizable.argument computation.inputDomains false computation.precondition)
  have packed := arrayPackRaw_realizable element length
  have pair := Realizable.pairOutputs computation.inputDomains (boundedUnary length)
    ((bitVectors element.widthPolynomial).arrayOfLength length) computation.precondition countResult
    (arrayPackRaw element length).compute counted packed
  apply pair.withEncodedOutput computation.outputDomain computation.compute (fun _ => rfl)
  intro sizes arguments
  apply congrArg tape
  change ArrayEncoding.bits (((boundedUnary length).prod
    (bitVectors (length * element.widthPolynomial))).encode sizes
      (countResult sizes arguments,
        (ArrayEncoding.encode (element.encode sizes) _ (pack (arguments.val false) (arguments.val true))).setWidth _)) = _
  rw [bits_prod_encode, bits_prod_encode, arrayOfLength_encode_bits]
  apply congrArg (fun bits => ArrayEncoding.bits ((boundedUnary length).encode sizes (countResult sizes arguments)) ++ bits)
  change ArrayEncoding.bits ((ArrayEncoding.encode (element.encode sizes) _
    (pack (arguments.val false) (arguments.val true))).setWidth
      (MvPolynomial.eval sizes (length * element.widthPolynomial))) =
    ArrayEncoding.bits (ArrayEncoding.encode id (MvPolynomial.eval sizes length)
      (rawPack (element.encode sizes) (arguments.val false) (arguments.val true)))
  rw [map_mul]
  exact (rawPack_encode_bits (element.encode sizes) (arguments.val false) (arguments.val true)).symm

/-- A bit-preserving view used by count and payload projections. -/
noncomputable def boundedArrayStorage (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := boundedArray element length
  outputDomain := (boundedUnary length).prod (bitVectors (length * element.widthPolynomial))
  precondition _ _ := True
  compute sizes arguments := ((arguments.val ()).1,
    (ArrayEncoding.encode (element.encode sizes) (arguments.val ()).1.val (arguments.val ()).2).setWidth
      (MvPolynomial.eval sizes (length * element.widthPolynomial)))

theorem boundedArrayStorage_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (boundedArrayStorage element length).Realizable :=
  (copy_realizable (boundedArray element length)).withEncodedOutput
    (boundedArrayStorage element length).outputDomain (boundedArrayStorage element length).compute
    (fun _ => rfl) (by intros; rfl)

noncomputable def boundedArrayCount (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (boundedArrayStorage element length).followedBy
    (pairProjection (boundedUnary length) (bitVectors (length * element.widthPolynomial)) false)
    rfl (by intros; trivial)

theorem boundedArrayCount_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (boundedArrayCount element length).Realizable :=
  (boundedArrayStorage_realizable element length).followedBy
    (pairProjection_realizable (boundedUnary length) (bitVectors (length * element.widthPolynomial)) false)
    rfl (by intros; trivial)

noncomputable def boundedArrayPayload (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (boundedArrayStorage element length).followedBy
    (pairProjection (boundedUnary length) (bitVectors (length * element.widthPolynomial)) true)
    rfl (by intros; trivial)

theorem boundedArrayPayload_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (boundedArrayPayload element length).Realizable :=
  (boundedArrayStorage_realizable element length).followedBy
    (pairProjection_realizable (boundedUnary length) (bitVectors (length * element.widthPolynomial)) true)
    rfl (by intros; trivial)

/-- Retain one shared source-to-dense position table alongside the exact packed
array. Related fields and dependency references can reuse this table. -/
noncomputable def arrayPackWithPositions (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    Computation Parameter Bool where
  inputDomains := (arrayPack element length).inputDomains
  outputDomain := (boundedArray element length).prod ((bitVectors (length + 1)).arrayOfLength length)
  precondition _ _ := True
  compute sizes arguments := ((arrayPack element length).compute sizes arguments,
    (prefixCounts length).compute sizes ⟨(fun _ => arguments.val false), trivial⟩)

theorem arrayPackWithPositions_realizable (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayPackWithPositions element length).Realizable := by
  let computation := arrayPackWithPositions element length
  have positions := (prefixCounts_realizable length).onResults computation.inputDomains computation.precondition
    (fun _ _ arguments => arguments.val false) (by intros; trivial)
    (fun _ => Realizable.argument computation.inputDomains false computation.precondition)
  exact Realizable.pairOutputs computation.inputDomains (boundedArray element length)
    ((bitVectors (length + 1)).arrayOfLength length) computation.precondition
    (arrayPack element length).compute
    (fun sizes arguments => (prefixCounts length).compute sizes ⟨(fun _ => arguments.val false), trivial⟩)
    (arrayPack_realizable element length) positions

/-- Every active coordinate's stored position is its exact dense output index. -/
theorem arrayPackWithPositions_rank (element : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (arrayPackWithPositions element length).Arguments sizes)
    (index : {index : Fin (MvPolynomial.eval sizes length) // arguments false index = true}) :
    ((((arrayPackWithPositions element length).compute sizes ⟨arguments, trivial⟩).2) index.val).toNat =
      (rank (arguments false) index).val := prefixCounts_packing_rank length sizes (arguments false) index

end Polytime2.Computation
