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

import Polytime2.Encoding.BinaryEncoding
import Polytime2.Encoding.EncodedArray

/-! # Bounded unary values with proper binary encodings

A value at most the polynomial capacity is represented by that many ones,
followed by zero padding. Blank remains outside the encoded data region.
-/

namespace Polytime2.BoundedUnary

/-- The canonical word has exactly the capacity, including for value zero. -/
def bits (capacity value : ℕ) : List Bool :=
  List.replicate value true ++ List.replicate (capacity - value) false

@[simp] theorem bits_length {capacity value : ℕ} (bounded : value ≤ capacity) :
    (bits capacity value).length = capacity := by
  simp [bits]; omega

@[simp] theorem bits_count (capacity value : ℕ) : (bits capacity value).count true = value := by
  simp [bits, List.count_replicate]

/-- The bit vector itself carries no delimiter or blank symbol. -/
def encode (capacity : ℕ) (value : Fin (capacity + 1)) : BitVec capacity :=
  BitVec.ofNat capacity (Binary.value (bits capacity value.val))

@[simp] theorem encode_bits (capacity : ℕ) (value : Fin (capacity + 1)) :
    EncodedDomain.ArrayEncoding.bits (encode capacity value) = bits capacity value.val :=
  Binary.bits_value _ (bits_length (by omega))

def decode (capacity : ℕ) (word : BitVec capacity) : Option (Fin (capacity + 1)) :=
  let count := (EncodedDomain.ArrayEncoding.bits word).count true
  if bounded : count ≤ capacity then
    let value : Fin (capacity + 1) := ⟨count, by omega⟩
    if encode capacity value = word then some value else none
  else none

@[simp] theorem decode_encode (capacity : ℕ) (value : Fin (capacity + 1)) :
    decode capacity (encode capacity value) = some value := by
  have bounded : value.val ≤ capacity := by omega
  simp only [decode, encode_bits, bits_count, dite_eq_left bounded]
  simp

theorem encode_decode (capacity : ℕ) (word : BitVec capacity) (value : Fin (capacity + 1))
    (accepted : decode capacity word = some value) : encode capacity value = word := by
  dsimp only [decode] at accepted
  split at accepted
  · split at accepted
    · cases Option.some.inj accepted
      assumption
    · contradiction
  · contradiction

end Polytime2.BoundedUnary

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Polynomially bounded runtime sizes, in unary with binary zero padding. -/
noncomputable def boundedUnary (capacity : MvPolynomial Parameter ℕ) : EncodedDomain Parameter where
  Carrier sizes := Fin (MvPolynomial.eval sizes capacity + 1)
  widthPolynomial := capacity
  encode sizes := BoundedUnary.encode (MvPolynomial.eval sizes capacity)
  decode sizes := BoundedUnary.decode (MvPolynomial.eval sizes capacity)
  decode_encode sizes := BoundedUnary.decode_encode (MvPolynomial.eval sizes capacity)
  encode_decode sizes := BoundedUnary.encode_decode (MvPolynomial.eval sizes capacity)

/-- A genuine coordinate in unary; the all-ones search sentinel is rejected. -/
noncomputable def unaryIndex (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter where
  Carrier sizes := Fin (MvPolynomial.eval sizes length)
  widthPolynomial := length
  encode sizes index := BoundedUnary.encode _ index.castSucc
  decode sizes bits := do
    let value ← BoundedUnary.decode (MvPolynomial.eval sizes length) bits
    if within : value.val < MvPolynomial.eval sizes length then some ⟨value.val, within⟩ else none
  decode_encode sizes index := by simp [BoundedUnary.decode_encode, index.isLt]
  encode_decode sizes bits index accepted := by
    cases decoded : BoundedUnary.decode (MvPolynomial.eval sizes length) bits with
    | none => simp [decoded] at accepted
    | some value =>
      simp only [decoded] at accepted
      dsimp only [Bind.bind, Option.bind] at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact BoundedUnary.encode_decode _ bits value decoded
      · simp at accepted

end Polytime2.EncodedDomain
