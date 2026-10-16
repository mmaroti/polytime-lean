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

import Polytime2.StandardArrayUpdate

/-! # Encoded array-update traces for composition with address arithmetic -/

namespace Polytime2.StandardArrayUpdate

open MultiTape CallingConvention
open Binary (Symbol data word value)

-- parameterLevel: names of the immutable unary size arguments.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

theorem encoded_runsOfLength (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : List Bool) (within : value index < MvPolynomial.eval sizes length)
    (array : (element.arrayOfLength length).Carrier sizes) (replacement : element.Carrier sizes)
    (oldOutput oldCounter scratch : List Symbol)
    (outputLength : oldOutput.length = (element.arrayOfLength length).width sizes)
    (counterLength : oldCounter.length = index.length) (scratchLength : scratch.length = index.length)
    (flag : Symbol) : ∃ ticks,
      ticks ≤ MvPolynomial.eval sizes length * (6 * index.length + 4 * element.width sizes + 11) +
        6 * index.length + 2 * element.width sizes + 18 ∧
      Runs (widths (element.width sizes) index.length ((element.arrayOfLength length).width sizes))
        readOnly (machine (element.width sizes)) ticks (entry (element.width sizes)) (fun _ => 0)
        (initialFrame index
          (EncodedDomain.ArrayEncoding.bits ((element.arrayOfLength length).encode sizes array))
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          oldOutput oldCounter scratch flag)
        (exit (element.width sizes)) (fun _ => 0)
        (frame index (encoded (element.arrayOfLength length) sizes array)
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          (encoded (element.arrayOfLength length) sizes (Function.update array ⟨value index, within⟩ replacement))
          (List.replicate index.length false) (word (List.replicate index.length false)) (data false)) := by
  obtain ⟨before, after, decomposition, prefixLength, updatedDecomposition⟩ :=
    EncodedDomain.ArrayEncoding.split_encode_update (element.encode sizes)
      (MvPolynomial.eval sizes length) array ⟨value index, within⟩ replacement
  let block := EncodedDomain.ArrayEncoding.bits (element.encode sizes (array ⟨value index, within⟩))
  let replacementBits := EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)
  have wholeLength : (before ++ block ++ after).length = (element.arrayOfLength length).width sizes := by
    rw [← decomposition]
    simp [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits]
  obtain ⟨ticks, cost, trace⟩ := runs (element.width sizes) index before block after replacementBits
    prefixLength List.length_ofFn List.length_ofFn oldOutput oldCounter scratch
    (outputLength.trans wholeLength.symm) counterLength scratchLength flag
  refine ⟨ticks, cost.trans ?_, ?_⟩
  · have indexBound : value index ≤ MvPolynomial.eval sizes length := Nat.le_of_lt within
    have bound := Nat.mul_le_mul_right (6 * index.length + 2 * element.width sizes + 11) indexBound
    have widthEq : (before ++ block ++ after).length = MvPolynomial.eval sizes length * element.width sizes :=
      by simpa [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec] using wholeLength
    nlinarith [prefixLength]
  · rw [wholeLength] at trace
    have arrayBitsEq : EncodedDomain.ArrayEncoding.bits
        ((element.arrayOfLength length).encode sizes array) = before ++ block ++ after := by
      simpa only [EncodedDomain.arrayOfLength_encode_bits] using decomposition
    have updatedBitsEq : EncodedDomain.ArrayEncoding.bits
        ((element.arrayOfLength length).encode sizes (Function.update array ⟨value index, within⟩ replacement)) =
        before ++ replacementBits ++ after := by
      simpa only [EncodedDomain.arrayOfLength, EncodedDomain.ofCodec,
        EncodedDomain.ArrayEncoding.bits_cast] using updatedDecomposition
    have sourceEq : buffer (word (before ++ block ++ after)) =
        encoded (element.arrayOfLength length) sizes array :=
      congrArg (fun bits => buffer (word bits)) arrayBitsEq.symm
    have outputEq : buffer (word (before ++ replacementBits ++ after)) =
        encoded (element.arrayOfLength length) sizes (Function.update array ⟨value index, within⟩ replacement) :=
      congrArg (fun bits => buffer (word bits)) updatedBitsEq.symm
    rw [sourceEq, outputEq, ← arrayBitsEq] at trace
    exact trace

end Polytime2.StandardArrayUpdate
