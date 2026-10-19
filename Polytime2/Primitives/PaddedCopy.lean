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

import Polytime2.Primitives.Fill
import Polytime2.Primitives.UnaryHeader
import Polytime2.Primitives.PrefixCopy
import Polytime2.Encoding.Dependent

/-! # Padding a runtime-sized result to a caller capacity

Two unary headers give the caller capacity and the actual bit length. A fixed
machine fills the destination with binary zeros, then copies the live prefix.
-/

namespace Polytime2.PaddedCopy

open MultiTape CallingConvention EncodedDomain
open Binary (Symbol data word)

variable {TapeName : Type} [DecidableEq TapeName]

private def prefixTapes : Fin 3 ↪ Fin 4 :=
  ⟨(fun name => ⟨name.val + 1, by omega⟩), by
    intro first second equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    dsimp only at values
    omega⟩

@[simp] private theorem prefixTapes_zero : prefixTapes 0 = 1 := rfl
@[simp] private theorem prefixTapes_one : prefixTapes 1 = 2 := rfl
@[simp] private theorem prefixTapes_two : prefixTapes 2 = 3 := rfl

noncomputable def machine (wiring : Fin 4 ↪ TapeName) :
    Machine (Alphabet TapeName) (SymbolScan.State Unit ⊕ Fin 4) :=
  MultiTape.sequence
    (Fill.machine (wiring 0) (wiring 3) (wiring.injective.ne (by decide)) (data false))
    (PrefixCopy.machine (prefixTapes.trans wiring)) 0

/-- The final destination is precisely the zero-extended bit vector, with
blank surroundings. Both zero actual width and zero capacity are allowed. -/
theorem runs (wiring : Fin 4 ↪ TapeName) (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly (wiring 3) = false) {length capacity : ℕ}
    (bits : BitVec length) (bounded : length ≤ capacity) (fits : capacity ≤ width (wiring 3))
    (initial : Tapes (Alphabet TapeName))
    (capacityHeader : initial (wiring 0) = unary capacity)
    (lengthHeader : initial (wiring 1) = unary length)
    (source : initial (wiring 2) = buffer (word (ArrayEncoding.bits bits)))
    (region : Region capacity 0 (initial (wiring 3))) :
    Runs width readOnly (machine wiring) (2 * capacity + 3 * length + 6)
      (.inl (.inl ())) (fun _ => 0) initial (.inr 3) (fun _ => 0)
      (Function.update initial (wiring 3)
        (buffer (word (ArrayEncoding.bits (bits.setWidth capacity))))) := by
  have fillTrace := Fill.runs (wiring 0) (wiring 3) (wiring.injective.ne (by decide))
    (data false) width readOnly writable capacity fits initial capacityHeader
    region
  let middle := Function.update initial (wiring 3) (buffer (List.replicate capacity (data false)))
  have zeroSplit : List.replicate capacity (data false) =
      List.replicate length (data false) ++ List.replicate (capacity - length) (data false) := by
    rw [← List.replicate_add]
    congr 1
    omega
  have copyTrace := PrefixCopy.runs (prefixTapes.trans wiring) width readOnly (by simpa using writable)
    (word (ArrayEncoding.bits bits)) (List.replicate length (data false)) []
    (List.replicate (capacity - length) (data false)) (by simp [word, ArrayEncoding.bits])
    (by simpa [word, ArrayEncoding.bits] using bounded.trans fits) middle
    (by simpa [middle, word, ArrayEncoding.bits, Function.update_of_ne (wiring.injective.ne (show (1 : Fin 4) ≠ 3 by decide))] using lengthHeader)
    (by simpa [middle, Function.update_of_ne (wiring.injective.ne (show (2 : Fin 4) ≠ 3 by decide))] using source)
    (by simp [middle, zeroSplit])
  have combined := fillTrace.sequence (PrefixCopy.machine (prefixTapes.trans wiring)) 0
    (by intro symbols; rfl) copyTrace
  have padded : word (ArrayEncoding.bits (bits.setWidth capacity)) =
      word (ArrayEncoding.bits bits) ++ List.replicate (capacity - length) (data false) := by
    simp only [EncodedDomain.bits_setWidth bits bounded, word, List.map_append, List.map_replicate]
  rw [padded]
  convert combined using 1 <;>
    (simp [machine, middle, Function.update_idem, word, ArrayEncoding.bits]; try omega)

/-- Extract the exact payload from a padded argument into fresh storage. The
callee therefore starts with blanks immediately after its actual input. -/
theorem prefix_runs (wiring : Fin 3 ↪ TapeName) (width : TapeName → ℕ)
    (readOnly : TapeName → Bool) (writable : readOnly (wiring 2) = false)
    {length capacity : ℕ} (bits : BitVec length) (bounded : length ≤ capacity)
    (fits : length ≤ width (wiring 2)) (initial : Tapes (Alphabet TapeName))
    (lengthHeader : initial (wiring 0) = unary length)
    (source : initial (wiring 1) = buffer (word (ArrayEncoding.bits (bits.setWidth capacity))))
    (blank : initial (wiring 2) = buffer []) :
    Runs width readOnly (PrefixCopy.machine wiring) (3 * length + 3)
      0 (fun _ => 0) initial 3 (fun _ => 0)
      (Function.update initial (wiring 2) (buffer (word (ArrayEncoding.bits bits)))) := by
  have trace := PrefixCopy.runs wiring width readOnly writable
    (word (ArrayEncoding.bits bits)) (List.replicate length 0)
    (List.replicate (capacity - length) (data false)) []
    (by simp [word, ArrayEncoding.bits])
    (by simpa [word, ArrayEncoding.bits] using fits) initial
    (by simpa [word, ArrayEncoding.bits] using lengthHeader)
    (by simpa [bits_setWidth bits bounded, word, List.map_append, List.map_replicate] using source)
    (by simpa only [List.append_nil, ← UnaryHeader.buffer_append_blanks [] length, List.nil_append] using blank)
  simpa [word, ArrayEncoding.bits] using trace

end Polytime2.PaddedCopy
