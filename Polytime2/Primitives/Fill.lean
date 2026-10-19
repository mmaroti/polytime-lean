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

import Polytime2.Primitives.SymbolScan
import Polytime2.Machine.CallingConventionRegions

/-! # Unary-controlled constant-symbol filling

The unary header determines the exact live output length. Physical tape
capacities may be larger, and every other tape is preserved.
-/

namespace Polytime2.Fill

open MultiTape CallingConvention
open Binary (Symbol word)

variable {TapeName : Type} [DecidableEq TapeName]

noncomputable def machine (source target : TapeName) (distinct : source ≠ target)
    (symbol : Symbol) : Machine (Alphabet TapeName) (SymbolScan.State Unit) :=
  MultiTape.wire (twoTapes source target distinct)
    (SymbolScan.machine BinaryScan.copy (fun _ => symbol))

/-- Fill exactly the header's length, with restored heads and arbitrary old
contents inside that live region. The empty region is supported. -/
theorem runs (source target : TapeName) (distinct : source ≠ target) (symbol : Symbol)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (writable : readOnly target = false)
    (capacity : ℕ) (fits : capacity ≤ width target)
    (initial : Tapes (Alphabet TapeName)) (header : initial source = unary capacity)
    (region : Region capacity 0 (initial target)) :
    Runs width readOnly (machine source target distinct symbol) (2 * capacity + 2)
      (.inl ()) (fun _ => 0) initial (.inr ((), true)) (fun _ => 0)
      (Function.update initial target (buffer (List.replicate capacity symbol))) := by
  obtain ⟨old, oldLength, oldTape⟩ := region.exists_buffer
  have trace := SymbolScan.buffer_runs BinaryScan.copy (fun _ => symbol) ()
    (List.replicate capacity true) old (by simpa using oldLength)
  simp only [SymbolScan.run, BinaryScan.copy_run, List.length_replicate,
    List.map_replicate] at trace
  have enlarged := trace.regions (fun name => width (twoTapes source target distinct name))
    (fun _ => 0) (by
      intro name writableName
      cases name
      · simp at writableName
      · constructor
        · omega
        · simpa using fits)
  simp only [add_zero] at enlarged
  apply enlarged.wire_of_eq (twoTapes source target distinct) width readOnly
  · intro name; rfl
  · intro name premise
    cases name
    · rfl
    · simp [writable] at premise
  · intro name
    cases name
    · simpa [unary, tape, buffer] using header
    · simpa using oldTape
  · intro name
    cases name
    · simpa [unary, tape, buffer, Function.update_of_ne distinct] using header
    · simp
  · intro name outside
    apply Function.update_of_ne
    intro equal
    exact outside ⟨true, by simpa only [twoTapes_true] using equal.symm⟩

end Polytime2.Fill
