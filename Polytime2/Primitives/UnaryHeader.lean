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
import Polytime2.Encoding.BoundedUnary
import Polytime2.Machine.CallingConventionRegions

/-! # Preparing private raw unary headers from bounded binary unary values

Public domains keep binary zero padding. Only this internal adapter turns the
unused suffix into blanks before a computed-size call.
-/

namespace Polytime2.UnaryHeader

open MultiTape CallingConvention
open Binary (Symbol data word)

/-- Blank padding does not change the mathematical tape. -/
theorem buffer_append_blanks (contents : List Symbol) (count : ℕ) :
    buffer (contents ++ List.replicate count 0) = buffer contents := by
  have same : Turing.ListBlank.mk (contents ++ List.replicate count (0 : Symbol)) =
      Turing.ListBlank.mk contents := Quotient.sound (Or.inr ⟨count, by simp⟩)
  simp only [buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, same]

/-- A fixed scanner turns the proper unary encoding into a private size tape. -/
def machine := SymbolScan.machine BinaryScan.copy (fun bit => if bit then data true else 0)

/-- Size zero and arbitrary old contents are handled by the same controller. -/
theorem runs (capacity : ℕ) (value : Fin (capacity + 1)) (old : List Symbol)
    (oldLength : old.length = capacity) :
    Runs (fun _ : Bool => capacity) (fun name => !name) machine (2 * capacity + 2)
      (.inl ()) (fun _ => 0)
      (Copy.frame [0] (word (BoundedUnary.bits capacity value.val) ++ [0]) [0] (old ++ [0]))
      (.inr ((), true)) (fun _ => 0)
      (fun name => if name then unary value.val else
        buffer (word (BoundedUnary.bits capacity value.val))) := by
  have length : (BoundedUnary.bits capacity value.val).length = capacity :=
    BoundedUnary.bits_length (by omega)
  have trace := SymbolScan.runs BinaryScan.copy (fun bit => if bit then data true else 0)
    () (BoundedUnary.bits capacity value.val) old (oldLength.trans length.symm)
  have mapped : (BoundedUnary.bits capacity value.val).map (fun bit => if bit then data true else 0) =
      List.replicate value.val (data true) ++ List.replicate (capacity - value.val) 0 := by
    simp [BoundedUnary.bits]
  simp only [SymbolScan.run, BinaryScan.copy_run, length, mapped] at trace
  have finalEqual : Copy.frame [0] (word (BoundedUnary.bits capacity value.val) ++ [0]) [0]
      (List.replicate value.val (data true) ++ List.replicate (capacity - value.val) 0 ++ [0]) =
      (fun name => if name then unary value.val else buffer (word (BoundedUnary.bits capacity value.val))) := by
    funext name
    cases name
    · exact buffer_padding _
    · change Turing.Tape.mk' _ _ = unary value.val
      rw [buffer_padding, buffer_append_blanks]
      simp [unary, tape, word, buffer]
  rw [finalEqual] at trace
  exact trace

/-- Normalize inside a larger private capacity without touching any other tape. -/
theorem runs_at {TapeName : Type} [DecidableEq TapeName]
    (wiring : Bool ↪ TapeName) (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly (wiring true) = false) (capacity : ℕ) (value : Fin (capacity + 1))
    (fits : capacity ≤ width (wiring true)) (initial : Tapes (Alphabet TapeName))
    (source : initial (wiring false) = buffer (word (BoundedUnary.bits capacity value.val)))
    (target : Region capacity 0 (initial (wiring true))) :
    Runs width readOnly (MultiTape.wire wiring machine) (2 * capacity + 2)
      (.inl ()) (fun _ => 0) initial (.inr ((), true)) (fun _ => 0)
      (Function.update initial (wiring true) (unary value.val)) := by
  obtain ⟨old, oldLength, oldTape⟩ := target.exists_buffer
  have trace := runs capacity value old oldLength
  have frameEqual : Copy.frame [0] (word (BoundedUnary.bits capacity value.val) ++ [0]) [0] (old ++ [0]) =
      (fun name => if name then buffer old else buffer (word (BoundedUnary.bits capacity value.val))) := by
    funext name
    cases name <;> exact buffer_padding _
  rw [frameEqual] at trace
  have enlarged := trace.regions (fun name => width (wiring name)) (fun _ => 0) (by
    intro name writableLocal
    cases name
    · contradiction
    · constructor
      · omega
      · simp only [zero_add]
        exact_mod_cast fits)
  simp only [add_zero] at enlarged
  apply enlarged.wire_of_eq wiring width readOnly
  · intro name; rfl
  · intro name premise
    cases name
    · rfl
    · simp [writable] at premise
  · intro name
    cases name
    · simpa using source
    · simpa using oldTape
  · intro name
    cases name
    · rw [Function.update_of_ne (wiring.injective.ne (by decide))]
      simpa using source
    · simp
  · intro name outside
    apply Function.update_of_ne
    intro equal
    exact outside ⟨true, equal.symm⟩

end Polytime2.UnaryHeader
