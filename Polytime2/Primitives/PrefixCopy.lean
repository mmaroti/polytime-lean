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

import Polytime2.Primitives.UnaryCopy
import Polytime2.Machine.CallingConventionRegions

/-! # Unary-controlled prefix copying inside polynomial capacities

Only the selected prefix is overwritten. The remaining source and destination
contents are preserved, so the same rule handles truncation and zero padding.
-/

namespace Polytime2.UnaryCopy

open MultiTape CallingConvention
open Binary (Symbol data word)

/-- Runtime-width copying stated on complete buffers with preserved suffixes. -/
theorem buffer_runs (payload old sourceAfter targetAfter : List Symbol)
    (sameLength : old.length = payload.length) (width : Fin 3 → ℕ)
    (fits : payload.length ≤ width 2) :
    Runs width (fun name => decide (name ≠ 2)) machine (3 * payload.length + 3)
      0 (fun _ => 0)
      (fun name => if name = 0 then unary payload.length else if name = 1 then
        buffer (payload ++ sourceAfter) else buffer (old ++ targetAfter))
      3 (fun _ => 0)
      (fun name => if name = 0 then unary payload.length else if name = 1 then
        buffer (payload ++ sourceAfter) else buffer (payload ++ targetAfter)) := by
  have frameBuffer (source target : List Symbol) :
      frame [0] (List.replicate payload.length (data true) ++ [0]) [0]
        (source ++ [0]) [0] (target ++ [0]) =
      (fun name => if name = 0 then unary payload.length else if name = 1 then buffer source else buffer target) := by
    funext name
    fin_cases name <;>
      simp [frame, buffer_padding, unary, tape, word, buffer, List.map_replicate]
  have trace := runs payload old sameLength [0] (sourceAfter ++ [0]) [0] (targetAfter ++ [0])
    width (fun _ => 0) (by constructor; omega; simpa using fits)
  simp only [← List.append_assoc] at trace
  rw [frameBuffer, frameBuffer] at trace
  exact trace

end Polytime2.UnaryCopy

namespace Polytime2.PrefixCopy

open MultiTape CallingConvention
open Binary (Symbol)

variable {TapeName : Type} [DecidableEq TapeName]

noncomputable def machine (wiring : Fin 3 ↪ TapeName) : Machine (Alphabet TapeName) (Fin 4) :=
  MultiTape.wire wiring UnaryCopy.machine

/-- Copying a live prefix does not require source or destination capacities to
be equal to that prefix, and it preserves every other tape. -/
theorem runs (wiring : Fin 3 ↪ TapeName) (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (writable : readOnly (wiring 2) = false)
    (payload old sourceAfter targetAfter : List Symbol) (sameLength : old.length = payload.length)
    (fits : payload.length ≤ width (wiring 2)) (initial : Tapes (Alphabet TapeName))
    (header : initial (wiring 0) = unary payload.length)
    (source : initial (wiring 1) = buffer (payload ++ sourceAfter))
    (target : initial (wiring 2) = buffer (old ++ targetAfter)) :
    Runs width readOnly (machine wiring) (3 * payload.length + 3) 0 (fun _ => 0) initial
      3 (fun _ => 0) (Function.update initial (wiring 2) (buffer (payload ++ targetAfter))) := by
  have trace := UnaryCopy.buffer_runs payload old sourceAfter targetAfter sameLength
    (fun name => width (wiring name)) fits
  apply trace.wire_of_eq wiring width readOnly
  · intro name; rfl
  · intro name premise
    fin_cases name
    · decide
    · decide
    · simp [writable] at premise
  · intro name
    fin_cases name <;> simp only [Fin.isValue] <;> assumption
  · intro name
    fin_cases name
    · rw [Function.update_of_ne (wiring.injective.ne (by decide))]
      exact header
    · rw [Function.update_of_ne (wiring.injective.ne (by decide))]
      exact source
    · simp
  · intro name outside
    apply Function.update_of_ne
    intro equal
    exact outside ⟨2, equal.symm⟩

end Polytime2.PrefixCopy
