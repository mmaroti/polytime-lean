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

import Polytime2.Primitives.UnaryHeader
import Polytime2.Primitives.Fill
import Polytime2.Machine.Pipeline

/-! # Clearing private tapes to blank with a restoring fixed controller

An immutable capacity header determines the extent, independently of old
writable contents. This prepares the smaller blank-surrounded regions needed
by a call at computed sizes.
-/

namespace Polytime2.Blank

open MultiTape CallingConvention
open Binary (Symbol word)

variable {TapeName : Type} [DecidableEq TapeName]

/-- Erasing is the symbol scanner with a constant blank output map. -/
noncomputable def machine (source target : TapeName) (distinct : source ≠ target) :
    Machine (Alphabet TapeName) (SymbolScan.State Unit) :=
  Fill.machine source target distinct 0

/-- All neighboring cells and source tapes are preserved, and heads return. -/
theorem runs (source target : TapeName) (distinct : source ≠ target)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (writable : readOnly target = false)
    (capacity : ℕ) (targetWidth : width target = capacity)
    (initial : Tapes (Alphabet TapeName)) (header : initial source = unary capacity)
    (region : Region capacity 0 (initial target)) :
    Runs width readOnly (machine source target distinct) (2 * capacity + 2)
      (.inl ()) (fun _ => 0) initial (.inr ((), true)) (fun _ => 0)
      (Function.update initial target (buffer [])) := by
  have trace := Fill.runs source target distinct 0 width readOnly writable capacity
    (by omega) initial header region
  have blank : buffer (List.replicate capacity (0 : Symbol)) = buffer [] := by
    simpa using UnaryHeader.buffer_append_blanks [] capacity
  simpa only [machine, blank] using trace


/-- Initialize a finite private workspace using one immutable capacity header. -/
noncomputable def prepare {count : ℕ} (header : TapeName) (targets : Fin count ↪ TapeName)
    (different : ∀ index, header ≠ targets index) :
    Machine (Alphabet TapeName) (Pipeline.State (fun _ : Fin count => SymbolScan.State Unit)) :=
  Pipeline.machine (fun index => machine header (targets index) (different index)) (fun _ => .inl ())

/-- Every private tape starts blank, with its whole capacity charged. An empty
workspace needs no special case or extra source of initialized storage. -/
theorem prepare_runs {count : ℕ} (header : TapeName) (targets : Fin count ↪ TapeName)
    (different : ∀ index, header ≠ targets index)
    (width : TapeName → ℕ) (readOnly : TapeName → Bool) (capacity : ℕ)
    (immutable : readOnly header = true) (writable : ∀ index, readOnly (targets index) = false)
    (targetWidths : ∀ index, width (targets index) = capacity)
    (initial : Tapes (Alphabet TapeName)) (headerValue : initial header = unary capacity)
    (regions : ∀ name, Region (width name) 0 (initial name)) :
    ∃ ticks final, ticks ≤ count * (2 * capacity + 3) ∧
      Runs width readOnly (prepare header targets different) ticks
        (Pipeline.position (fun _ : Fin count => (Sum.inl () : SymbolScan.State Unit)) 0)
        (fun _ => 0) initial none (fun _ => 0) final ∧
      ∀ index, final (targets index) = buffer [] := by
  have prepared := Pipeline.updates_runs width readOnly
    (fun index => machine header (targets index) (different index))
    (fun _ => .inl ()) (fun _ => .inr ((), true)) targets targets.injective
    (fun _ => buffer []) (2 * capacity + 2)
    (by intro index symbols; simp [machine, Fill.machine, MultiTape.wire, SymbolScan.machine])
    initial regions (by
      intro index tapes preserved currentRegions
      refine ⟨2 * capacity + 2, le_rfl, ?_⟩
      apply runs header (targets index) (different index) width readOnly (writable index)
        capacity (targetWidths index) tapes
      · exact (preserved header immutable).trans headerValue
      · rw [← targetWidths index]
        exact currentRegions (targets index))
  simpa only [prepare, Nat.add_assoc] using prepared

end Polytime2.Blank
