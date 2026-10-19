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

import Polytime2.Arithmetic.BinaryRemainder
import Polytime2.Arithmetic.GcdMath

/-! # A Euclidean step with immutable operands

Compute the remainder in private fixed-width storage, then copy the divisor
to a second output tape. The two original operands remain unchanged.
-/

namespace Polytime2.StandardGcdStep

open MultiTape CallingConvention
open Binary (Symbol word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)
abbrev State := Sum StandardBinaryRemainder.State (Fin 3)
def widths (digits : ℕ) (name : Fin 8) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 1 ∨ name = 6)

def remainderWiring : Fin 7 ↪ Fin 8 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 8 => name.val) equal)⟩


@[simp] theorem remainderWiring_apply (name : Fin 7) :
    remainderWiring name = ⟨name.val, by omega⟩ := rfl


noncomputable def remainderMachine : Machine Alphabet StandardBinaryRemainder.State :=
  MultiTape.wire remainderWiring StandardBinaryRemainder.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 1 7 (by decide)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence remainderMachine copyMachine 0

def entry : State := .inl StandardBinaryRemainder.entry
def exit : State := .inr 2

/-- Both results are live encodings; all other writable tapes stay private. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (initial : Tapes Alphabet) (leftEq : initial 6 = buffer (word left))
    (rightEq : initial 1 = buffer (word right))
    (regions : ∀ name, Region (widths right.length name) 0 (initial name)) :
    ∃ final, Runs (widths right.length) readOnly machine (8 * right.length ^ 2 + 21 * right.length + 9)
      entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final 0 = buffer (word (StandardBinaryRemainder.finish right left.reverse (List.replicate right.length false))) ∧
      final 7 = buffer (word right) := by
  obtain ⟨localFinal, localTrace, result⟩ := StandardBinaryRemainder.runs left right
    (fun name => initial (remainderWiring name)) leftEq rightEq
    (by
      intro name
      have region := regions (remainderWiring name)
      fin_cases name <;> simpa [widths, StandardBinaryRemainder.widths, sameLength] using region)
  obtain ⟨after, first, located, outside, immutable⟩ := localTrace.wire_restoring remainderWiring
    (widths right.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardBinaryRemainder.widths, sameLength])
    (by intro name premise; fin_cases name <;> first | rfl | contradiction) initial (fun _ => rfl)
  obtain ⟨old, oldLength, oldEq⟩ := (first.region 7 (regions 7)).exists_buffer
  have copied := StandardTapeCommands.copy_runs (1 : Fin 8) 7 (by decide)
    (widths right.length) readOnly rfl right old rfl rfl oldLength after
    ((first.readOnly_tape 1 rfl).trans rightEq) oldEq
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryRemainder.machine, StandardBinaryRemainder.exit,
      MultiTape.sequence, StandardBinaryRemainder.loopMachine, StandardBitFold.machine, StandardBitFold.exit]) copied
  refine ⟨Function.update after 7 (buffer (word right)), ?_, ?_, Function.update_self _ _ _⟩
  · convert complete using 1 <;> first | rfl | (simp [sameLength]; ring)
  · exact (Function.update_of_ne (by decide : (0 : Fin 8) ≠ 7) _ _).trans ((located 0).trans result)

end Polytime2.StandardGcdStep
