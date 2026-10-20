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

import Polytime2.Arithmetic.BinaryDivision
import Polytime2.Arithmetic.GcdMath

/-! # A Euclidean step with immutable operands

Compute the remainder in private fixed-width storage, then copy the divisor
to a second output tape. The two original operands remain unchanged.
-/

namespace Polytime2.StandardGcdStep

open MultiTape CallingConvention
open Binary (Symbol word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)
abbrev State := Sum StandardBinaryDivision.State (Fin 3)
def widths (digits : ℕ) (name : Fin 8) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 1 ∨ name = 6)

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy 1 7 (by decide)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence StandardBinaryDivision.machine copyMachine 0

def entry : State := .inl StandardBinaryDivision.entry
def exit : State := .inr 2

/-- Both results are live encodings; all other writable tapes stay private. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (initial : Tapes Alphabet) (leftEq : initial 6 = buffer (word left))
    (rightEq : initial 1 = buffer (word right))
    (regions : ∀ name, Region (widths right.length name) 0 (initial name)) :
    ∃ final, Runs (widths right.length) readOnly machine (12 * right.length ^ 2 + 31 * right.length + 12)
      entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      final 0 = buffer (word ((StandardBinaryDivision.finish right left.reverse
        (List.replicate right.length false, List.replicate right.length false)).2)) ∧
      final 7 = buffer (word right) := by
  have widthsMatch : StandardBinaryDivision.widths left.length right.length = widths right.length := by
    funext name
    fin_cases name <;> simp [StandardBinaryDivision.widths, widths, sameLength]
  obtain ⟨after, first, quotientResult, result⟩ := StandardBinaryDivision.runs left right
    initial leftEq rightEq (by intro name; rw [widthsMatch]; exact regions name)
  rw [widthsMatch] at first
  obtain ⟨old, oldLength, oldEq⟩ := (first.region 7 (regions 7)).exists_buffer
  have copied := StandardTapeCommands.copy_runs (1 : Fin 8) 7 (by decide)
    (widths right.length) readOnly rfl right old rfl rfl oldLength after
    ((first.readOnly_tape 1 rfl).trans rightEq) oldEq
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [StandardBinaryDivision.machine, StandardBinaryDivision.exit,
      MultiTape.sequence, StandardBinaryDivision.loopMachine, StandardBitFold.machine, StandardBitFold.exit]) copied
  refine ⟨Function.update after 7 (buffer (word right)), ?_, ?_, Function.update_self _ _ _⟩
  · convert complete using 1 <;> first | rfl | (simp [sameLength]; ring)
  · exact (Function.update_of_ne (by decide : (0 : Fin 8) ≠ 7) _ _).trans result

end Polytime2.StandardGcdStep
