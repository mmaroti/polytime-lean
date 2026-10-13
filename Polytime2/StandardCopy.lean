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

import Polytime2.CallingConvention
import Polytime2.Copy

/-! # Fixed-width copying under the standard calling convention

The existing copy controller needs no boundary markers or prepared output.
Its source is immutable at every transition, and all surrounding blanks stay
blank even while the heads travel outside the data interval.
-/

namespace Polytime2.StandardCopy

open MultiTape CallingConvention
open Binary (Symbol word)

abbrev Alphabet := fun _ : Bool => Symbol

def readOnly (name : Bool) : Bool := !name

def position (width : ℕ) (state : Copy.State width) : Bool → ℤ :=
  fun _ => if state.1 then (state.2.val : ℤ) else (width : ℤ) - state.2.val

private theorem safe (width : ℕ) (state : Copy.State width) (symbols : Symbols Alphabet)
    (nextState : Copy.State width) (actions : Actions Alphabet)
    (instruction : Copy.machine width state symbols = some (nextState, actions)) :
    Allowed (fun _ : Bool => width) readOnly (position width state) symbols actions ∧
      position width nextState = fun name => position width state name + displacement (actions name).2 := by
  obtain ⟨phase, remaining⟩ := state
  have bounded := remaining.isLt
  cases phase with
  | false =>
    by_cases finished : remaining.val = 0
    · simp only [Copy.machine, finished, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      constructor
      · intro name premise; rfl
      · funext name; simp [position, stationary, displacement, finished]
    · simp only [Copy.machine, finished, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      constructor
      · intro name premise
        cases name with
        | false => rfl
        | true =>
          simp only [readOnly, Bool.not_true, Bool.false_eq_true, false_or, position, Bool.false_eq_true,
            ↓reduceIte] at premise
          omega
      · funext name
        simp only [position, Bool.false_eq_true, ↓reduceIte, displacement]
        have decrement : remaining.val - 1 + 1 = remaining.val := by omega
        omega
  | true =>
    by_cases finished : remaining.val = 0
    · simp [Copy.machine, finished] at instruction
    · simp only [Copy.machine, finished, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq] at instruction
      obtain ⟨rfl, rfl⟩ := instruction
      constructor
      · intro name premise; rfl
      · funext name
        simp only [position, ↓reduceIte, displacement]
        have decrement : remaining.val - 1 + 1 = remaining.val := by omega
        omega

/-- The old counted execution now certifies the convention at every prefix. -/
theorem runs (width : ℕ) (bits : List Bool) (old : List Symbol)
    (bitsLength : bits.length = width) (oldLength : old.length = width) :
    Runs (fun _ : Bool => width) readOnly (Copy.machine width) (2 * width + 1)
      (false, Fin.last width) (fun _ => 0)
      (Copy.frame [] (word bits) [] old)
      (true, 0) (fun _ => 0) (Copy.frame [] (word bits) [] (word bits)) := by
  have trace := Runs.of_steps (position width) (safe width)
    (Copy.steps width (word bits) old (by simpa [word] using bitsLength) oldLength [] [] [] [])
  have initialPosition : position width (false, Fin.last width) = fun _ => 0 := by
    funext name; simp [position]
  have finalPosition : position width (true, 0) = fun _ => 0 := by
    funext name; simp [position]
  rw [initialPosition, finalPosition] at trace
  simpa only [List.append_nil] using trace

/-- Copy an element inside a larger array region. The surrounding data are
preserved, and both heads return to their entry positions within the tapes. -/
theorem slice_runs (width : ℕ) (bits : List Bool) (old : List Symbol)
    (bitsLength : bits.length = width) (oldLength : old.length = width)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol)
    (enclosingWidth : Bool → ℕ) (offset : Bool → ℤ)
    (fits : 0 ≤ offset true ∧ offset true + width ≤ enclosingWidth true) :
    Runs enclosingWidth readOnly (Copy.machine width) (2 * width + 1)
      (false, Fin.last width) offset
      (Copy.frame sourceLeft (word bits ++ sourceRight) targetLeft (old ++ targetRight))
      (true, 0) offset
      (Copy.frame sourceLeft (word bits ++ sourceRight) targetLeft (word bits ++ targetRight)) := by
  have trace := Runs.of_steps (position width) (safe width)
    (Copy.steps width (word bits) old (by simpa [word] using bitsLength) oldLength
      sourceLeft sourceRight targetLeft targetRight)
  have initialPosition : position width (false, Fin.last width) = fun _ => 0 := by
    funext name; simp [position]
  have finalPosition : position width (true, 0) = fun _ => 0 := by
    funext name; simp [position]
  rw [initialPosition, finalPosition] at trace
  have enclosed := trace.regions enclosingWidth offset (by
    intro name writable
    cases name
    · contradiction
    · exact fits)
  simpa only [zero_add] using enclosed

/-- No runtime size parameter is needed for a specialization-fixed width. -/
def sizeTapes : Empty ↪ Bool := ⟨Empty.elim, by intro name; cases name⟩

-- carrierLevel: mathematical elements of the copied domain.
universe carrierLevel

/-- Copy any specialization-fixed encoded domain, overwriting arbitrary output
contents and preserving the complete input throughout execution. -/
theorem contract (domain : EncodedDomain.{0, carrierLevel} Empty) (width : ℕ)
    (fixedWidth : ∀ assignment, domain.width assignment = width) :
    CallingConvention.Realizes (fun _ : Bool => domain) readOnly sizeTapes
      (Copy.machine width) (false, Fin.last width) (true, 0)
      (fun _ _ => True)
      (fun _ input output => output ⟨true, rfl⟩ = input ⟨false, rfl⟩) := by
  refine ⟨(by intro parameter; cases parameter), (by intro symbols; simp [Copy.machine]),
    MvPolynomial.C (2 * width + 1), ?_⟩
  intro assignment input initial valid represented sizes
  let bits := List.ofFn (fun index : Fin (domain.width assignment) =>
    (domain.encode assignment (input ⟨false, rfl⟩)).getLsbD index.val)
  obtain ⟨old, oldLength, target⟩ := represented.2 true rfl
  have source := represented.1 false rfl
  have initialEq : initial = Copy.frame [] (word bits) [] old := by
    funext name
    cases name with
    | false => exact source
    | true => exact target
  subst initial
  let output : Outputs (fun _ : Bool => domain) readOnly assignment := fun _ => input ⟨false, rfl⟩
  refine ⟨2 * width + 1, output, Copy.frame [] (word bits) [] (word bits), by simp, ?_, rfl, ?_⟩
  · simpa only [fixedWidth assignment] using
      runs width bits old (by simp [bits, fixedWidth]) (oldLength.trans (fixedWidth assignment))
  · intro name writable
    cases name with
    | false => contradiction
    | true => rfl

end Polytime2.StandardCopy
