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

import Polytime2.StandardBinaryRemainder
import Polytime2.Gcd

/-! # A Euclidean step with immutable operands

Compute the remainder in private fixed-width storage, then copy the divisor
to a second output tape. The two original operands remain unchanged.
-/

namespace Polytime2.StandardGcdStep

open MultiTape CallingConvention
open Binary (Symbol word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)
abbrev State := Sum StandardBinaryRemainder.State (Fin 3)
abbrev Workspace := StandardBinaryRemainder.Workspace

/-- The remainder machine's seven tapes, followed by the new first operand. -/
def frame (left right : List Bool) (work : Workspace) (newLeft : List Symbol) : Tapes Alphabet :=
  fun name => if name = 0 then buffer (word work.1)
    else if name = 1 then buffer (word right)
    else if name = 2 then buffer work.2.1
    else if name = 3 then buffer work.2.2.1
    else if name = 4 then buffer [work.2.2.2.2]
    else if name = 5 then buffer work.2.2.2.1
    else if name = 6 then buffer (word left)
    else buffer newLeft

def initialFrame (left right : List Bool) (work : Workspace)
    (oldRemainder newLeft : List Symbol) : Tapes Alphabet :=
  fun name => if name = 0 then buffer oldRemainder else frame left right work newLeft name

def widths (digits : ℕ) (name : Fin 8) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 1 ∨ name = 6)

def remainderWiring : Fin 7 ↪ Fin 8 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 8 => name.val) equal)⟩

def copyWiring : Bool ↪ Fin 8 :=
  ⟨(fun name => if name then 7 else 1), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem remainderWiring_apply (name : Fin 7) :
    remainderWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem copyWiring_apply (name : Bool) :
    copyWiring name = (if name then 7 else 1) := rfl

noncomputable def remainderMachine : Machine Alphabet StandardBinaryRemainder.State :=
  MultiTape.wire remainderWiring StandardBinaryRemainder.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  MultiTape.wire copyWiring StandardTerminatedCopy.machine

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence remainderMachine copyMachine 0

def entry : State := .inl StandardBinaryRemainder.entry
def exit : State := .inr 2

private theorem remainder_install (left right : List Bool) (work original : Workspace)
    (newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (frame left right original newLeft) = frame left right work newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install remainderWiring _ _ (remainderWiring 0) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 1) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 2) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 3) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 4) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 5) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 6) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 8 => name.val) equal;
        have bounded := localName.isLt; simp only [remainderWiring_apply] at values; omega)

private theorem remainder_initial (left right : List Bool) (work : Workspace)
    (old newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.initialFrame (buffer (word left)) right old work)
      (initialFrame left right work old newLeft) = initialFrame left right work old newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install remainderWiring _ _ (remainderWiring 0) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 1) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 2) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 3) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 4) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 5) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 6) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 8 => name.val) equal;
        have bounded := localName.isLt; simp only [remainderWiring_apply] at values; omega)

private theorem remainder_final (left right : List Bool) (work original : Workspace)
    (old newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (initialFrame left right original old newLeft) = frame left right work newLeft := by
  have same : install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (initialFrame left right original old newLeft) =
      install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
        (frame left right original newLeft) := by
    funext name
    by_cases located : name ∈ Set.range remainderWiring
    · obtain ⟨localName, rfl⟩ := located
      rw [install_at, install_at]
    · rw [install_outside _ _ _ _ located, install_outside _ _ _ _ located]
      have notZero : name ≠ 0 := by
        intro equal
        subst name
        exact located ⟨0, rfl⟩
      simp [initialFrame, notZero]
  rw [same, remainder_install]

private theorem copy_install (left right : List Bool) (work : Workspace)
    (old newLeft : List Symbol) :
    install copyWiring (Copy.frame [0] (word right ++ [0]) [0] (newLeft ++ [0]))
      (frame left right work old) = frame left right work newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install copyWiring _ _ (copyWiring false) = _;
        rw [install_at]; exact buffer_padding (word right))
    | (change install copyWiring _ _ (copyWiring true) = _;
        rw [install_at]; exact buffer_padding newLeft)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        cases localName <;> simp [copyWiring_apply] at equal)

/-- A complete Euclidean step uses a separate output for each new operand.
Every internal controller obeys the fixed-region convention. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (old shifted difference result newLeft : List Symbol)
    (oldLength : old.length = right.length) (shiftedLength : shifted.length = right.length)
    (differenceLength : difference.length = right.length) (resultLength : result.length = right.length)
    (newLeftLength : newLeft.length = right.length) (flag : Symbol) :
    let work : Workspace := (List.replicate right.length false, shifted, difference, result, flag)
    Runs (widths right.length) readOnly machine (8 * right.length ^ 2 + 21 * right.length + 9)
      entry (fun _ => 0) (initialFrame left right work old newLeft)
      exit (fun _ => 0) (frame left right
        (StandardBinaryRemainder.finish right left.reverse work) (word right)) := by
  dsimp only
  let work : Workspace := (List.replicate right.length false, shifted, difference, result, flag)
  have first := (StandardBinaryRemainder.runs left right old shifted difference result
    oldLength shiftedLength differenceLength resultLength flag).wire
    remainderWiring (widths right.length) readOnly
    (by intro name; fin_cases name <;>
        simp [widths, StandardBinaryRemainder.widths, sameLength, remainderWiring_apply])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, StandardBinaryRemainder.readOnly, remainderWiring_apply])
    (initialFrame left right work old newLeft) (fun _ => 0)
  have firstPositions : install remainderWiring (fun _ : Fin 7 => (0 : ℤ))
      (fun _ : Fin 8 => (0 : ℤ)) = fun _ => 0 := install_self remainderWiring _
  rw [firstPositions, remainder_initial, remainder_final] at first
  have second := (StandardTerminatedCopy.runs right newLeft newLeftLength).wire
    copyWiring (widths right.length) readOnly
    (by intro name; cases name <;> simp [widths, copyWiring_apply])
    (by intro name premise; cases name <;> simp [readOnly, copyWiring_apply] at premise ⊢)
    (frame left right (StandardBinaryRemainder.finish right left.reverse work) newLeft) (fun _ => 0)
  have secondPositions : install copyWiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Fin 8 => (0 : ℤ)) = fun _ => 0 := install_self copyWiring _
  rw [secondPositions, copy_install, copy_install] at second
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryRemainder.machine, StandardBinaryRemainder.exit, MultiTape.sequence,
      StandardBinaryRemainder.loopMachine, StandardBitFold.machine, StandardBitFold.exit]) second
  simp only [sameLength] at complete
  convert complete using 1 <;> first | rfl | ring

/-- The two public results have the mathematical values of `Gcd.advance`. -/
theorem result_value (left right : List Bool) (shifted difference result : List Symbol) (flag : Symbol)
    (shiftedLength : shifted.length = right.length) (differenceLength : difference.length = right.length)
    (resultLength : result.length = right.length) (positive : 0 < value right)
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    (value right, value (StandardBinaryRemainder.finish right left.reverse
      (List.replicate right.length false, shifted, difference, result, flag)).1) =
      Gcd.advance (value left, value right) := by
  rw [StandardBinaryRemainder.result_value left right shifted difference result flag
    shiftedLength differenceLength resultLength positive capacity]
  rfl

end Polytime2.StandardGcdStep
