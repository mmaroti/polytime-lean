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


import Polytime2.UnaryAppend

/-! # Preserving copies of unary counters

Clear the destination, append the source, and return the destination head.
Gauss–Jordan uses this to initialize a candidate from the next pivot row.
-/

namespace Polytime2.UnaryCopy

open MultiTape
open Binary (Symbol tape)

noncomputable def clear : Machine (fun _ : Bool => Symbol) (Fin 3) :=
  wire (oneTape true) (Unary.machine true)

noncomputable def returnTarget : Machine (fun _ : Bool => Symbol) (Fin 2) :=
  wire (oneTape true) BoundaryReturn.machine

abbrev State := Sum (Fin 3) (Sum (Sum (Fin 2) (Fin 2)) (Fin 2))

noncomputable def machine : Machine (fun _ : Bool => Symbol) State :=
  sequence clear (sequence UnaryAppend.machine returnTarget 0) (.inl (.inl 0))

def entry : State := .inl 0
def exit : State := .inr (.inr 1)

def frame (source target : ℕ) : Tapes (fun _ : Bool => Symbol) :=
  Copy.frame [3] (List.replicate source 2 ++ [0]) [3] (List.replicate target 2 ++ [0])

private theorem clear_steps (source target : ℕ) :
    Steps clear (2 * target + 3) (0, frame source target) (2, frame source 0) := by
  have blank : Turing.ListBlank.mk (List.replicate target (0 : Symbol) ++ [0]) = Turing.ListBlank.mk [0] := by
    have zeros : Turing.ListBlank.mk (List.replicate target (0 : Symbol) ++ [0]) = Turing.ListBlank.mk [] :=
      Quotient.sound (Or.inr ⟨target + 1, by simp [List.replicate_succ']⟩)
    exact zeros.trans UnaryAppend.mk_zero.symm
  apply wire_steps_of_eq (oneTape true) _ (Unary.reset_steps target [] [])
  · intro name; cases name; rfl
  · intro name; cases name
    change Turing.Tape.mk' _ (Turing.ListBlank.mk [0]) = Turing.Tape.mk' _
      (Turing.ListBlank.mk (List.replicate target 0 ++ [0]))
    rw [blank]
  · intro name outside
    cases name with
    | false => rfl
    | true => exact False.elim (outside ⟨(), rfl⟩)

private theorem return_steps (source : ℕ) :
    Steps returnTarget (source + 2)
      (0, Copy.frame [3] (List.replicate source 2 ++ [0]) (List.replicate source 2 ++ [3]) [0])
      (1, frame source source) := by
  have trace : Steps BoundaryReturn.machine (source + 2)
      (0, tape (List.replicate source 2 ++ [3]) [0])
      (1, tape [3] (List.replicate source 2 ++ [0])) := by
    simpa [Binary.word, Binary.data] using BoundaryReturn.steps (List.replicate source true) 0 (by decide) [] []
  apply wire_steps_of_eq (oneTape true) _ trace
  · intro name; cases name; rfl
  · intro name; cases name; rfl
  · intro name outside
    cases name with
    | false => rfl
    | true => exact False.elim (outside ⟨(), rfl⟩)

theorem steps (source target : ℕ) :
    Steps machine (3 * source + 2 * target + 11) (entry, frame source target) (exit, frame source source) := by
  have append := UnaryAppend.steps source [] [] [3]
  have copied := sequence_steps UnaryAppend.machine returnTarget 0 append
    (by intro symbols; simp [UnaryAppend.machine, MultiTape.sequence, UnaryAppend.returnSource, wire, BoundaryReturn.machine])
    (return_steps source)
  have trace := sequence_steps clear (sequence UnaryAppend.machine returnTarget 0) (.inl (.inl 0))
    (clear_steps source target) (by intro symbols; simp [clear, wire, Unary.machine]) copied
  convert trace using 1 <;> first | rfl | omega

-- parameterLevel: runtime size names bounding source and destination counters.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (sourceCapacity targetCapacity : MvPolynomial Parameter ℕ) :
    Realizes machine entry exit
      (fun assignment initial => ∃ source target,
        source ≤ MvPolynomial.eval assignment sourceCapacity ∧
        target ≤ MvPolynomial.eval assignment targetCapacity ∧ initial = frame source target)
      (fun _ initial final => ∀ source target, initial = frame source target → final = frame source source) := by
  refine ⟨by intro symbols; simp [machine, exit, MultiTape.sequence, returnTarget, wire, BoundaryReturn.machine],
    3 * sourceCapacity + 2 * targetCapacity + 11, ?_⟩
  intro assignment initial valid
  obtain ⟨source, target, sourceBound, targetBound, rfl⟩ := valid
  refine ⟨3 * source + 2 * target + 11, _, ?_, steps source target, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    omega
  · intro otherSource otherTarget equal
    have otherTrace := steps otherSource otherTarget
    rw [← equal] at otherTrace
    exact congrArg Prod.snd ((steps source target).final_eq otherTrace
      (by simp [step, machine, exit, MultiTape.sequence, returnTarget, wire, BoundaryReturn.machine])
      (by simp [step, machine, exit, MultiTape.sequence, returnTarget, wire, BoundaryReturn.machine]))

end Polytime2.UnaryCopy
