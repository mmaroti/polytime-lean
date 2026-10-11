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

import Polytime2.Unary
import Polytime2.Wiring

/-! # Append a unary counter to another counter

The source starts at its first digit and returns there. The target starts
at its blank end and is left at the new end. This permits repeated addition
without rescanning the growing target. No scratch tape is needed.
-/

namespace Polytime2.UnaryAppend

open MultiTape
open Binary (Symbol tape)
open Copy (frame)

@[simp] theorem mk_replicate_zero (count : ℕ) :
    Turing.ListBlank.mk (List.replicate count (0 : Symbol)) = Turing.ListBlank.mk [] :=
  Quotient.sound (Or.inr ⟨count, rfl⟩)

@[simp] theorem mk_zero : Turing.ListBlank.mk [(0 : Symbol)] = Turing.ListBlank.mk [] :=
  Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])

def forward : Machine (fun _ : Bool => Symbol) (Fin 2) := fun state symbols =>
  if state = 0 then
    if symbols false = 0 then some (1, stationary symbols)
    else some (0, fun _ => (2, some .right))
  else none

private theorem forward_steps (count : ℕ) (sourceLeft sourceRight targetLeft : List Symbol) :
    Steps forward (count + 1)
      (0, frame sourceLeft (List.replicate count 2 ++ 0 :: sourceRight) targetLeft [0])
      (1, frame (List.replicate count 2 ++ sourceLeft) (0 :: sourceRight)
        (List.replicate count 2 ++ targetLeft) [0]) := by
  induction count generalizing sourceLeft targetLeft with
  | zero =>
    refine .next ?_ (.zero _)
    simp [step, forward, MultiTape.read, frame]
  | succ count hypothesis =>
    have first : step forward
        (0, frame sourceLeft (List.replicate (count + 1) 2 ++ 0 :: sourceRight) targetLeft [0]) =
        some (0, frame (2 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight) (2 :: targetLeft) [0]) := by
      simp only [step, forward, ↓reduceIte, MultiTape.read, frame, List.replicate_succ, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        show (2 : Symbol) ≠ 0 by decide, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have commute (amount : ℕ) (tail : List Symbol) :
        List.replicate amount 2 ++ 2 :: tail = 2 :: (List.replicate amount 2 ++ tail) := by
      induction amount with
      | zero => rfl
      | succ amount smaller => simp [List.replicate_succ, smaller]
    simpa [List.replicate_succ, commute, Nat.add_assoc] using
      Steps.next first (hypothesis (2 :: sourceLeft) (2 :: targetLeft))

noncomputable def returnSource : Machine (fun _ : Bool => Symbol) (Fin 2) :=
  wire (oneTape false) BoundaryReturn.machine

noncomputable def machine : Machine (fun _ : Bool => Symbol) (Sum (Fin 2) (Fin 2)) :=
  sequence forward returnSource 0

/-- The preserved source is added to the target's head-position counter. -/
theorem steps (count : ℕ) (sourceLeft sourceRight targetLeft : List Symbol) :
    Steps machine (2 * count + 4)
      (.inl 0, frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight) targetLeft [0])
      (.inr 1, frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight)
        (List.replicate count 2 ++ targetLeft) [0]) := by
  have scanned := forward_steps count (3 :: sourceLeft) sourceRight targetLeft
  have localTrace : Steps BoundaryReturn.machine (count + 2)
      (0, tape (List.replicate count 2 ++ 3 :: sourceLeft) (0 :: sourceRight))
      (1, tape (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight)) := by
    simpa [Binary.word, Binary.data] using
      BoundaryReturn.steps (List.replicate count true) 0 (by decide) sourceLeft sourceRight
  have restored := wire_steps (oneTape false) BoundaryReturn.machine localTrace
    (frame (List.replicate count 2 ++ 3 :: sourceLeft) (0 :: sourceRight)
      (List.replicate count 2 ++ targetLeft) [0]) (by intro name; cases name; rfl)
  have installed : install (oneTape false)
      (tape (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight))
      (frame (List.replicate count 2 ++ 3 :: sourceLeft) (0 :: sourceRight)
        (List.replicate count 2 ++ targetLeft) [0]) =
      frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight)
        (List.replicate count 2 ++ targetLeft) [0] := by
    funext name
    cases name <;> simp [frame, Binary.tape, Function.update]
  rw [installed] at restored
  have trace := sequence_steps forward returnSource 0 scanned
    (by intro symbols; simp [forward]) restored
  convert trace using 1 <;> first | rfl | omega

-- parameterLevel: runtime size names bounding the appended value.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine (.inl 0) (.inr 1)
      (fun assignment initial => ∃ (count : ℕ) (sourceLeft sourceRight targetLeft : List Symbol),
        count ≤ MvPolynomial.eval assignment capacity ∧
        initial = frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight) targetLeft [0])
      (fun _ initial final => ∃ (count : ℕ) (sourceLeft sourceRight targetLeft : List Symbol),
        initial = frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight) targetLeft [0] ∧
        final = frame (3 :: sourceLeft) (List.replicate count 2 ++ 0 :: sourceRight)
          (List.replicate count 2 ++ targetLeft) [0]) := by
  refine ⟨by intro symbols; simp [machine, MultiTape.sequence, returnSource, wire, BoundaryReturn.machine], 2 * capacity + 4, ?_⟩
  intro assignment initial valid
  obtain ⟨count, sourceLeft, sourceRight, targetLeft, bounded, rfl⟩ := valid
  refine ⟨2 * count + 4, _, ?_, steps count sourceLeft sourceRight targetLeft,
    count, sourceLeft, sourceRight, targetLeft, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.UnaryAppend
