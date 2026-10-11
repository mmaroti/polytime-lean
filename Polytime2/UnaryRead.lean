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

/-! # Reading self-delimiting unary size fields

The source contains a unary field terminated by `3`, followed by the rest of
an external input. The destination is blank. Reading consumes the field and
its delimiter, preserves the source data, and creates a counter with its head
restored to the first digit. Gauss–Jordan uses this for its dimension header.
-/

namespace Polytime2.UnaryRead

open MultiTape
open Binary (Symbol)

def formatTarget : Machine (fun _ : Bool => Symbol) (Fin 2) := fun state symbols =>
  if state = 0 then
    some (1, fun name => if name then (3, some .right) else (symbols name, none))
  else none

def forward : Machine (fun _ : Bool => Symbol) (Fin 2) := fun state symbols =>
  if state = 0 then
    if symbols false = 2 then
      some (0, fun name => (if name then 2 else symbols name, some .right))
    else some (1, fun name => if name then (0, none) else (symbols name, some .right))
  else none

noncomputable def returnTarget : Machine (fun _ : Bool => Symbol) (Fin 2) :=
  wire (oneTape true) BoundaryReturn.machine

abbrev State := Sum (Sum (Fin 2) (Fin 2)) (Fin 2)

noncomputable def machine : Machine (fun _ : Bool => Symbol) State :=
  sequence (sequence formatTarget forward 0) returnTarget 0

def entry : State := .inl (.inl 0)
def exit : State := .inr 1

private theorem forward_steps (count : ℕ) (sourceLeft sourceRight targetLeft : List Symbol) :
    Steps forward (count + 1)
      (0, Copy.frame sourceLeft (List.replicate count 2 ++ 3 :: sourceRight) targetLeft [0])
      (1, Copy.frame (3 :: (List.replicate count 2 ++ sourceLeft)) sourceRight
        (List.replicate count 2 ++ targetLeft) [0]) := by
  induction count generalizing sourceLeft targetLeft with
  | zero =>
    refine .next ?_ (.zero _)
    simp only [step, forward, Fin.isValue, ↓reduceIte, MultiTape.read, Copy.frame,
      List.replicate_zero, List.nil_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk,
      List.headI_cons, show (3 : Symbol) ≠ 2 by decide, Option.map_some]
    congr 2
    funext name
    cases name <;> simp [act, Copy.frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  | succ count hypothesis =>
    have first : step forward
        (0, Copy.frame sourceLeft (List.replicate (count + 1) 2 ++ 3 :: sourceRight) targetLeft [0]) =
        some (0, Copy.frame (2 :: sourceLeft) (List.replicate count 2 ++ 3 :: sourceRight) (2 :: targetLeft) [0]) := by
      simp only [step, forward, ↓reduceIte, MultiTape.read, Copy.frame, List.replicate_succ, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, Copy.frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have commute (amount : ℕ) (tail : List Symbol) :
        List.replicate amount 2 ++ 2 :: tail = 2 :: (List.replicate amount 2 ++ tail) := by
      induction amount with
      | zero => rfl
      | succ amount smaller => simp [List.replicate_succ, smaller]
    simpa [List.replicate_succ, commute, Nat.add_assoc] using
      Steps.next first (hypothesis (2 :: sourceLeft) (2 :: targetLeft))

/-- Read one external size field; no destination storage is supplied in advance. -/
theorem steps (count : ℕ) (sourceLeft sourceRight : List Symbol) :
    Steps machine (2 * count + 6)
      (entry, Copy.frame sourceLeft (List.replicate count 2 ++ 3 :: sourceRight) [] [0])
      (exit, Copy.frame (3 :: (List.replicate count 2 ++ sourceLeft)) sourceRight
        [3] (List.replicate count 2 ++ [0])) := by
  have initialized : Steps formatTarget 1
      (0, Copy.frame sourceLeft (List.replicate count 2 ++ 3 :: sourceRight) [] [0])
      (1, Copy.frame sourceLeft (List.replicate count 2 ++ 3 :: sourceRight) [3] [0]) := by
    refine .next ?_ (.zero _)
    simp only [step, formatTarget, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    cases name with
    | false => exact Turing.Tape.write_self _
    | true => simp [act, Copy.frame, Turing.Tape.write_mk',
        Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
  have scanned := forward_steps count sourceLeft sourceRight [3]
  have restored : Steps returnTarget (count + 2)
      (0, Copy.frame (3 :: (List.replicate count 2 ++ sourceLeft)) sourceRight
        (List.replicate count 2 ++ [3]) [0])
      (1, Copy.frame (3 :: (List.replicate count 2 ++ sourceLeft)) sourceRight
        [3] (List.replicate count 2 ++ [0])) := by
    have localTrace : Steps BoundaryReturn.machine (count + 2)
        (0, Binary.tape (List.replicate count 2 ++ [3]) [0])
        (1, Binary.tape [3] (List.replicate count 2 ++ [0])) := by
      simpa [Binary.word, Binary.data] using
        BoundaryReturn.steps (List.replicate count true) 0 (by decide) [] []
    apply wire_steps_of_eq (oneTape true) _ localTrace
    · intro name; cases name; simp [Copy.frame, Binary.tape]
    · intro name; cases name; simp [Copy.frame, Binary.tape]
    · intro name outside
      cases name with
      | false => rfl
      | true => exact False.elim (outside ⟨(), rfl⟩)
  have first := sequence_steps _ _ 0 initialized (by intro symbols; simp [formatTarget]) scanned
  have complete := sequence_steps _ _ 0 first
    (by intro symbols; simp [MultiTape.sequence, forward]) restored
  convert complete using 1 <;> first | rfl | omega

theorem halt (symbols : Symbols (fun _ : Bool => Symbol)) : machine exit symbols = none := by
  simp [machine, exit, MultiTape.sequence, returnTarget, wire, BoundaryReturn.machine]

end Polytime2.UnaryRead
