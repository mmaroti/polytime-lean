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

/-! # Comparison of polynomially bounded unary counters

Two counters are scanned together until one ends. The Boolean result is
written on a third tape, and both counter heads return to their boundaries.
-/

namespace Polytime2.UnaryCompare

open MultiTape
open Binary (Symbol)

/-- `some false` and `some true` hold counters; `none` holds the result. -/
abbrev TapeName := Option Bool

abbrev Alphabet (_name : TapeName) := Symbol

def frame (left right : Bool → List Symbol) (flag : Turing.Tape Symbol) : Tapes Alphabet
  | some name => Turing.Tape.mk' (Turing.ListBlank.mk (left name)) (Turing.ListBlank.mk (right name))
  | none => flag

def machine : Machine Alphabet (Fin 3) := fun phase symbols =>
  match phase.val with
  | 0 => if symbols (some false) = 2 ∧ symbols (some true) = 2 then
      some (0, fun name => match name with
        | some _ => (symbols name, some .right)
        | none => (symbols none, none))
    else some (1, fun name =>
      (if name = none then Binary.data (decide (symbols (some false) = 0 ∧ symbols (some true) = 2))
        else symbols name, none))
  | 1 => if symbols (some false) = 3 then
      some (2, fun name => (symbols name, if name = none then none else some .right))
    else some (1, fun name => (symbols name, if name = none then none else some .left))
  | _ => none

private theorem replicate_cons (count : ℕ) (tail : List Symbol) :
    List.replicate count 2 ++ 2 :: tail = 2 :: (List.replicate count 2 ++ tail) := by
  induction count with
  | zero => rfl
  | succ count hypothesis => simp [List.replicate_succ, hypothesis]

private theorem forward_steps (count : ℕ) (left right : Bool → List Symbol)
    (flag : Turing.Tape Symbol) :
    Steps machine count
      (0, frame left (fun name => List.replicate count 2 ++ right name) flag)
      (0, frame (fun name => List.replicate count 2 ++ left name) right flag) := by
  induction count generalizing left with
  | zero => simpa using Steps.zero (machine := machine) (0, frame left right flag)
  | succ count hypothesis =>
    have first : step machine
        (0, frame left (fun name => List.replicate (count + 1) 2 ++ right name) flag) =
        some (0, frame (fun name => 2 :: left name)
          (fun name => List.replicate count 2 ++ right name) flag) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, List.replicate_succ,
        List.cons_append, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons,
        and_self, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_self,
        Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [List.replicate_succ, replicate_cons] using
      Steps.next first (hypothesis (fun name => 2 :: left name))

private theorem rewind_steps (count : ℕ) (left right : Bool → List Symbol)
    (current : Bool → Symbol) (notBoundary : current false ≠ 3) (flag : Turing.Tape Symbol) :
    Steps machine (count + 2)
      (1, frame (fun name => List.replicate count 2 ++ 3 :: left name)
        (fun name => current name :: right name) flag)
      (2, frame (fun name => 3 :: left name)
        (fun name => List.replicate count 2 ++ current name :: right name) flag) := by
  induction count generalizing current right with
  | zero =>
    have first : step machine
        (1, frame (fun name => 3 :: left name) (fun name => current name :: right name) flag) =
        some (1, frame left (fun name => 3 :: current name :: right name) flag) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_self,
        Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        (1, frame left (fun name => 3 :: current name :: right name) flag) =
        some (2, frame (fun name => 3 :: left name) (fun name => current name :: right name) flag) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_self,
        Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa using Steps.next first (Steps.next second (.zero _))
  | succ count hypothesis =>
    have first : step machine
        (1, frame (fun name => List.replicate (count + 1) 2 ++ 3 :: left name)
          (fun name => current name :: right name) flag) =
        some (1, frame (fun name => List.replicate count 2 ++ 3 :: left name)
          (fun name => 2 :: current name :: right name) flag) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, List.replicate_succ, Turing.Tape.write_self,
        Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    simpa [List.replicate_succ, replicate_cons, Nat.add_assoc] using
      Steps.next first (hypothesis (fun name => current name :: right name) (fun _ => 2) (by decide))

/-- Compare counters with a common scanned prefix and unequal or exhausted next digits. -/
private theorem stopped_steps (count : ℕ) (left right : Bool → List Symbol)
    (current : Bool → Symbol) (notBoundary : current false ≠ 3)
    (stopped : ¬ (current false = 2 ∧ current true = 2)) (flag : Turing.Tape Symbol) :
    Steps machine (2 * count + 3)
      (0, frame (fun name => 3 :: left name)
        (fun name => List.replicate count 2 ++ current name :: right name) flag)
      (2, frame (fun name => 3 :: left name)
        (fun name => List.replicate count 2 ++ current name :: right name)
        (flag.write (Binary.data (decide (current false = 0 ∧ current true = 2))))) := by
  have scanned := forward_steps count (fun name => 3 :: left name)
    (fun name => current name :: right name) flag
  have finish : step machine
      (0, frame (fun name => List.replicate count 2 ++ 3 :: left name)
        (fun name => current name :: right name) flag) =
      some (1, frame (fun name => List.replicate count 2 ++ 3 :: left name)
        (fun name => current name :: right name)
        (flag.write (Binary.data (decide (current false = 0 ∧ current true = 2))))) := by
    simp only [step, machine, Fin.val_zero, MultiTape.read, frame, Turing.Tape.mk'_head,
      Turing.ListBlank.head_mk, List.headI_cons, stopped, ↓reduceIte, Option.map_some]
    congr 2
    funext name
    cases name with
    | none =>
      by_cases firstZero : current false = 0 <;> by_cases secondLive : current true = 2 <;>
        simp [act, frame, firstZero, secondLive]
    | some name => simp [act, frame]
  have restored := rewind_steps count left right current notBoundary
    (flag.write (Binary.data (decide (current false = 0 ∧ current true = 2))))
  convert scanned.trans (Steps.next finish restored) using 1
  omega

/-- Canonical counter tapes and an arbitrary result tape. -/
def counters (first second : ℕ) (flag : Turing.Tape Symbol) : Tapes Alphabet :=
  frame (fun _ => [3])
    (fun name => List.replicate (if name then second else first) 2 ++ [0]) flag

private theorem ordered_steps (count extra : ℕ) (reversed : Bool) (flag : Turing.Tape Symbol) :
    Steps machine (2 * count + 3)
      (0, counters (if reversed then count + extra else count)
        (if reversed then count else count + extra) flag)
      (2, counters (if reversed then count + extra else count)
        (if reversed then count else count + extra)
        (flag.write (Binary.data (decide (extra > 0 ∧ reversed = false))))) := by
  cases extra with
  | zero =>
    have trace := stopped_steps count (fun _ => []) (fun _ => []) (fun _ => 0)
      (by decide) (by decide) flag
    simpa [counters] using trace
  | succ extra =>
    have trace := stopped_steps count (fun _ => [])
      (fun name => if name != reversed then List.replicate extra 2 ++ [0] else [])
      (fun name => if name != reversed then 2 else 0)
      (by cases reversed <;> decide) (by cases reversed <;> decide) flag
    convert trace using 1 <;> first
    | rfl
    | (congr 1
       funext name
       cases name with
       | none => cases reversed <;> simp [counters, frame]
       | some name => cases name <;> cases reversed <;>
           simp [counters, frame, List.replicate_add, List.replicate_succ, List.append_assoc])

theorem steps (first second : ℕ) (flag : Turing.Tape Symbol) :
    Steps machine (2 * min first second + 3)
      (0, counters first second flag)
      (2, counters first second (flag.write (Binary.data (decide (first < second))))) := by
  rcases le_total first second with ordered | ordered
  · have trace := ordered_steps first (second - first) false flag
    have total : first + (second - first) = second := Nat.add_sub_of_le ordered
    simpa [total, Nat.min_eq_left ordered, show second - first > 0 ↔ first < second by omega] using trace
  · have trace := ordered_steps second (first - second) true flag
    have total : second + (first - second) = first := Nat.add_sub_of_le ordered
    simpa [total, Nat.min_eq_right ordered, show ¬ first < second by omega] using trace

-- parameterLevel: runtime size names bounding the first counter.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine 0 2
      (fun assignment initial => ∃ (first second : ℕ) (flag : Turing.Tape Symbol),
        first ≤ MvPolynomial.eval assignment capacity ∧ initial = counters first second flag)
      (fun _ initial final => ∀ (first second : ℕ) (flag : Turing.Tape Symbol),
        initial = counters first second flag →
        final = counters first second (flag.write (Binary.data (decide (first < second))))) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨first, second, flag, bounded, rfl⟩ := valid
  refine ⟨2 * min first second + 3, _, ?_, steps first second flag, ?_⟩
  · simp only [map_add, map_mul, map_ofNat]
    have := Nat.min_le_left first second
    omega
  · intro otherFirst otherSecond otherFlag equal
    have otherTrace := steps otherFirst otherSecond otherFlag
    rw [← equal] at otherTrace
    exact congrArg Prod.snd ((steps first second flag).final_eq otherTrace rfl rfl)

end Polytime2.UnaryCompare
