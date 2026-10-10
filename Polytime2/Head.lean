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

import Polytime2.Binary

/-! # Head positioning for fixed-width array elements

Fixed movement uses a specialization-dependent controller. Returning to an
array's left boundary uses a fixed controller and a linear scan of binary data.
Neither routine changes tape contents.
-/

namespace Polytime2.Move

open MultiTape

-- tapeLevel: moved tape names; symbolLevel: their alphabets.
universe tapeLevel symbolLevel
variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]

def machine (count : ℕ) (direction : Turing.Dir) : Machine Alphabet (Fin (count + 1)) :=
  fun remaining symbols => if finished : remaining.val = 0 then none else
    some (⟨remaining.val - 1, by omega⟩, fun name => (symbols name, some direction))

private theorem remaining_steps (count remaining : ℕ) (fits : remaining < count + 1)
    (direction : Turing.Dir) (tapes : Tapes Alphabet) :
    Steps (machine count direction) remaining (⟨remaining, fits⟩, tapes)
      (0, fun name => (Turing.Tape.move direction)^[remaining] (tapes name)) := by
  induction remaining generalizing tapes with
  | zero => exact .zero _
  | succ remaining hypothesis =>
    have smaller : remaining < count + 1 := by omega
    have first : step (machine count direction) (⟨remaining + 1, fits⟩, tapes) =
        some (⟨remaining, smaller⟩, fun name => (tapes name).move direction) := by
      simp [step, machine, act_move]
    have rest := hypothesis smaller (fun name => (tapes name).move direction)
    simpa only [Function.iterate_succ_apply] using Steps.next first rest

theorem steps (count : ℕ) (direction : Turing.Dir) (tapes : Tapes Alphabet) :
    Steps (machine count direction) count (Fin.last count, tapes)
      (0, fun name => (Turing.Tape.move direction)^[count] (tapes name)) :=
  remaining_steps count count (Nat.lt_succ_self count) direction tapes

/-- Moving across an ordinary word preserves its cells in the reversed left region. -/
theorem right_list {Symbol : Type symbolLevel} [Inhabited Symbol]
    (payload left right : List Symbol) :
    (Turing.Tape.move .right)^[payload.length]
      (Turing.Tape.mk' (Turing.ListBlank.mk left) (Turing.ListBlank.mk (payload ++ right))) =
      Turing.Tape.mk' (Turing.ListBlank.mk (payload.reverse ++ left)) (Turing.ListBlank.mk right) := by
  induction payload generalizing left with
  | nil => rfl
  | cons symbol payload hypothesis =>
    simp only [List.length_cons, Function.iterate_succ_apply, List.cons_append,
      Turing.Tape.move_right_mk', Turing.ListBlank.head_mk, List.headI_cons,
      Turing.ListBlank.tail_mk, List.tail_cons, Turing.ListBlank.cons_mk]
    simpa [List.reverse_cons, List.append_assoc] using hypothesis (symbol :: left)

-- parameterLevel: size names of any caller of this fixed movement routine.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
    [∀ name, Fintype (Alphabet name)] (count : ℕ) (direction : Turing.Dir) :
    Realizes (machine (Alphabet := Alphabet) count direction) (Fin.last count) 0
      (fun (_assignment : Parameter → ℕ) _ => True)
      (fun _ initial final => final = fun name => (Turing.Tape.move direction)^[count] (initial name)) := by
  refine ⟨by intro symbols; simp [machine], MvPolynomial.C count, ?_⟩
  intro assignment initial _valid
  exact ⟨count, _, by simp, steps count direction initial, rfl⟩

end Polytime2.Move

namespace Polytime2.BoundaryReturn

open MultiTape
open Binary (Symbol data word tape)

def machine : Machine (fun _ : Unit => Symbol) (Fin 2) := fun state symbols =>
  if state = 0 then
    if symbols () = 3 then some (1, fun _ => (symbols (), some .right))
    else some (0, fun _ => (symbols (), some .left))
  else none

theorem steps (preceding : List Bool) (current : Symbol) (notBoundary : current ≠ 3)
    (left right : List Symbol) :
    Steps machine (preceding.length + 2)
      (0, tape (word preceding ++ 3 :: left) (current :: right))
      (1, tape (3 :: left) ((word preceding).reverse ++ current :: right)) := by
  induction preceding generalizing current right with
  | nil =>
    have first : step machine (0, tape (3 :: left) (current :: right)) =
        some (0, tape left (3 :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte]
      congr 2
    have second : step machine (0, tape left (3 :: current :: right)) =
        some (1, tape (3 :: left) (current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte]
      congr 2
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit preceding hypothesis =>
    have first : step machine
        (0, tape (word (bit :: preceding) ++ 3 :: left) (current :: right)) =
        some (0, tape (word preceding ++ 3 :: left) (data bit :: current :: right)) := by
      simp only [step, machine, MultiTape.read, tape, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte]
      congr 2
    have notMarker : data bit ≠ 3 := by cases bit <;> decide
    have rest := hypothesis (data bit) notMarker (current :: right)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

-- parameterLevel: size names bounding the distance to the array boundary.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine 0 1
      (fun assignment initial => ∃ preceding current left right,
        preceding.length ≤ MvPolynomial.eval assignment capacity ∧ current ≠ 3 ∧
          initial = tape (word preceding ++ 3 :: left) (current :: right))
      (fun _ initial final => ∃ preceding current left right,
        initial = tape (word preceding ++ 3 :: left) (current :: right) ∧
          final = tape (3 :: left) ((word preceding).reverse ++ current :: right)) := by
  refine ⟨by intro symbols; rfl, capacity + 2, ?_⟩
  intro assignment initial valid
  obtain ⟨preceding, current, left, right, fits, notBoundary, rfl⟩ := valid
  refine ⟨preceding.length + 2, tape (3 :: left) ((word preceding).reverse ++ current :: right),
    ?_, steps preceding current notBoundary left right, preceding, current, left, right, rfl, rfl⟩
  simp only [map_add, map_ofNat]
  omega

end Polytime2.BoundaryReturn
