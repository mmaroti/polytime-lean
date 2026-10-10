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
import Polytime2.Copy

/-! # Copying a runtime-width binary index

Tape false supplies the digits and tape true receives them. Both digit regions
have a left boundary (3) and a blank terminator (0). Unlike fixed-width element
copying, this controller does not depend on the digit count. Proofs reuse the
forward/return traversal pattern of `Polytime2.Copy`.
-/

namespace Polytime2.TerminatedCopy

open MultiTape
open Binary (Symbol data word)
open Copy (frame)

def machine : Machine (fun _ : Bool => Symbol) (Fin 3) := fun state symbols =>
  match state.val with
  | 0 => if symbols false = 0 then some (1, stationary symbols)
    else some (0, fun _ => (symbols false, some .right))
  | 1 => if symbols false = 3 then
      some (2, fun name => (symbols name, some .right))
    else some (1, fun name => (symbols name, some .left))
  | _ => none

private theorem forward (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine bits.length
      (0, frame sourceLeft (word bits ++ sourceRight) targetLeft (old ++ targetRight))
      (0, frame ((word bits).reverse ++ sourceLeft) sourceRight
        ((word bits).reverse ++ targetLeft) targetRight) := by
  induction bits generalizing old sourceLeft targetLeft with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero sameLength
    subst old
    simpa [word] using Steps.zero (machine := machine) (0, frame sourceLeft sourceRight targetLeft targetRight)
  | cons bit bits hypothesis =>
    cases old with
    | nil => simp at sameLength
    | cons previous old =>
      have first : step machine
          (0, frame sourceLeft (word (bit :: bits) ++ sourceRight) targetLeft ((previous :: old) ++ targetRight)) =
          some (0, frame (data bit :: sourceLeft) (word bits ++ sourceRight)
            (data bit :: targetLeft) (old ++ targetRight)) := by
        have nonblank : data bit ≠ 0 := by cases bit <;> decide
        simp only [step, machine, Fin.val_zero, MultiTape.read, frame, word, List.map_cons, List.cons_append,
          Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank, ↓reduceIte, Option.map_some]
        congr 2
        funext name
        cases name <;>
          simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
      have rest := hypothesis old (by simpa using sameLength) (data bit :: sourceLeft) (data bit :: targetLeft)
      simpa [word, List.reverse_cons, List.append_assoc] using Steps.next first rest

private theorem return_head (bits : List Bool) (current : Symbol) (notBoundary : current ≠ 3)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine (bits.length + 2)
      (1, frame (word bits ++ 3 :: sourceLeft) (current :: sourceRight)
        (word bits ++ 3 :: targetLeft) (current :: targetRight))
      (2, frame (3 :: sourceLeft) ((word bits).reverse ++ current :: sourceRight)
        (3 :: targetLeft) ((word bits).reverse ++ current :: targetRight)) := by
  induction bits generalizing current sourceRight targetRight with
  | nil =>
    have first : step machine
        (1, frame (3 :: sourceLeft) (current :: sourceRight) (3 :: targetLeft) (current :: targetRight)) =
        some (1, frame sourceLeft (3 :: current :: sourceRight) targetLeft (3 :: current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        (1, frame sourceLeft (3 :: current :: sourceRight) targetLeft (3 :: current :: targetRight)) =
        some (2, frame (3 :: sourceLeft) (current :: sourceRight) (3 :: targetLeft) (current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    have first : step machine
        (1, frame (word (bit :: bits) ++ 3 :: sourceLeft) (current :: sourceRight)
          (word (bit :: bits) ++ 3 :: targetLeft) (current :: targetRight)) =
        some (1, frame (word bits ++ 3 :: sourceLeft) (data bit :: current :: sourceRight)
          (word bits ++ 3 :: targetLeft) (data bit :: current :: targetRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;> simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have notMarker : data bit ≠ 3 := by cases bit <;> decide
    have rest := hypothesis (data bit) notMarker (current :: sourceRight) (current :: targetRight)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

/-- Exact linear cost, with both heads and both boundaries restored. -/
theorem steps (bits : List Bool) (old : List Symbol) (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps machine (2 * bits.length + 3)
      (0, frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (3 :: targetLeft) (old ++ 0 :: targetRight))
      (2, frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (3 :: targetLeft) (word bits ++ 0 :: targetRight)) := by
  have copied := forward bits old sameLength (3 :: sourceLeft) (0 :: sourceRight) (3 :: targetLeft) (0 :: targetRight)
  have handover : step machine
      (0, frame ((word bits).reverse ++ 3 :: sourceLeft) (0 :: sourceRight)
        ((word bits).reverse ++ 3 :: targetLeft) (0 :: targetRight)) =
      some (1, frame ((word bits).reverse ++ 3 :: sourceLeft) (0 :: sourceRight)
        ((word bits).reverse ++ 3 :: targetLeft) (0 :: targetRight)) := by
    simp [step, machine, MultiTape.read, frame]
  have restored := return_head bits.reverse 0 (by decide) sourceLeft sourceRight targetLeft targetRight
  simp only [word, List.map_reverse, List.reverse_reverse, List.length_reverse] at copied restored handover ⊢
  convert copied.trans (Steps.next handover restored) using 1; omega

-- parameterLevel: size names bounding the runtime number of digits.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine 0 2
      (fun assignment initial => ∃ bits old sourceLeft sourceRight targetLeft targetRight,
        bits.length ≤ MvPolynomial.eval assignment capacity ∧ old.length = bits.length ∧
          initial = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight)
            (3 :: targetLeft) (old ++ 0 :: targetRight))
      (fun _ initial final => ∃ bits old sourceLeft sourceRight targetLeft targetRight,
        old.length = bits.length ∧
          initial = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight)
            (3 :: targetLeft) (old ++ 0 :: targetRight) ∧
          final = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight)
            (3 :: targetLeft) (word bits ++ 0 :: targetRight)) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨bits, old, sourceLeft, sourceRight, targetLeft, targetRight, fits, length, rfl⟩ := valid
  refine ⟨2 * bits.length + 3,
    frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) (3 :: targetLeft) (word bits ++ 0 :: targetRight),
    ?_, steps bits old length sourceLeft sourceRight targetLeft targetRight,
    bits, old, sourceLeft, sourceRight, targetLeft, targetRight, length, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.TerminatedCopy
