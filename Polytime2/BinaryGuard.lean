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

/-! # Restoring binary nonzero guard

Tape false holds the binary counter; tape true receives one Boolean result.
The counter, its boundaries, and both head positions are preserved. The
controller stores only a Boolean flag while scanning the runtime digit count.
-/

namespace Polytime2.BinaryGuard

open MultiTape
open Binary (Symbol data word)
open Copy (frame)

theorem any_iff_positive (bits : List Bool) : bits.any id = true ↔ 0 < Binary.value bits := by
  induction bits with
  | nil => simp [Binary.value]
  | cons bit bits hypothesis => cases bit <;> simp [Binary.value, hypothesis]

def machine : Machine (fun _ : Bool => Symbol) (Bool × Fin 3) := fun (flag, phase) symbols =>
  match phase.val with
  | 0 => if symbols false = 0 then some ((flag, 1), stationary symbols)
    else some ((flag || decide (symbols false = 2), 0),
      fun name => if name then (symbols name, none) else (symbols name, some .right))
  | 1 => if symbols false = 3 then
      some ((false, 2), fun name => if name then (data flag, none) else (symbols name, some .right))
    else some ((flag, 1), fun name => if name then (symbols name, none) else (symbols name, some .left))
  | _ => none

private theorem forward (bits : List Bool) (flag : Bool)
    (sourceLeft sourceRight flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps machine bits.length
      ((flag, 0), frame sourceLeft (word bits ++ sourceRight) flagLeft (oldFlag :: flagRight))
      ((flag || bits.any id, 0), frame ((word bits).reverse ++ sourceLeft) sourceRight flagLeft (oldFlag :: flagRight)) := by
  induction bits generalizing flag sourceLeft with
  | nil => simpa [word] using Steps.zero (machine := machine) ((flag, 0), frame sourceLeft sourceRight flagLeft (oldFlag :: flagRight))
  | cons bit bits hypothesis =>
    have nonblank : data bit ≠ 0 := by cases bit <;> decide
    have digitFlag : decide (data bit = 2) = bit := by cases bit <;> decide
    have first : step machine
        ((flag, 0), frame sourceLeft (word (bit :: bits) ++ sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag || bit, 0), frame (data bit :: sourceLeft) (word bits ++ sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_zero, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, nonblank,
        digitFlag, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    have rest := hypothesis (flag || bit) (data bit :: sourceLeft)
    simpa [word, List.reverse_cons, List.append_assoc, Bool.or_assoc] using Steps.next first rest

private theorem return_head (bits : List Bool) (current : Symbol) (notBoundary : current ≠ 3)
    (flag : Bool) (sourceLeft sourceRight flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps machine (bits.length + 2)
      ((flag, 1), frame (word bits ++ 3 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight))
      ((false, 2), frame (3 :: sourceLeft) ((word bits).reverse ++ current :: sourceRight) flagLeft (data flag :: flagRight)) := by
  induction bits generalizing current sourceRight with
  | nil =>
    have first : step machine
        ((flag, 1), frame (3 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag, 1), frame sourceLeft (3 :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have second : step machine
        ((flag, 1), frame sourceLeft (3 :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((false, 2), frame (3 :: sourceLeft) (current :: sourceRight) flagLeft (data flag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, Turing.Tape.mk'_head,
        Turing.ListBlank.head_mk, List.headI_cons, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_right_mk', Turing.ListBlank.cons_mk]
    simpa [word] using Steps.next first (Steps.next second (.zero _))
  | cons bit bits hypothesis =>
    have first : step machine
        ((flag, 1), frame (word (bit :: bits) ++ 3 :: sourceLeft) (current :: sourceRight) flagLeft (oldFlag :: flagRight)) =
        some ((flag, 1), frame (word bits ++ 3 :: sourceLeft) (data bit :: current :: sourceRight) flagLeft (oldFlag :: flagRight)) := by
      simp only [step, machine, Fin.val_one, MultiTape.read, frame, word, List.map_cons, List.cons_append,
        Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons, notBoundary, ↓reduceIte, Option.map_some]
      congr 2
      funext name
      cases name <;>
        simp [act, frame, Turing.Tape.write_mk', Turing.Tape.move_left_mk', Turing.ListBlank.cons_mk]
    have notMarker : data bit ≠ 3 := by cases bit <;> decide
    have rest := hypothesis (data bit) notMarker (current :: sourceRight)
    simpa [word, List.reverse_cons, List.append_assoc, Nat.add_assoc] using Steps.next first rest

theorem steps (bits : List Bool) (sourceLeft sourceRight flagLeft flagRight : List Symbol) (oldFlag : Symbol) :
    Steps machine (2 * bits.length + 3)
      ((false, 0), frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (oldFlag :: flagRight))
      ((false, 2), frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (data (bits.any id) :: flagRight)) := by
  have scanned := forward bits false (3 :: sourceLeft) (0 :: sourceRight) flagLeft flagRight oldFlag
  have handover : step machine
      ((bits.any id, 0), frame ((word bits).reverse ++ 3 :: sourceLeft) (0 :: sourceRight) flagLeft (oldFlag :: flagRight)) =
      some ((bits.any id, 1), frame ((word bits).reverse ++ 3 :: sourceLeft) (0 :: sourceRight) flagLeft (oldFlag :: flagRight)) := by
    simp [step, machine, MultiTape.read, frame]
  have restored := return_head bits.reverse 0 (by decide) (bits.any id) sourceLeft sourceRight flagLeft flagRight oldFlag
  simp only [Bool.false_or, word, List.map_reverse, List.reverse_reverse, List.length_reverse] at scanned handover restored ⊢
  convert scanned.trans (Steps.next handover restored) using 1; omega

-- parameterLevel: size names bounding the runtime number of counter digits.
universe parameterLevel

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (capacity : MvPolynomial Parameter ℕ) :
    Realizes machine (false, 0) (false, 2)
      (fun assignment initial => ∃ bits sourceLeft sourceRight flagLeft flagRight oldFlag,
        bits.length ≤ MvPolynomial.eval assignment capacity ∧
          initial = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (oldFlag :: flagRight))
      (fun _ initial final => ∃ bits sourceLeft sourceRight flagLeft flagRight oldFlag,
        initial = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (oldFlag :: flagRight) ∧
          final = frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (data (bits.any id) :: flagRight)) := by
  refine ⟨by intro symbols; rfl, 2 * capacity + 3, ?_⟩
  intro assignment initial valid
  obtain ⟨bits, sourceLeft, sourceRight, flagLeft, flagRight, oldFlag, fits, rfl⟩ := valid
  refine ⟨2 * bits.length + 3,
    frame (3 :: sourceLeft) (word bits ++ 0 :: sourceRight) flagLeft (data (bits.any id) :: flagRight),
    ?_, steps bits sourceLeft sourceRight flagLeft flagRight oldFlag,
    bits, sourceLeft, sourceRight, flagLeft, flagRight, oldFlag, rfl, rfl⟩
  simp only [map_add, map_mul, map_ofNat]
  omega

end Polytime2.BinaryGuard
