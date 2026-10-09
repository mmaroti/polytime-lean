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

import Polytime.TupleMachine

/-! # Extracting the dense output after the matrix frame delimiter

Erase the working working and delimiter, then halt at the untouched output.
Encoded bits and all counter markers preceding the delimiter differ from four.
-/

namespace Polytime.FrameExtractMachine

open TupleMachine (Symbol)

/-- Erase cells through the first delimiter four, returning at its suffix. -/
def machine : Turing.TM0.Machine Symbol (Fin 4) := fun phase symbol =>
  match phase.val with
  | 0 => some ((if symbol = 4 then 2 else 1), .write 0)
  | 1 => some (0, .move .right)
  | 2 => some (3, .move .right)
  | _ => none

/-- Extraction preserves every output bit and caller suffix and clears all
working storage to the left. The transition count is linear in that storage. -/
theorem realizes (working tail : List Symbol) (valid : ∀ symbol ∈ working, symbol ≠ 4) :
    Tape.Steps machine (2 * working.length + 2)
      (Tape.configuration 0 [] (working ++ 4 :: tail))
      (Tape.configuration 3 [] tail) := by
  induction working with
  | nil =>
    have erased := Tape.write (machine := machine) (state := 0) (nextState := 2) [] tail 4 0 (by rfl)
    have moved := Tape.move_right (machine := machine) (state := 2) (nextState := 3) [] tail 0 (by rfl)
    have blank : Tape.configuration (3 : Fin 4) [0] tail = Tape.configuration (3 : Fin 4) [] tail :=
      Tape.configuration_append_blank (Symbol := Symbol) _ [] tail
    rw [blank] at moved
    exact .next erased (.next moved (.zero _))
  | cons symbol working hypothesis =>
    have distinct := valid symbol (by simp)
    have erased := Tape.write (machine := machine) (state := 0) (nextState := 1)
      [] (working ++ 4 :: tail) symbol 0 (by simp [machine, distinct])
    have moved := Tape.move_right (machine := machine) (state := 1) (nextState := 0)
      [] (working ++ 4 :: tail) 0 (by rfl)
    have blank : Tape.configuration (0 : Fin 4) [0] (working ++ 4 :: tail) =
        Tape.configuration (0 : Fin 4) [] (working ++ 4 :: tail) :=
      Tape.configuration_append_blank (Symbol := Symbol) _ [] _
    rw [blank] at moved
    have rest := hypothesis (by intro current member; exact valid current (by simp [member]))
    have trace := Tape.Steps.next erased (Tape.Steps.next moved rest)
    simpa [Nat.mul_add, Nat.add_assoc] using trace

@[simp] theorem halt (symbol : Symbol) : machine 3 symbol = none := rfl

end Polytime.FrameExtractMachine
