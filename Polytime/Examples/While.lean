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

import Polytime.WhileMachine
import Polytime.UnaryMachine

/-! # A guarded unary-counter loop

The controller has four states, independent of the initial counter. It erases
one unit per body execution and halts on the zero-field separator, preserving
all following storage. No runtime iteration limit is supplied to the machine.
-/

namespace Polytime.Examples.While

open UnaryMachine (Symbol units)

def guard : Turing.TM0.Machine Symbol Unit := fun _ _ => none

def body : Turing.TM0.Machine Symbol (Fin 3) := fun phase _ =>
  match phase.val with
  | 0 => some (1, .write 0)
  | 1 => some (2, .move .right)
  | _ => none

def machine := WhileMachine.machine guard body () 0

private def tape (counter : ℕ) (tail : List Symbol) : Turing.Tape Symbol :=
  (Tape.configuration () [] (units counter ++ 1 :: tail)).Tape

private def condition (counter : ℕ) : Bool := decide (0 < counter)

private theorem counter_bit (counter : ℕ) (tail : List Symbol) :
    (tape counter tail).head = TupleMachine.data (condition counter) := by
  cases counter <;> simp [tape, condition, units, Tape.configuration, Turing.Tape.mk',
    Turing.ListBlank.head_mk, TupleMachine.data, List.replicate_succ]

private theorem body_run (counter : ℕ) (tail : List Symbol) (positive : condition counter = true) :
    Tape.Steps body 2 ⟨0, tape counter tail⟩ ⟨2, tape (counter - 1) tail⟩ := by
  cases counter with
  | zero => simp [condition] at positive
  | succ counter =>
    have write := Tape.write (machine := body) (state := 0) (nextState := 1)
      [] (units counter ++ 1 :: tail) 2 0 (by rfl)
    have move := Tape.move_right (machine := body) (state := 1) (nextState := 2)
      [] (units counter ++ 1 :: tail) 0 (by rfl)
    have trace := Tape.Steps.next write (Tape.Steps.next move (.zero _))
    have padding : Tape.configuration (2 : Fin 3) [0] (units counter ++ 1 :: tail) =
        Tape.configuration (2 : Fin 3) [] (units counter ++ 1 :: tail) := by
      simpa [TupleMachine.instInhabitedSymbol] using
        Tape.configuration_append_blank (2 : Fin 3) [] (units counter ++ 1 :: tail)
    rw [padding] at trace
    simpa [tape, Tape.configuration, units, List.replicate_succ] using trace

private theorem iterate_decrement (counter iterations : ℕ) :
    (fun value : ℕ => value - 1)^[iterations] counter = counter - iterations := by
  induction iterations generalizing counter with
  | zero => simp
  | succ iterations hypothesis =>
    rw [Function.iterate_succ_apply, hypothesis]
    omega

/-- The generic while rule gives an actual finite-machine runtime bound. -/
theorem realizes (counter : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ (counter + 1) * 4 ∧ Tape.Steps machine ticks
      ⟨.inl (), tape counter tail⟩ ⟨.inl (), tape 0 tail⟩ ∧
      Turing.TM0.step machine ⟨.inl (), tape 0 tail⟩ = none := by
  have result := WhileMachine.realizes guard body () () 0 2
    (fun value => tape value tail) (fun value => tape value tail) condition
    (fun value => value - 1) (fun _ => True) 0 2
    (by intro symbol; rfl) (by intro symbol; rfl)
    (by intro value _; exact counter_bit value tail)
    (by intro value _ _; trivial)
    (by intro value _; exact ⟨0, le_rfl, .zero _⟩)
    (by intro value _ positive; exact ⟨2, le_rfl, body_run value tail positive⟩)
    counter trivial counter
    (by intro index earlier; simp [iterate_decrement, condition, earlier])
    (by simp [iterate_decrement, condition])
  simpa [machine, iterate_decrement] using result

def execute (counter : ℕ) (tail : List Symbol) : Option (List Symbol) :=
  (Tape.run machine ((counter + 1) * 4) ⟨.inl (), tape counter tail⟩).map fun final =>
    (List.range (tail.length + 1)).map final.Tape.right₀.nth

#guard execute 0 [7] = some [1, 7]
#guard execute 1 [2, 1, 7] = some [1, 2, 1, 7]
#guard execute 8 [7, 2] = some [1, 7, 2]

end Polytime.Examples.While
