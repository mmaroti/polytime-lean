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

import Polytime1.RealizationLoop
import Polytime1.UnaryMachine

/-! # A guarded unary-counter loop

The controller has four states, independent of the initial counter. It erases
one unit per body execution and halts on the zero-field separator, preserving
all following storage. No runtime iteration limit is supplied to the machine.
-/

namespace Polytime1.Examples.While

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

/-- The relational rule hides the intermediate tape and needs no exact
iteration formula or chosen scratch result. -/
theorem realizes (counter : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ (counter + 1) * 4 ∧ Tape.Steps machine ticks
      ⟨.inl (), tape counter tail⟩ ⟨.inl (), tape 0 tail⟩ ∧
      Turing.TM0.step machine ⟨.inl (), tape 0 tail⟩ = none := by
  let represented (value : ℕ) (actual : Turing.Tape Symbol) := actual = tape value tail
  obtain ⟨final, finalTape, ticks, cost, _, _, stopped, encoded, trace, halt⟩ :=
    WhileMachine.realizes_relation guard body () () 0 2 represented represented condition
      (fun _ => True) id (fun initial final => final = initial - 1) 0 2 (by intro symbol; rfl) (by intro symbol; rfl)
      (by intro value actual equal; rw [equal]; exact counter_bit value tail)
      (by intro value actual _ equal; exact ⟨0, actual, le_rfl, .zero _, equal⟩)
      (by
        intro value actual _ active equal
        subst actual
        refine ⟨value - 1, tape (value - 1) tail, 2, le_rfl, body_run value tail active, rfl, trivial, ?_, rfl⟩
        simp only [condition, decide_eq_true_eq] at active
        simp only [id_eq]
        omega)
      counter (tape counter tail) trivial rfl
  have zero : final = 0 := by simpa [condition] using stopped
  subst final
  change finalTape = tape 0 tail at encoded
  subst finalTape
  exact ⟨ticks, cost, trace, halt⟩

abbrev context : SizeContext := ⟨Unit, inferInstance⟩

/-- An arbitrary caller suffix is preserved independently of the logical counter. -/
def representation (_assignment : SizeAssignment context) (tail : List Symbol)
    (value : ℕ) (actual : Turing.Tape Symbol) : Prop := actual = tape value tail

noncomputable section CounterContract

/-- The same counter loop through the shared contract interface. Its author
supplies only the invariant and decreasing measure, not the runtime polynomial. -/
theorem contract : Realization.Realizes representation representation
    (fun assignment value => value ≤ assignment ()) (fun _ _ final => final = 0) := by
  have guardContract : Realization.Realizes representation representation
      (fun assignment value => value ≤ assignment ()) (fun _ initial final => final = initial) := by
    refine ⟨Unit, inferInstance, inferInstance, (), (), guard, 0, by intros; rfl, ?_⟩
    intro assignment tail value actual _ represented
    exact ⟨value, actual, 0, by simp, .zero _, rfl, represented⟩
  have bodyContract : Realization.Realizes representation representation
      (fun assignment value => value ≤ assignment () ∧ condition value = true)
      (fun _ initial final => final = initial - 1) := by
    refine ⟨Fin 3, inferInstance, inferInstance, 0, 2, body, SizePolynomial.constant 2, by intros; rfl, ?_⟩
    intro assignment tail value actual valid represented
    change actual = tape value tail at represented
    subst actual
    exact ⟨value - 1, tape (value - 1) tail, 2, by simp, body_run value tail valid.2, rfl, rfl⟩
  have loop := Realization.Realizes.whileLoop representation representation (fun _ => condition)
    (fun assignment value => value ≤ assignment ()) (fun _ initial final => final = initial - 1)
    (fun _ => id) guardContract bodyContract
    (by intro assignment tail value actual represented; rw [represented]; exact counter_bit value tail)
    (by intro assignment initial final bounded _ equal; omega)
    (by
      intro assignment initial final _ active equal
      simp only [condition, decide_eq_true_eq] at active
      simp only [id_eq]
      omega)
    ⟨SizePolynomial.parameter (), by intros; simpa⟩
  exact loop.consequence (by intros; assumption) (by
    intro assignment initial final _ correct
    simpa [condition] using correct.2.2)

end CounterContract

def execute (counter : ℕ) (tail : List Symbol) : Option (List Symbol) :=
  (Tape.run machine ((counter + 1) * 4) ⟨.inl (), tape counter tail⟩).map fun final =>
    (List.range (tail.length + 1)).map final.Tape.right₀.nth

#guard execute 0 [7] = some [1, 7]
#guard execute 1 [2, 1, 7] = some [1, 2, 1, 7]
#guard execute 8 [7, 2] = some [1, 7, 2]

end Polytime1.Examples.While
