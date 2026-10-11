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

import Polytime1.HeaderMoveMachine

/-! # Exchanging a traversal column with a retained pivot column

Five fixed header relocations exchange the third and fifth fields, preserving
the two row indices, the column count, and all following caller storage.
-/

namespace Polytime1.HeaderColumnSwapMachine

open UnaryMachine (Symbol fields)

/-- The five relocation controllers, with the current stage recorded by sums. -/
abbrev State := Sum (Sum (Sum (Sum (HeaderMoveMachine.State 2)
  (HeaderMoveMachine.State 3)) (HeaderMoveMachine.State 4)) (HeaderMoveMachine.State 4))
    (HeaderMoveMachine.State 4)

instance : Fintype State := inferInstance

def machine : Turing.TM0.Machine Symbol State :=
  Tape.sequence
    (Tape.sequence
      (Tape.sequence
        (Tape.sequence (HeaderMoveMachine.machine 2) (HeaderMoveMachine.machine 3) (.inl (Fin.last 3, 0)))
        (HeaderMoveMachine.machine 4) (.inl (Fin.last 4, 0)))
      (HeaderMoveMachine.machine 4) (.inl (Fin.last 4, 0)))
    (HeaderMoveMachine.machine 4) (.inl (Fin.last 4, 0))

@[simp] theorem halt (symbol : Symbol) : machine (.inr (.inr (.inr (.inr (0, 7))))) symbol = none := by
  simp [machine, Tape.sequence, HeaderMoveMachine.halt]

/-- Swap the traversal and pivot-column fields with a quadratic tape bound.
Both column values are runtime data, including zero. -/
theorem realizes (firstRow secondRow column columns pivotColumn : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ 640 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 + 4 ∧
      Tape.Steps machine ticks
        (Tape.configuration (.inl (.inl (.inl (.inl (.inl (Fin.last 2, 0)))))) []
          (fields [firstRow, secondRow, column, columns, pivotColumn] ++ tail))
        (Tape.configuration (.inr (.inr (.inr (.inr (0, 7))))) []
          (fields [firstRow, secondRow, pivotColumn, columns, column] ++ tail)) := by
  obtain ⟨firstTicks, firstCost, firstTrace⟩ := HeaderMoveMachine.realizes [firstRow, secondRow]
    [columns, pivotColumn] column tail
  obtain ⟨secondTicks, secondCost, secondTrace⟩ := HeaderMoveMachine.realizes [column, firstRow, secondRow]
    [pivotColumn] columns tail
  obtain ⟨thirdTicks, thirdCost, thirdTrace⟩ := HeaderMoveMachine.realizes [columns, column, firstRow, secondRow]
    [] pivotColumn tail
  obtain ⟨fourthTicks, fourthCost, fourthTrace⟩ := HeaderMoveMachine.realizes [pivotColumn, columns, column, firstRow]
    [] secondRow tail
  obtain ⟨fifthTicks, fifthCost, fifthTrace⟩ := HeaderMoveMachine.realizes [secondRow, pivotColumn, columns, column]
    [] firstRow tail
  let entryThree : HeaderMoveMachine.State 3 := .inl (Fin.last 3, 0)
  let entryFour : HeaderMoveMachine.State 4 := .inl (Fin.last 4, 0)
  let exitFour : HeaderMoveMachine.State 4 := .inr (.inr (.inr (0, 7)))
  let first := Tape.sequence (HeaderMoveMachine.machine 2) (HeaderMoveMachine.machine 3) entryThree
  let second := Tape.sequence first (HeaderMoveMachine.machine 4) entryFour
  let third := Tape.sequence second (HeaderMoveMachine.machine 4) entryFour
  have firstResult := Tape.sequence_steps entryThree firstTrace (HeaderMoveMachine.halt 2) secondTrace
  have firstHalt (symbol : Symbol) : first (.inr (.inr (.inr (.inr (0, 7))))) symbol = none := by
    simp [first, Tape.sequence, HeaderMoveMachine.halt]
  have secondResult := Tape.sequence_steps entryFour firstResult firstHalt thirdTrace
  have secondHalt (symbol : Symbol) : second (.inr exitFour) symbol = none := by
    simp [second, exitFour, Tape.sequence, HeaderMoveMachine.halt]
  have thirdResult := Tape.sequence_steps entryFour secondResult secondHalt fourthTrace
  have thirdHalt (symbol : Symbol) : third (.inr exitFour) symbol = none := by
    simp [third, exitFour, Tape.sequence, HeaderMoveMachine.halt]
  have result := Tape.sequence_steps entryFour thirdResult thirdHalt fifthTrace
  have boundFirst : firstTicks ≤ 128 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 := by
    simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using firstCost
  have boundSecond : secondTicks ≤ 128 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 := by
    simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using secondCost
  have boundThird : thirdTicks ≤ 128 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 := by
    simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using thirdCost
  have boundFourth : fourthTicks ≤ 128 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 := by
    simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fourthCost
  have boundFifth : fifthTicks ≤ 128 * (firstRow + secondRow + column + columns + pivotColumn + 6) ^ 2 := by
    simpa [fields, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fifthCost
  refine ⟨firstTicks + (secondTicks + 1) + (thirdTicks + 1) + (fourthTicks + 1) + (fifthTicks + 1), by omega, ?_⟩
  simpa only [machine, first, second, third, entryThree, entryFour,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    Nat.reduceAdd, Tape.configuration] using result

end Polytime1.HeaderColumnSwapMachine
