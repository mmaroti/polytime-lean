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

import Polytime1.SizeEvaluation

/-! # Evaluate the matrix capacity K*L+1 before frame preparation -/

namespace Polytime1.Examples.SizeEvaluation

open UnaryMachine (Symbol units fields)

abbrev context : SizeContext := ⟨Fin 2, inferInstance⟩
def ordering : context.Parameter ≃ Fin 2 := Equiv.refl _
def capacity : SizeExpression context := .add (.mul (.parameter 0) (.parameter 1)) (.constant 1)
def assignment (rows columns : ℕ) : SizeAssignment context := fun name =>
  if name = 0 then rows else columns

/-- Matrix capacity evaluation composes inside one reserved frame, preserving
both caller regions without exposing workspace or runtime polynomials. -/
theorem capacity_frame_realization :
    ∃ scratch, SizeFrame.Realizes
      [SizeExpression.parameter (ctx := context) 0, .parameter 1]
      (capacity :: scratch ++ [.parameter 0, .parameter 1]) := by
  apply SizeFrame.evaluates capacity
  intro name
  fin_cases name <;> simp

/-- The reserved-frame proof also supplies the original caller interface. -/
theorem capacity_realization :
    ∃ scratch, Polytime1.SizeEvaluation.Realizes
      [SizeExpression.parameter (ctx := context) 0, .parameter 1]
      (capacity :: scratch ++ [.parameter 0, .parameter 1]) := by
  obtain ⟨scratch, certificate⟩ := capacity_frame_realization
  exact ⟨scratch, Polytime1.SizeEvaluation.Realizes.of_frame certificate⟩

/-- A small specialized machine realizes the same capacity directly, preserving
both header fields and all following input. -/
theorem realizes_capacity (rows columns : ℕ) (tail : List Symbol) :
    ∃ ticks, ticks ≤ 256 * (rows + columns + 1) ^ 5 ∧
      UnaryMachine.Steps true ticks
        (UnaryMachine.configuration 0 [] (TupleMachine.word
          (Frame.header (Frame.values ordering (assignment rows columns))) ++ tail))
        (UnaryMachine.configuration 19 []
          (units (capacity.eval (assignment rows columns)) ++ 1 ::
            (TupleMachine.word (Frame.header (Frame.values ordering (assignment rows columns))) ++ tail))) := by
  simpa [ordering, assignment, capacity, SizeExpression.eval, Frame.values,
    ← Polytime1.SizeEvaluation.fields_header, fields, List.ofFn_succ,
    units, List.append_assoc] using UnaryMachine.realizes true rows columns tail

/-- Observe the complete returned fields and payload in a bounded machine run. -/
def execute (rows columns : ℕ) (payload : List Symbol) : Option (List Symbol) :=
  (Tape.run (UnaryMachine.machine true) (256 * (rows + columns + 1) ^ 5)
    (UnaryMachine.configuration 0 [] (fields [rows, columns] ++ payload))).map fun final =>
      (List.range ((fields [rows * columns + 1, rows, columns]).length + payload.length)).map
        final.Tape.right₀.nth

#guard execute 0 0 [7] = some (fields [1, 0, 0] ++ [7])
#guard execute 0 3 [1, 2, 7] = some (fields [1, 0, 3] ++ [1, 2, 7])
#guard execute 3 0 [] = some (fields [1, 3, 0])
#guard execute 2 3 [7, 1, 2] = some (fields [7, 2, 3] ++ [7, 1, 2])

-- Static selection can cross zero-valued parameters without losing separators.
#guard (Tape.run (SizeMachine.Copy.machine 2) 4096
    (Tape.configuration (Fin.last 2, 0) [] (fields [0, 2, 3] ++ [7]))).map
    (fun final => (List.range 13).map final.Tape.right₀.nth) =
  some (fields [3, 0, 2, 3] ++ [7])

-- Constants also work when there is no parameter header or payload.
#guard (Tape.run (SizeMachine.Constant.machine 0) 3
    (Tape.configuration (Fin.last 0, 0) [] [])).map (fun final => final.Tape.right₀.nth 0) = some 1
#guard (Tape.run SizeMachine.Addition.machine 32
    (Tape.configuration 0 [] (fields [0, 0] ++ [7]))).map
    (fun final => (List.range 2).map final.Tape.right₀.nth) = some [1, 7]

end Polytime1.Examples.SizeEvaluation
