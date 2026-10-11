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

import Polytime2.MatrixEntry
import Polytime2.TM0Input

/-! # Standard-machine certificate for runtime matrix access

The certificate includes address construction, access, scratch clearing, and
the polynomial-cost multi-tape simulation, starting at Mathlib's `TM0.init`.
-/

namespace Polytime2.MatrixEntry

open MultiTape

variable {Scalar : Type} {rows columns : ℕ}

theorem frame_fits (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (row : Fin rows) (column : Fin columns) (element : Scalar) :
    ∀ name, Fits (rows * columns + rows + columns + 2) (frame matrix row column 0 element name) := by
  intro name
  have rowBound := row.isLt
  have columnBound := column.isLt
  cases name with
  | inl name =>
    cases name with
    | row => exact (MatrixAddress.counter_fits 0 row.val).mono (by omega)
    | width => exact (MatrixAddress.counter_fits 0 columns).mono (by omega)
    | column => exact (MatrixAddress.counter_fits 0 column.val).mono (by omega)
    | output => exact (MatrixAddress.counter_fits 0 0).mono (by omega)
  | inr name =>
    cases name with
    | false =>
      refine ⟨[some none], TableTraversal.word (MatrixAccess.entries matrix) ++ [none], rfl, ?_⟩
      change ([some none] : List (TableTraversal.Symbol Scalar)).length +
        (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]).length ≤
        rows * columns + rows + columns + 2
      simp only [TableTraversal.word, List.length_append, List.length_cons,
        List.length_nil, List.length_map, MatrixAccess.entries_length]
      omega
    | true =>
      refine ⟨[some none], [some (some element)], rfl, ?_⟩
      change 2 ≤ rows * columns + rows + columns + 2
      omega

/-- One finite TM0 program handles all dimensions, matrices, and valid indices
for the fixed scalar carrier. Its output represents exactly the specified update
or lookup result, with all index counters retained and address scratch cleared. -/
theorem realizes_tm0 [Fintype Scalar] (write : Bool) :
    let names := (Finset.univ : Finset TapeName).toList
    let inputCapacity : MvPolynomial Bool ℕ :=
      MvPolynomial.X false * MvPolynomial.X true + MvPolynomial.X false + MvPolynomial.X true + 2
    let program := TM0Input.machine (SingleTape.compile (Simulation.machine names (machine (Scalar := Scalar) write)))
      (.inl (Simulation.entry names entry))
    ∃ timeBound rowBound : MvPolynomial Bool ℕ,
      ∀ assignment (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
        (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
        ∃ ticks finalRows, ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          Tracks.Represents finalRows
            (frame (if write then MatrixAccess.update matrix row column element else matrix)
              row column 0 (if write then element else matrix row column)) ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity)
                (frame matrix row column 0 element)).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro names inputCapacity program
  have inputFits : ∀ assignment initial,
      (∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
        (row : Fin (assignment false)) (column : Fin (assignment true)) (element : Scalar),
        initial = frame matrix row column 0 element) →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    intro assignment initial valid name
    obtain ⟨matrix, row, column, element, rfl⟩ := valid
    simpa only [inputCapacity, map_add, map_mul, map_ofNat, MvPolynomial.eval_X] using
      frame_fits matrix row column element name
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_input names
    (Finset.nodup_toList _) (by intro name; simp [names]) (realizes (Scalar := Scalar) write) inputCapacity inputFits
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment matrix row column element
  obtain ⟨ticks, finalRows, final, time, storage, correct, output, trace, halted⟩ :=
    runs assignment (frame matrix row column 0 element) ⟨matrix, row, column, element, rfl⟩
  have finalValue := correct matrix row column element rfl
  subst final
  exact ⟨ticks, finalRows, time, storage, output, trace, halted⟩

end Polytime2.MatrixEntry
