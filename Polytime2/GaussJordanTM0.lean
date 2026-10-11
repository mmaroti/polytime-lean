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


import Polytime2.GaussJordanMachine
import Polytime2.TM0Input

/-! # Standard-machine certificate for prepared Gauss–Jordan elimination

The finite TM0 simulator charges every guard, field operation, counter operation,
and simulated head movement. Input preparation and output serialization are
separate obligations: this certificate starts with the canonical track frame.
-/

namespace Polytime2.GaussJordanMachine

open MultiTape GaussJordanWorkspace

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {rows columns : ℕ}

omit [DecidableEq Scalar] in
theorem frame_fits (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    ∀ name, Fits (rows * columns + rows + columns + 2)
      (frame matrix 0 0 0 0 0 0 0 false name) := by
  intro name
  cases name with
  | inl name =>
    cases name with
    | inl name => cases name with
      | inl name => cases name with
        | row => exact (MatrixAddress.counter_fits 0 0).mono (by omega)
        | width => exact (MatrixAddress.counter_fits 0 columns).mono (by omega)
        | column => exact (MatrixAddress.counter_fits 0 0).mono (by omega)
        | output => exact (MatrixAddress.counter_fits 0 0).mono (by omega)
      | inr name => cases name with
        | false =>
          refine ⟨[some none], TableTraversal.word (MatrixAccess.entries matrix) ++ [none], rfl, ?_⟩
          change ([some none] : List (TableTraversal.Symbol Scalar)).length +
            (TableTraversal.word (MatrixAccess.entries matrix) ++ [none]).length ≤
              rows * columns + rows + columns + 2
          simp only [TableTraversal.word, List.length_append, List.length_cons,
            List.length_nil, List.length_map, MatrixAccess.entries_length]
          omega
        | true =>
          refine ⟨[some none], [some (some (0 : Scalar))], rfl, ?_⟩
          change 2 ≤ rows * columns + rows + columns + 2
          omega
    | inr name => cases name with
      | inl name => cases name with
        | false => exact (MatrixAddress.counter_fits 0 0).mono (by omega)
        | true =>
          refine ⟨[(3 : Binary.Symbol)], [Binary.data false], rfl, ?_⟩
          change 2 ≤ rows * columns + rows + columns + 2
          omega
      | inr name =>
        refine ⟨[some none], [some (some (if name then (0 : Scalar) else 0))], ?_, ?_⟩
        · cases name <;> rfl
        · change 2 ≤ rows * columns + rows + columns + 2
          omega

  | inr name => cases name <;> exact (MatrixAddress.counter_fits 0 _).mono (by omega)

/-- A fixed finite TM0 program computes reduced row-echelon form from a
prepared input, with polynomial runtime and output storage for all dimensions. -/
theorem realizes_tm0 [Fintype Scalar] :
    let names := (Finset.univ : Finset TapeName).toList
    let inputCapacity : MvPolynomial Bool ℕ :=
      MvPolynomial.X false * MvPolynomial.X true + MvPolynomial.X false + MvPolynomial.X true + 2
    let program := TM0Input.machine
      (SingleTape.compile (Simulation.machine names (machine (Scalar := Scalar))))
      (.inl (Simulation.entry names entry))
    ∃ timeBound rowBound : MvPolynomial Bool ℕ,
      ∀ assignment (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar),
        ∃ ticks finalRows candidate rank sourceValue targetValue coefficient,
          ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          candidate ≤ assignment false ∧ rank ≤ assignment false ∧
          Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧
          Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) ∧
          Tracks.Represents finalRows
            (frame (GaussJordan.eliminate matrix) candidate 0 rank (assignment true)
              sourceValue targetValue coefficient false) ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity)
                (frame matrix 0 0 0 0 0 0 0 false)).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro names inputCapacity program
  have inputFits : ∀ assignment initial,
      (∃ matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar,
        initial = frame matrix 0 0 0 0 0 0 0 false) →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    intro assignment initial valid name
    obtain ⟨matrix, rfl⟩ := valid
    simpa only [inputCapacity, map_add, map_mul, map_ofNat, MvPolynomial.eval_X] using frame_fits matrix name
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_input names
    (Finset.nodup_toList _) (by intro name; simp [names])
    (realizes (Scalar := Scalar)) inputCapacity inputFits
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment matrix
  obtain ⟨ticks, finalRows, final, time, storage, correct, output, trace, halted⟩ :=
    runs assignment (frame matrix 0 0 0 0 0 0 0 false) ⟨matrix, rfl⟩
  obtain ⟨candidate, rank, sourceValue, targetValue, coefficient, finalValue, candidateBound, rankBound,
    equivalent, reduced⟩ := correct matrix rfl
  subst final
  exact ⟨ticks, finalRows, candidate, rank, sourceValue, targetValue, coefficient, time, storage,
    candidateBound, rankBound, equivalent, reduced, output, trace, halted⟩

end Polytime2.GaussJordanMachine
