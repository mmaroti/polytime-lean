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


import Polytime2.MatrixRows
import Polytime2.TM0Input

/-! # Standard-machine certificate for complete matrix-row operations

Address construction, scalar operations, all loop guards, counter restoration,
and the polynomial-cost multi-tape simulation are charged to actual TM0 steps.
-/

namespace Polytime2.MatrixRows

open MultiTape

variable {Scalar : Type} {rows columns : ℕ}

theorem frame_fits (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (source target : Fin rows) (sourceValue targetValue coefficient : Scalar) (flag : Bool) :
    ∀ name, Fits (rows * columns + rows + columns + 2)
      (frame matrix source.val target.val 0 sourceValue targetValue coefficient flag name) := by
  intro name
  have sourceBound := source.isLt
  have targetBound := target.isLt
  cases name with
  | inl name => cases name with
    | inl name => cases name with
      | row => exact (MatrixAddress.counter_fits 0 target.val).mono (by omega)
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
        refine ⟨[some none], [some (some targetValue)], rfl, ?_⟩
        change 2 ≤ rows * columns + rows + columns + 2
        omega
  | inr name => cases name with
    | inl name => cases name with
      | false => exact (MatrixAddress.counter_fits 0 source.val).mono (by omega)
      | true =>
        refine ⟨[(3 : Binary.Symbol)], [Binary.data flag], rfl, ?_⟩
        change 2 ≤ rows * columns + rows + columns + 2
        omega
    | inr name =>
      refine ⟨[some none], [some (some (if name then coefficient else sourceValue))], ?_, ?_⟩
      · cases name <;> rfl
      · change 2 ≤ rows * columns + rows + columns + 2
        omega

/-- One finite TM0 program performs the fixed row operation for all dimensions
and runtime coefficients, preserving the matrix outside the specified rows. -/
theorem realizes_tm0 [Zero Scalar] [Fintype Scalar]
    (writeSource : Bool) (operation : Scalar → Scalar → Scalar → Scalar × Scalar) :
    let names := (Finset.univ : Finset TapeName).toList
    let inputCapacity : MvPolynomial Bool ℕ :=
      MvPolynomial.X false * MvPolynomial.X true + MvPolynomial.X false + MvPolynomial.X true + 2
    let program := TM0Input.machine
      (SingleTape.compile (Simulation.machine names (machine (Scalar := Scalar) writeSource operation)))
      (.inl (Simulation.entry names entry))
    ∃ timeBound rowBound : MvPolynomial Bool ℕ,
      ∀ assignment (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
        (source target : Fin (assignment false)) (sourceValue targetValue coefficient : Scalar) (flag : Bool),
        ∃ ticks finalRows finalSource finalTarget,
          ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          Tracks.Represents finalRows
            (frame (transform writeSource operation coefficient matrix source target)
              source.val target.val 0 finalSource finalTarget coefficient false) ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker ::
              ((Tracks.initialRows (MvPolynomial.eval assignment inputCapacity)
                (frame matrix source.val target.val 0 sourceValue targetValue coefficient flag)).map Sweep.row ++
                  [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro names inputCapacity program
  have inputFits : ∀ assignment initial,
      (∃ (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar)
        (source target : Fin (assignment false)) (sourceValue targetValue coefficient : Scalar) (flag : Bool),
        initial = frame matrix source.val target.val 0 sourceValue targetValue coefficient flag) →
      ∀ name, Fits (MvPolynomial.eval assignment inputCapacity) (initial name) := by
    intro assignment initial valid name
    obtain ⟨matrix, source, target, sourceValue, targetValue, coefficient, flag, rfl⟩ := valid
    simpa only [inputCapacity, map_add, map_mul, map_ofNat, MvPolynomial.eval_X] using
      frame_fits matrix source target sourceValue targetValue coefficient flag name
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_input names
    (Finset.nodup_toList _) (by intro name; simp [names])
    (realizes (Scalar := Scalar) writeSource operation) inputCapacity inputFits
  refine ⟨timeBound, rowBound, ?_⟩
  intro assignment matrix source target sourceValue targetValue coefficient flag
  obtain ⟨ticks, finalRows, final, time, storage, correct, output, trace, halted⟩ :=
    runs assignment (frame matrix source.val target.val 0 sourceValue targetValue coefficient flag)
      ⟨matrix, source, target, sourceValue, targetValue, coefficient, flag, rfl⟩
  obtain ⟨finalSource, finalTarget, finalValue⟩ := correct matrix source target sourceValue targetValue coefficient flag rfl
  subst final
  exact ⟨ticks, finalRows, finalSource, finalTarget, time, storage, output, trace, halted⟩

end Polytime2.MatrixRows
