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

import Polytime2.GaussJordanExternal
import Polytime2.SparseInput
import Polytime2.TM0Input

/-! # TM0 realization from an unprepared external matrix input

The physical input contains a complete dimension header and binary matrix bits
in one fixed track, with constant framing. Other tracks start blank; all working
boundaries, counters, and scalar cells are created by the simulated program.
The output track contains the canonical binary result. Physical compaction of
this track into a standalone TM0 output word is a separate adapter.
-/

namespace Polytime2.GaussJordanExternal

open MultiTape GaussJordanInput

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {rows columns width : ℕ}

attribute [local instance] scalarInhabited

def inputWord (encode : Scalar → BitVec width) (matrix : Matrix (Fin rows) (Fin columns) Scalar) : List Binary.Symbol :=
  header rows columns ++ ScalarStreams.word encode (MatrixAccess.entries matrix) ++ [0]

def inputRows (encode : Scalar → BitVec width) (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    List (Tracks.Row (Alphabet Scalar)) :=
  Tracks.inputRows (.inl false) 3 (inputWord encode matrix).headI (inputWord encode matrix).tail

omit [Field Scalar] [DecidableEq Scalar] in
theorem inputRows_length (encode : Scalar → BitVec width) (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    (inputRows encode matrix).length = rows + columns + rows * columns * width + 4 := by
  simp only [inputRows, Tracks.inputRows_length, inputWord, List.length_tail, List.length_append,
    header, List.length_replicate, List.length_cons, List.length_nil, ScalarStreams.word_length, MatrixAccess.entries_length]
  omega

omit [Field Scalar] [DecidableEq Scalar] in
theorem inputRows_represents (encode : Scalar → BitVec width) (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    Tracks.Represents (inputRows encode matrix)
      (initial rows columns (ScalarStreams.word encode (MatrixAccess.entries matrix))) := by
  have represented := Tracks.inputRows_represents (Alphabet := Alphabet Scalar) (.inl false) 3
    (inputWord encode matrix).headI (inputWord encode matrix).tail
  convert represented using 1 <;> first | rfl | (funext name; fin_cases name <;> rfl)

omit [DecidableEq Scalar] in
theorem bitWidth_pos {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality) : 0 < Nat.clog 2 cardinality := by
  have distinct : enumeration (0 : Scalar) ≠ enumeration 1 := enumeration.injective.ne zero_ne_one
  have zeroBound := (enumeration (0 : Scalar)).isLt
  have oneBound := (enumeration (1 : Scalar)).isLt
  apply Nat.clog_pos (by decide)
  by_contra tooSmall
  apply distinct
  apply Fin.ext
  omega

/-- Standard TM0 entry from only a size header and binary matrix input. Runtime
includes preparation, elimination, serialization, and multi-tape simulation. -/
theorem realizes_tm0 [Fintype Scalar] {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality) :
    let encode := ScalarCodec.represent enumeration
    let decode := ScalarCodec.interpret enumeration 0
    let names := (Finset.univ : Finset TapeName).toList
    let program := TM0Input.machine (SingleTape.compile (Simulation.machine names (machine encode decode)))
      (.inl (Simulation.entry names (entry (Nat.clog 2 cardinality))))
    ∃ timeBound rowBound : MvPolynomial Bool ℕ,
      ∀ assignment (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar),
        ∃ ticks finalRows,
          ticks ≤ MvPolynomial.eval assignment timeBound ∧
          finalRows.length ≤ MvPolynomial.eval assignment rowBound ∧
          Tracks.RepresentsAt (.inl true) finalRows
            (Binary.tape [3] (ScalarStreams.word encode (MatrixAccess.entries (GaussJordan.eliminate matrix)) ++ [0]) ()) ∧
          Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧
          Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker :: ((inputRows encode matrix).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr (.inr ()), Sweep.tape [Sweep.leftMarker]
              (finalRows.map Sweep.row ++ [Sweep.rightMarker])))) = none := by
  intro encode decode names program
  have roundtrip : ∀ value, decode (encode value) = value := ScalarCodec.interpret_represent enumeration 0
  have positive := bitWidth_pos enumeration
  let capacity : MvPolynomial Bool ℕ := MvPolynomial.X false + MvPolynomial.X true +
    MvPolynomial.X false * MvPolynomial.X true * MvPolynomial.C (Nat.clog 2 cardinality) + 4
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes names
    (Finset.nodup_toList _) (by intro name; simp [names])
    (realizes encode decode roundtrip positive) capacity
  refine ⟨timeBound + 1, rowBound, ?_⟩
  intro assignment matrix
  obtain ⟨ticks, finalRows, final, time, storage, correct, represented, trace, stopped⟩ :=
    runs assignment (initial (assignment false) (assignment true) (ScalarStreams.word encode (MatrixAccess.entries matrix)))
      ⟨matrix, rfl⟩ (inputRows encode matrix) (inputRows_represents encode matrix) (by
        simp only [inputRows_length, capacity, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.le_refl])
  obtain ⟨output, equivalent, reduced⟩ := correct matrix rfl
  have representedOutput := represented (.inl true)
  rw [output] at representedOutput
  refine ⟨ticks + 1, finalRows, ?_, storage, representedOutput, equivalent, reduced,
    TM0Input.initialized_steps _ _ _ trace, ?_⟩
  · simp only [map_add, map_one]; omega
  · simp only [program, TM0Input.step_embed, stopped, Option.map_none]

end Polytime2.GaussJordanExternal
