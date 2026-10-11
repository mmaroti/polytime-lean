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

import Polytime2.GaussJordanExternalTM0
import Polytime2.TrackOutput

/-! # Standalone TM0 output for Gauss–Jordan elimination

The output adapter erases all simulated tracks and boundary markers, leaving
only fixed binary letters and the physical head at the beginning of the result.
-/

namespace Polytime2.GaussJordanExternal

open MultiTape GaussJordanInput

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar]
attribute [local instance] scalarInhabited

/-- Fixed physical binary letters; no head flags or working-track data. -/
def outputLetter (bit : Bool) : Tracks.Row (Alphabet Scalar) :=
  (Tracks.inputSymbols (.inl false) (Binary.data bit), fun _ => false)

def extract : Machine (fun _ : Unit => Sweep.Alphabet (Tracks.Row (Alphabet Scalar))) (Fin 8) :=
  TrackOutput.machine (fun row => row.2 (.inl true)) (fun row => row.1 (.inl true)) outputLetter

omit [Field Scalar] [DecidableEq Scalar] in
private theorem extract_steps (rows : List (Tracks.Row (Alphabet Scalar))) (bits : List Bool)
    (represented : Tracks.RepresentsAt (.inl true) rows (Binary.tape [3] (Binary.word bits ++ [0]) ())) :
    ∃ ticks, ticks ≤ 2 * rows.length + 8 ∧ Steps (extract (Scalar := Scalar)) ticks
      (0, Sweep.tape [Sweep.leftMarker] (rows.map Sweep.row ++ [Sweep.rightMarker]))
      (7, Sweep.tape [] (TrackOutput.word outputLetter bits)) := by
  obtain ⟨before, current, after, split, unmarked, marked, _, tape⟩ := represented
  have encoded : Turing.ListBlank.mk ((current :: after).map (fun row => row.1 (.inl true))) =
      Turing.ListBlank.mk (Binary.word bits) := by
    have right := congrArg (fun tape : Turing.Tape Binary.Symbol => tape.right.cons tape.head) tape
    have blanks := TrackOutput.mk_append_blanks (Binary.word bits) 1
    have reconstruct (payload : List Binary.Symbol) :
        Turing.ListBlank.mk (payload.headI :: payload.tail) = Turing.ListBlank.mk payload := by
      cases payload with
      | nil => exact Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk [])
      | cons => rfl
    have payload := right.symm
    simp only [Binary.tape, Turing.Tape.mk', Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk,
      Turing.ListBlank.cons_mk, reconstruct] at payload
    exact payload.trans (by simpa using blanks)
  subst rows
  exact TrackOutput.steps _ _ _ before current after bits unmarked marked encoded

/-- Complete external realization: unprepared input to a standalone binary output.
All preparation, elimination, simulation, extraction, and startup costs count. -/
theorem realizes_output_tm0 [Fintype Scalar] {cardinality : ℕ} (enumeration : Scalar ≃ Fin cardinality) :
    let encode := ScalarCodec.represent enumeration
    let decode := ScalarCodec.interpret enumeration 0
    let names := (Finset.univ : Finset TapeName).toList
    let source := sequence (Simulation.machine names (machine encode decode)) (extract (Scalar := Scalar)) 0
    let program := TM0Input.machine (SingleTape.compile source)
      (.inl (.inl (Simulation.entry names (entry (Nat.clog 2 cardinality)))))
    ∃ timeBound : MvPolynomial Bool ℕ,
      ∀ assignment (matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar),
        ∃ ticks, ticks ≤ MvPolynomial.eval assignment timeBound ∧
          Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧
          Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) ∧
          (fun current => current.bind (Turing.TM0.step program))^[ticks]
            (some (Turing.TM0.init (Sweep.leftMarker :: ((inputRows encode matrix).map Sweep.row ++ [Sweep.rightMarker])))) =
            some (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
              (TrackOutput.word outputLetter (ScalarStreams.bits encode (MatrixAccess.entries (GaussJordan.eliminate matrix))))))) ∧
          Turing.TM0.step program
            (TM0Input.embed (SingleTape.configuration (.inr 7, Sweep.tape []
              (TrackOutput.word outputLetter (ScalarStreams.bits encode (MatrixAccess.entries (GaussJordan.eliminate matrix))))))) = none := by
  intro encode decode names source program
  have roundtrip : ∀ value, decode (encode value) = value := ScalarCodec.interpret_represent enumeration 0
  have positive := bitWidth_pos enumeration
  let capacity : MvPolynomial Bool ℕ := MvPolynomial.X false + MvPolynomial.X true +
    MvPolynomial.X false * MvPolynomial.X true * MvPolynomial.C (Nat.clog 2 cardinality) + 4
  obtain ⟨timeBound, rowBound, runs⟩ := Simulation.realizes_steps names
    (Finset.nodup_toList _) (by intro name; simp [names])
    (realizes encode decode roundtrip positive) capacity
  refine ⟨2 * (timeBound + 2 * rowBound + 9) + 1, ?_⟩
  intro assignment matrix
  obtain ⟨ticks, finalRows, final, time, storage, correct, represented, trace⟩ :=
    runs assignment (initial (assignment false) (assignment true) (ScalarStreams.word encode (MatrixAccess.entries matrix)))
      ⟨matrix, rfl⟩ (inputRows encode matrix) (inputRows_represents encode matrix) (by
        simp only [inputRows_length, capacity, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.le_refl])
  obtain ⟨output, equivalent, reduced⟩ := correct matrix rfl
  have representedOutput := represented (.inl true)
  rw [output, ScalarStreams.word_eq] at representedOutput
  obtain ⟨extractTicks, extractCost, extracted⟩ := extract_steps finalRows _ representedOutput
  have complete := sequence_steps (Simulation.machine names (machine encode decode)) extract 0
    trace (by intro symbols; rfl) extracted
  refine ⟨2 * (ticks + extractTicks + 1) + 1, ?_, equivalent, reduced,
    TM0Input.initialized_steps _ _ _ (SingleTape.steps source complete), ?_⟩
  · simp only [map_add, map_mul, map_ofNat, map_one]
    omega
  · apply (TM0Input.step_embed _ _ _).trans
    rw [SingleTape.halt source _ (by rfl)]
    rfl

end Polytime2.GaussJordanExternal
