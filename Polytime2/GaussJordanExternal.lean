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

import Polytime2.GaussJordanInput

/-! # Gauss–Jordan elimination from external binary matrix input

Compose header parsing and blank-tape preparation, the verified eliminator, and
binary serialization on one fixed collection of tapes. All data movement,
initialization, guards, arithmetic, and handovers contribute to the bound.
-/

namespace Polytime2.GaussJordanExternal

open MultiTape GaussJordanInput

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {rows columns width : ℕ}

local instance scalarInhabited : Inhabited Scalar := ⟨0⟩

def workingWiring : GaussJordanWorkspace.TapeName ↪ TapeName :=
  ⟨Sum.inr, Sum.inr_injective⟩

noncomputable def eliminate : Machine (Alphabet Scalar) GaussJordanMachine.State :=
  wire workingWiring GaussJordanMachine.machine

private theorem eliminate_steps (matrix : Matrix (Fin rows) (Fin columns) Scalar)
    (input output : Turing.Tape Binary.Symbol) :
    ∃ ticks candidate rank sourceValue targetValue coefficient,
      ticks ≤ GaussJordanMachine.bound rows columns ∧
      Steps eliminate ticks
        (GaussJordanMachine.entry, frame input output (GaussJordanWorkspace.frame matrix 0 0 0 0 0 0 0 false))
        (GaussJordanMachine.exit, frame input output (GaussJordanWorkspace.frame (GaussJordan.eliminate matrix)
          candidate 0 rank columns sourceValue targetValue coefficient false)) ∧
      candidate ≤ rows ∧ rank ≤ rows ∧
      Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧ Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) := by
  obtain ⟨ticks, candidate, rank, sourceValue, targetValue, coefficient, cost, trace, correct⟩ := GaussJordanMachine.steps matrix
  refine ⟨ticks, candidate, rank, sourceValue, targetValue, coefficient, cost, ?_, correct⟩
  apply wire_steps_of_eq workingWiring _ trace
  · intro name; rfl
  · intro name; rfl
  · intro name outside
    cases name with
    | inl name => cases name <;> rfl
    | inr name => exact False.elim (outside ⟨name, rfl⟩)

private theorem eliminate_halt (symbols : Symbols (Alphabet Scalar)) : eliminate GaussJordanMachine.exit symbols = none := by
  rfl

noncomputable def serialize (encode : Scalar → BitVec width) :
    Machine (Alphabet Scalar) (ScalarStreams.SerializeState width) :=
  wire (streamWiring true) (relabel (streamEquivalences Scalar true) (ScalarStreams.serializeMachine encode))

private theorem serialize_steps (encode : Scalar → BitVec width) (values : List Scalar)
    (input : Turing.Tape Binary.Symbol) (working : Tapes (GaussJordanWorkspace.Alphabet Scalar))
    (array : working arrayName = Turing.Tape.mk' (Turing.ListBlank.mk [some none])
      (Turing.ListBlank.mk (TableTraversal.word values ++ [none]))) :
    Steps (serialize encode) (values.length * (2 * width + 5) + 7)
      (ScalarStreams.serializeEntry width, frame input (Binary.tape [3] [0] ()) working)
      (ScalarStreams.serializeExit width, frame input (Binary.tape [3] (ScalarStreams.word encode values ++ [0]) ()) working) := by
  have trace := (ScalarStreams.serialize_steps encode values [] []).relabel
    (streamEquivalences Scalar true) (streamBlanks true)
  apply wire_steps_of_eq (streamWiring true) _ trace
  · intro name
    cases name with
    | false =>
      change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      rw [mapTape_identity]; rfl
    | true =>
      change working arrayName = Turing.Tape.map
        (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      rw [mapTape_identity]
      exact array
  · intro name
    cases name with
    | false =>
      change (_ : Turing.Tape Binary.Symbol) =
        Turing.Tape.map (⟨id, rfl⟩ : Turing.PointedMap Binary.Symbol Binary.Symbol) _
      rw [mapTape_identity]; rfl
    | true =>
      change working arrayName = Turing.Tape.map
        (⟨id, rfl⟩ : Turing.PointedMap (TableTraversal.Symbol Scalar) (TableTraversal.Symbol Scalar)) _
      rw [mapTape_identity]
      exact array
  · intro name outside
    cases name with
    | inl name => cases name with
      | false => rfl
      | true => exact False.elim (outside ⟨false, rfl⟩)
    | inr name => rfl

abbrev State (width : ℕ) :=
  Sum (Sum (GaussJordanInput.PrepareState width) GaussJordanMachine.State) (ScalarStreams.SerializeState width)

instance statesFinite (width : ℕ) : Fintype (State width) := inferInstance

noncomputable def machine (encode : Scalar → BitVec width) (decode : BitVec width → Scalar) :
    Machine (Alphabet Scalar) (State width) :=
  sequence (sequence (prepare decode) eliminate GaussJordanMachine.entry)
    (serialize encode) (ScalarStreams.serializeEntry width)

def entry (width : ℕ) : State width := .inl (.inl (prepareEntry width))
def exit (width : ℕ) : State width := .inr (ScalarStreams.serializeExit width)

def bound (width rows columns : ℕ) : ℕ :=
  2 * rows + 2 * columns + rows * columns * (width + 4) + 21 +
    GaussJordanMachine.bound rows columns + rows * columns * (2 * width + 5) + 9

/-- Complete multi-tape execution from the raw size header and canonical matrix
bits to a serialized reduced row-echelon matrix, with polynomial runtime. -/
theorem steps (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width)
    (matrix : Matrix (Fin rows) (Fin columns) Scalar) :
    ∃ ticks candidate rank sourceValue targetValue coefficient,
      ticks ≤ bound width rows columns ∧
      Steps (machine encode decode) ticks
        (entry width, initial rows columns (ScalarStreams.word encode (MatrixAccess.entries matrix)))
        (exit width, frame
          (Binary.tape ((ScalarStreams.word encode (MatrixAccess.entries matrix)).reverse ++ consumedHeader rows columns) [0] ())
          (Binary.tape [3] (ScalarStreams.word encode (MatrixAccess.entries (GaussJordan.eliminate matrix)) ++ [0]) ())
          (GaussJordanWorkspace.frame (GaussJordan.eliminate matrix) candidate 0 rank columns sourceValue targetValue coefficient false)) ∧
      candidate ≤ rows ∧ rank ≤ rows ∧
      Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧ Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix) := by
  have prepared := GaussJordanInput.prepare_steps encode decode roundtrip positive matrix
  let input := Binary.tape
    ((ScalarStreams.word encode (MatrixAccess.entries matrix)).reverse ++ consumedHeader rows columns) [0] ()
  obtain ⟨ticks, candidate, rank, sourceValue, targetValue, coefficient, cost, eliminated, correct⟩ :=
    eliminate_steps matrix input (Binary.tape [3] [0] ())
  have serialized := serialize_steps encode (MatrixAccess.entries (GaussJordan.eliminate matrix)) input
    (GaussJordanWorkspace.frame (GaussJordan.eliminate matrix) candidate 0 rank columns sourceValue targetValue coefficient false) rfl
  have first := sequence_steps _ _ GaussJordanMachine.entry prepared (prepare_halt decode) eliminated
  have complete := sequence_steps _ _ (ScalarStreams.serializeEntry width) first
    (by intro symbols; simp [MultiTape.sequence, eliminate_halt]) serialized
  simp only [MatrixAccess.entries_length] at complete
  refine ⟨_, candidate, rank, sourceValue, targetValue, coefficient, ?_, complete, correct⟩
  dsimp [bound]
  omega

theorem halt (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (symbols : Symbols (Alphabet Scalar)) : machine encode decode (exit width) symbols = none := by
  simp [machine, exit, MultiTape.sequence, serialize, wire, relabel, ScalarStreams.serialize_halt]


/-- The external algorithm has one polynomial certificate for all dimensions;
algorithm users need only supply the fixed encoding's round-trip proof. -/
theorem realizes [Fintype Scalar] (encode : Scalar → BitVec width) (decode : BitVec width → Scalar)
    (roundtrip : ∀ value, decode (encode value) = value) (positive : 0 < width) :
    Realizes (machine encode decode) (entry width) (exit width)
      (fun assignment input =>
        ∃ matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar,
          input = initial (assignment false) (assignment true) (ScalarStreams.word encode (MatrixAccess.entries matrix)))
      (fun assignment input output =>
        ∀ matrix : Matrix (Fin (assignment false)) (Fin (assignment true)) Scalar,
          input = initial (assignment false) (assignment true) (ScalarStreams.word encode (MatrixAccess.entries matrix)) →
          output (.inl true) = Binary.tape [3]
            (ScalarStreams.word encode (MatrixAccess.entries (GaussJordan.eliminate matrix)) ++ [0]) () ∧
          Matrix.RowEquivalent matrix (GaussJordan.eliminate matrix) ∧
          Matrix.IsReducedRowEchelon (GaussJordan.eliminate matrix)) := by
  let rowCount : MvPolynomial Bool ℕ := MvPolynomial.X false
  let columnCount : MvPolynomial Bool ℕ := MvPolynomial.X true
  refine ⟨halt encode decode,
    2 * rowCount + 2 * columnCount + rowCount * columnCount * MvPolynomial.C (width + 4) + 21 +
      GaussJordanMachine.runtimePolynomial + rowCount * columnCount * MvPolynomial.C (2 * width + 5) + 9, ?_⟩
  intro assignment input valid
  obtain ⟨matrix, rfl⟩ := valid
  obtain ⟨ticks, candidate, rank, sourceValue, targetValue, coefficient, cost, trace, _⟩ :=
    steps encode decode roundtrip positive matrix
  refine ⟨ticks, _, ?_, trace, ?_⟩
  · simpa only [bound, rowCount, columnCount, map_add, map_mul, map_ofNat,
      MvPolynomial.eval_X, MvPolynomial.eval_C, GaussJordanMachine.eval_runtimePolynomial] using cost
  · intro otherMatrix equal
    obtain ⟨otherTicks, otherCandidate, otherRank, otherSource, otherTarget, otherCoefficient,
      _, otherTrace, otherBounds⟩ := steps encode decode roundtrip positive otherMatrix
    rw [← equal] at otherTrace
    refine ⟨?_, otherBounds.2.2⟩
    exact congrArg (fun configuration => configuration.2 (.inl true)) (trace.final_eq otherTrace rfl rfl)

end Polytime2.GaussJordanExternal
