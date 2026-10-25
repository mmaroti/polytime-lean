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

import Polytime2.Matrices.HermiteIncomingCoordinates
import Polytime2.Matrices.IntegerHermiteStagePrefix
import Polytime2.Matrices.HermiteIncomingMath

/-! # One runtime incoming Hermite stage

Read the source, incoming row, and column from the selected-row and pivot-column
arrays at an old-pivot position. Eliminate the incoming entry and normalize
exactly the preceding selected rows. The stage requires a positive source pivot
and a distinct prefix excluding both participating rows.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width pivots : MvPolynomial Parameter ℕ) :
    Fin 5 → EncodedDomain Parameter
  | 0 => (boundedIndex rows).arrayOfLength (pivots + 1)
  | 1 => (boundedIndex columns).arrayOfLength pivots
  | 2 => arrayPosition pivots
  | 3 => integerMatrices rows columns width
  | 4 => integerMatrices rows rows width

private noncomputable def coordinates (rows columns width pivots : MvPolynomial Parameter ℕ) :=
  (hermiteIncomingCoordinates rows columns pivots).withArguments (inputs rows columns width pivots)
    (Fin.castLEEmb (by decide : 3 ≤ 5)) (by intro name; fin_cases name <;> rfl)

private noncomputable def stageArguments (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (inputs rows columns width pivots name).Carrier sizes) :
    (integerHermiteRowStagePrefix rows columns width (pivots + 1)).Arguments sizes :=
  let prepared := (coordinates rows columns width pivots).compute sizes ⟨arguments, trivial⟩
  fun name => match name with
    | 0 => prepared.1
    | 1 => prepared.2.1
    | 2 => prepared.2.2.1
    | 3 => arguments 3
    | 4 => arguments 4
    | 5 => arguments 0
    | 6 => prepared.2.2.2

private def allowed (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (inputs rows columns width pivots name).Carrier sizes) :=
  (integerHermiteRowStagePrefix rows columns width (pivots + 1)).precondition sizes
    (stageArguments rows columns width pivots sizes arguments)

/-- Execute one old-pivot stage, deriving its coordinates and prefix internally. -/
noncomputable def hermiteIncomingStage (rows columns width pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  (integerHermiteRowStagePrefix rows columns width (pivots + 1)).onResults
    (inputs rows columns width pivots) (allowed rows columns width pivots)
    (fun name sizes arguments => stageArguments rows columns width pivots sizes arguments.val name)
    (by intro sizes arguments; exact arguments.property)

/-- Admissibility concerns only the participating rows and the preceding prefix. -/
theorem hermiteIncomingStage_precondition (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (hermiteIncomingStage rows columns width pivots).Arguments sizes) :
    (hermiteIncomingStage rows columns width pivots).precondition sizes arguments ↔
      let prepared := (hermiteIncomingCoordinates rows columns pivots).compute sizes
        ⟨(fun name => match name with | 0 => arguments 0 | 1 => arguments 1 | 2 => arguments 2), trivial⟩
      prepared.1 ≠ prepared.2.1 ∧ 0 < (arguments 3).val prepared.1 prepared.2.2.1 ∧
        ((List.ofFn (arguments 0)).take (arguments 2).val).Nodup ∧
        prepared.1 ∉ (List.ofFn (arguments 0)).take (arguments 2).val ∧
        prepared.2.1 ∉ (List.ofFn (arguments 0)).take (arguments 2).val := Iff.rfl

/-- An embedded row selection discharges all distinctness and prefix exclusions. -/
theorem hermiteIncomingStage_permitted (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (hermiteIncomingStage rows columns width pivots).Arguments sizes)
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (selected : successorValues pivots sizes (arguments 0) = selectedRows)
    (positive : 0 < (arguments 3).val (selectedRows (arguments 2).castSucc) (arguments 1 (arguments 2))) :
    (hermiteIncomingStage rows columns width pivots).precondition sizes arguments := by
  rw [hermiteIncomingStage_precondition]
  let prepared := (hermiteIncomingCoordinates rows columns pivots).compute sizes
    ⟨(fun name => match name with | 0 => arguments 0 | 1 => arguments 1 | 2 => arguments 2), trivial⟩
  have source : prepared.1 = selectedRows (arguments 2).castSucc :=
    congrFun selected (arguments 2).castSucc
  have incoming : prepared.2.1 = selectedRows (Fin.last (MvPolynomial.eval sizes pivots)) :=
    congrFun selected (Fin.last (MvPolynomial.eval sizes pivots))
  have rowList : List.ofFn (arguments 0) = List.ofFn selectedRows := by
    rw [← selected, ofFn_successorValues]
  change prepared.1 ≠ prepared.2.1 ∧ 0 < (arguments 3).val prepared.1 (arguments 1 (arguments 2)) ∧ _
  rw [source, incoming, rowList]
  refine ⟨?_, positive, (List.nodup_ofFn.mpr selectedRows.injective).take, ?_, ?_⟩
  · intro same
    have values := congrArg Fin.val (selectedRows.injective same)
    simp only [Fin.val_castSucc, Fin.val_last] at values
    exact (ne_of_lt (arguments 2).isLt) values
  all_goals
    intro member
    obtain ⟨index, bounded, same⟩ := List.mem_iff_getElem.mp member
    have before : index < (arguments 2).val := by
      exact lt_of_lt_of_le bounded (by simp only [List.length_take, List.length_ofFn]; exact Nat.min_le_left _ _)
    simp only [List.getElem_take, List.getElem_ofFn] at same
    have values := congrArg Fin.val (selectedRows.injective same)
    simp only [Fin.val_castSucc, Fin.val_last] at values
    have indexBound : (arguments 2).val < MvPolynomial.eval sizes pivots := (arguments 2).isLt
    omega

/-- Coordinate preparation and prefix normalization are composed without a new machine. -/
theorem hermiteIncomingStage_realizable (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingStage rows columns width pivots).Realizable := by
  let host := inputs rows columns width pivots
  let valid := allowed rows columns width pivots
  have prepared := ((hermiteIncomingCoordinates_realizable rows columns pivots).withArguments host
    (Fin.castLEEmb (by decide : 3 ≤ 5)) (by intro name; fin_cases name <;> rfl)).withPrecondition
    valid (by intros; trivial)
  have remaining := prepared.snd
  have lastPair := remaining.snd
  apply (integerHermiteRowStagePrefix_realizable rows columns width (pivots + 1)).onResults
  intro name
  fin_cases name
  · exact prepared.fst
  · exact remaining.fst
  · exact lastPair.fst
  · exact Realizable.argument host 3 valid
  · exact Realizable.argument host 4 valid
  · exact Realizable.argument host 0 valid
  · exact lastPair.snd

/-- The computed matrices are exactly the forward-prefix mathematical stage. -/
theorem hermiteIncomingStage_correct (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingStage rows columns width pivots).Arguments sizes //
      (hermiteIncomingStage rows columns width pivots).precondition sizes arguments}) :
    let prepared := (hermiteIncomingCoordinates rows columns pivots).compute sizes
      ⟨(fun name => match name with | 0 => arguments.val 0 | 1 => arguments.val 1 | 2 => arguments.val 2), trivial⟩
    let result := (hermiteIncomingStage rows columns width pivots).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      prepared.1 prepared.2.1 prepared.2.2.1
      ((List.ofFn (arguments.val 0)).take (arguments.val 2).val)
      (arguments.val 3).val (arguments.val 4).val := by
  exact integerHermiteRowStagePrefix_correct rows columns width (pivots + 1) sizes
    ⟨stageArguments rows columns width pivots sizes arguments.val, arguments.property⟩

/-- One runtime stage advances the mathematical incoming-prefix invariant. -/
theorem hermiteIncomingStage_prefix (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingStage rows columns width pivots).Arguments sizes //
      (hermiteIncomingStage rows columns width pivots).precondition sizes arguments})
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (selected : successorValues pivots sizes (arguments.val 0) = selectedRows)
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (invariant : ((arguments.val 3).val, (arguments.val 4).val) =
      IntegerMatrix.hermiteIncomingPrefix selectedRows (arguments.val 1) (arguments.val 2).val matrix left) :
    let result := (hermiteIncomingStage rows columns width pivots).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteIncomingPrefix selectedRows
      (arguments.val 1) ((arguments.val 2).val + 1) matrix left := by
  have computed := hermiteIncomingStage_correct rows columns width pivots sizes arguments
  dsimp only at computed ⊢
  apply computed.trans
  let prepared := (hermiteIncomingCoordinates rows columns pivots).compute sizes
    ⟨(fun name => match name with | 0 => arguments.val 0 | 1 => arguments.val 1 | 2 => arguments.val 2), trivial⟩
  have source : prepared.1 = selectedRows (arguments.val 2).castSucc :=
    congrFun selected (arguments.val 2).castSucc
  have incoming : prepared.2.1 = selectedRows (Fin.last (MvPolynomial.eval sizes pivots)) :=
    congrFun selected (Fin.last (MvPolynomial.eval sizes pivots))
  have rowList : List.ofFn (arguments.val 0) = List.ofFn selectedRows := by
    rw [← selected, ofFn_successorValues]
  change IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) prepared.1 prepared.2.1 (arguments.val 1 (arguments.val 2))
    ((List.ofFn (arguments.val 0)).take (arguments.val 2).val) (arguments.val 3).val (arguments.val 4).val = _
  rw [source, incoming, rowList]
  have moved := congrArg₂ (fun current basis => IntegerMatrix.hermiteRowStage
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    (selectedRows (arguments.val 2).castSucc) (selectedRows (Fin.last (MvPolynomial.eval sizes pivots)))
    (arguments.val 1 (arguments.val 2)) ((List.ofFn selectedRows).take (arguments.val 2).val) current basis)
    (congrArg Prod.fst invariant) (congrArg Prod.snd invariant)
  exact moved.trans (IntegerMatrix.hermiteIncomingPrefix_succ_forward
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) selectedRows (arguments.val 1)
    (arguments.val 2) matrix left).symm

end Polytime2.Computation.Realizable.Internal
