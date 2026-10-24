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

import Polytime2.Matrices.HermiteStageWorkspace
import Polytime2.Matrices.HermiteColumnUpdate
import Polytime2.Arrays.GuardedFold

/-! # Fixed-workspace fold updates for interleaved Hermite stages

The immutable context holds source row, incoming row, and selected column.
Each token selects an earlier row. The accumulator reuses the existing paired
matrix workspace. The enclosing traversal supplies the logical update contract.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def hermiteStageContext (rows columns : MvPolynomial Parameter ℕ) : Fin 3 → EncodedDomain Parameter
  | 0 | 1 => boundedIndex rows
  | 2 => boundedIndex columns

private def updateArguments (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :
    (integerHermiteRowStageUpdateWithin rows columns workspace).Arguments sizes
  | 0 => context 0 | 1 => context 1 | 2 => token | 3 => context 2 | 4 => state.1 | 5 => state.2

/-- The fold invariant supplies both mathematical admissibility and workspace fit. -/
def hermiteStageUpdateAllowed (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :=
  (integerHermiteRowStageUpdateWithin rows columns workspace).precondition sizes
    (updateArguments rows columns workspace sizes context state token)

/-- A total update with the fit proof supplied logically by the traversal. -/
noncomputable def hermiteStageUpdate (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :
    (hermiteColumnState rows columns workspace).Carrier sizes :=
  ArrayFold.extend (hermiteStageUpdateAllowed rows columns workspace sizes context)
    (fun state token valid => (integerHermiteRowStageUpdateWithin rows columns workspace).compute sizes
      ⟨updateArguments rows columns workspace sizes context state token, valid⟩) state token

/-- The conditional proof fallback adds no runtime bounds test under the fold contract. -/
theorem hermiteStageUpdate_realizable (rows columns workspace : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (hermiteStageContext rows columns) (boundedIndex rows) (hermiteColumnState rows columns workspace)
      (hermiteStageUpdateAllowed rows columns workspace) (hermiteStageUpdate rows columns workspace)).Realizable := by
  apply arrayFoldStep_of_partial_realizable
  let computation := arrayFoldStep (hermiteStageContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns workspace) (hermiteStageUpdateAllowed rows columns workspace)
    (hermiteStageUpdate rows columns workspace)
  exact (integerHermiteRowStageUpdateWithin_realizable rows columns workspace).onResults
    computation.inputDomains computation.precondition
    (fun name sizes arguments => updateArguments rows columns workspace sizes
      (fun original => arguments.val (.inl original)) (arguments.val (.inr false)) (arguments.val (.inr true)) name)
    (by intro sizes arguments; exact arguments.property) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains (.inl 0) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inl 1) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inr true) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inl 2) computation.precondition
      · exact (Realizable.argument computation.inputDomains (.inr false) computation.precondition).fst
      · exact (Realizable.argument computation.inputDomains (.inr false) computation.precondition).snd)

/-- Each permitted token performs exactly its singleton mathematical stage. -/
theorem hermiteStageUpdate_correct (rows columns workspace : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes)
    (valid : hermiteStageUpdateAllowed rows columns workspace sizes context state token) :
    let result := hermiteStageUpdate rows columns workspace sizes context state token
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (context 0) (context 1) (context 2) [token] state.1.val state.2.val := by
  simp only [hermiteStageUpdate, ArrayFold.extend_of_allowed valid]
  exact integerHermiteRowStageUpdateWithin_correct rows columns workspace sizes
    ⟨updateArguments rows columns workspace sizes context state token, valid⟩

/-- Selected tokens execute the stage update; unselected tokens retain the paired state. -/
noncomputable def hermiteStageSelectedUpdate (rows columns workspace : MvPolynomial Parameter ℕ) :=
  arrayFoldStep (hermiteStageContext rows columns) (booleans.prod (boundedIndex rows))
    (hermiteColumnState rows columns workspace)
    (arrayFoldGuardedAllowed (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns workspace) (hermiteStageUpdateAllowed rows columns workspace))
    (arrayFoldGuardedUpdate (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns workspace) (hermiteStageUpdate rows columns workspace))

theorem hermiteStageSelectedUpdate_realizable (rows columns workspace : MvPolynomial Parameter ℕ) :
    (hermiteStageSelectedUpdate rows columns workspace).Realizable :=
  arrayFoldGuardedUpdate_realizable (hermiteStageContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns workspace) (hermiteStageUpdateAllowed rows columns workspace)
    (hermiteStageUpdate rows columns workspace) (hermiteStageUpdate_realizable rows columns workspace)

/-- The fixed workspace contains elimination and every normalized prefix. -/
noncomputable def hermiteStageWorkspace (width : MvPolynomial Parameter ℕ) := 2 * (2 * width + 1) + 1

private def pairValues (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) := (state.1.val, state.2.val)

private def originalAllowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ) :=
  context 0 ≠ context 1 ∧ 0 < matrix (context 0) (context 2) ∧
    (∀ row column, (matrix row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, (left row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    pairValues rows columns (hermiteStageWorkspace width) sizes initial =
      IntegerMatrix.hermiteRowStep (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) (context 2) matrix left

private def initialAllowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :=
  (List.ofFn array).Nodup ∧ context 0 ∉ List.ofFn array ∧ context 1 ∉ List.ofFn array ∧
    ∃ matrix left, originalAllowed rows columns width sizes context initial matrix left

private def prefixInvariant (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (count : ℕ) (state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :=
  ∀ matrix left, originalAllowed rows columns width sizes context initial matrix left →
    pairValues rows columns (hermiteStageWorkspace width) sizes state =
      IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) (context 2)
        ((List.ofFn array).take count) matrix left

private theorem prefix_starts (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :
    prefixInvariant rows columns width length sizes context array initial 0 initial := by
  intro matrix left valid
  exact valid.2.2.2.2

private def stageNextAllowed (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (token : (boundedIndex rows).Carrier sizes) (value : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ ×
      Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ) :=
    (context 0 ≠ context 1 ∧ context 0 ≠ token ∧ token ≠ context 1 ∧ 0 < value.1 (context 0) (context 2)) ∧
    let result := IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) (context 2) [token] value.1 value.2
    (∀ row column, (result.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (result.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace)

private theorem prefix_permits (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (valid : initialAllowed rows columns width length sizes context array initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (invariant : prefixInvariant rows columns width length sizes context array initial index.val state) :
    hermiteStageUpdateAllowed rows columns (hermiteStageWorkspace width) sizes context state (array index) := by
  obtain ⟨matrix, left, original⟩ := valid.2.2.2
  have current := invariant matrix left original
  have fits := IntegerMatrix.hermiteRowStage_prefix_fits (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
    (context 0) (context 1) original.1 (context 2) (List.ofFn array) valid.1 valid.2.1 valid.2.2.1
    matrix left original.2.1 original.2.2.1 original.2.2.2.1 index.val
    (by simpa only [List.length_ofFn] using index.isLt)
  simp only [List.getElem_ofFn] at fits
  change stageNextAllowed rows columns (hermiteStageWorkspace width) sizes context (array index)
    (pairValues rows columns (hermiteStageWorkspace width) sizes state)
  rw [current]
  have capacity : MvPolynomial.eval sizes (hermiteStageWorkspace width) = 4 * MvPolynomial.eval sizes width + 3 := by
    simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]
    omega
  simpa only [stageNextAllowed, capacity] using fits

private theorem prefix_preserves (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (valid : initialAllowed rows columns width length sizes context array initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (invariant : prefixInvariant rows columns width length sizes context array initial index.val state) :
    prefixInvariant rows columns width length sizes context array initial (index.val + 1)
      (hermiteStageUpdate rows columns (hermiteStageWorkspace width) sizes context state (array index)) := by
  have permitted := prefix_permits rows columns width length sizes context array initial state valid index invariant
  have computed := hermiteStageUpdate_correct rows columns (hermiteStageWorkspace width) sizes context state (array index) permitted
  intro matrix left original
  have recurrence := IntegerMatrix.hermiteRowStage_prefix_succ (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) original.1 (context 2)
    (List.ofFn array) valid.1 valid.2.1 valid.2.2.1 matrix left original.2.1 index.val
    (by simpa only [List.length_ofFn] using index.isLt)
  simp only [List.getElem_ofFn] at recurrence
  exact computed.trans ((congrArg (fun pair => IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) (context 2)
    [array index] pair.1 pair.2) (invariant matrix left original)).trans recurrence.symm)

/-- Traverse an arbitrary admissible array of earlier rows in the derived fixed workspace. -/
noncomputable def hermiteStageController (rows columns width length : MvPolynomial Parameter ℕ) :=
  arrayFold (hermiteStageContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (hermiteStageWorkspace width)) length
    (initialAllowed rows columns width length) (hermiteStageUpdate rows columns (hermiteStageWorkspace width))

theorem hermiteStageController_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (hermiteStageController rows columns width length).Realizable := by
  apply arrayFold_realizable (hermiteStageContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (hermiteStageWorkspace width)) length
    (initialAllowed rows columns width length) (hermiteStageUpdate rows columns (hermiteStageWorkspace width))
    (hermiteStageUpdateAllowed rows columns (hermiteStageWorkspace width))
    (hermiteStageUpdate_realizable rows columns (hermiteStageWorkspace width))
    (prefixInvariant rows columns width length)
  · intro sizes context array initial _valid
    exact prefix_starts rows columns width length sizes context array initial
  · intro sizes context array initial valid index state invariant
    exact prefix_permits rows columns width length sizes context array initial state valid index invariant
  · intro sizes context array initial valid index state invariant
    exact prefix_preserves rows columns width length sizes context array initial state valid index invariant

/-- The full runtime fold agrees with the stage on every original input represented by its initial state. -/
theorem hermiteStageController_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteStageController rows columns width length).Arguments sizes //
      (hermiteStageController rows columns width length).precondition sizes arguments})
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (original : originalAllowed rows columns width sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr false)) matrix left) :
    let result := (hermiteStageController rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val (.inl 0)) (arguments.val (.inl 1)) (arguments.val (.inl 2))
      (List.ofFn (arguments.val (.inr true))) matrix left := by
  have invariant := ArrayFold.prefix_invariant
    (hermiteStageUpdate rows columns (hermiteStageWorkspace width) sizes (fun name => arguments.val (.inl name)))
    (arguments.val (.inr true)) (arguments.val (.inr false))
    (prefixInvariant rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false)))
    (prefix_starts rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false)))
    (fun index state valid => prefix_preserves rows columns width length sizes
      (fun name => arguments.val (.inl name)) (arguments.val (.inr true))
      (arguments.val (.inr false)) state arguments.property index valid)
  have takeAll : (List.ofFn (arguments.val (.inr true))).take (MvPolynomial.eval sizes length) =
      List.ofFn (arguments.val (.inr true)) := List.take_of_length_le (by simp)
  simpa only [takeAll, pairValues, hermiteStageController, arrayFold] using invariant matrix left original

private def prefixRows (rows length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes) :=
  fun index => (array index).2

private def selectionAllowed (rows columns length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes) (count : ℕ) :=
  count ≤ MvPolynomial.eval sizes length ∧ (∀ index, (array index).1 = decide (index.val < count)) ∧
    ((List.ofFn (prefixRows rows length sizes array)).take count).Nodup ∧
    context 0 ∉ (List.ofFn (prefixRows rows length sizes array)).take count ∧
    context 1 ∉ (List.ofFn (prefixRows rows length sizes array)).take count

private def selectedInitialAllowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :=
  ∃ count, selectionAllowed rows columns length sizes context array count ∧
    ∃ matrix left, originalAllowed rows columns width sizes context initial matrix left

private def selectedInvariant (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (visited : ℕ) (state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :=
  ∀ count, selectionAllowed rows columns length sizes context array count →
    ∀ matrix left, originalAllowed rows columns width sizes context initial matrix left →
      pairValues rows columns (hermiteStageWorkspace width) sizes state =
        IntegerMatrix.hermiteRowStage (Row := Fin (MvPolynomial.eval sizes rows))
          (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) (context 2)
          ((List.ofFn (prefixRows rows length sizes array)).take (min visited count)) matrix left

private theorem selected_starts (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes) :
    selectedInvariant rows columns width length sizes context array initial 0 initial := by
  intro count _selection matrix left original
  exact original.2.2.2.2

private theorem selected_permits (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (valid : selectedInitialAllowed rows columns width length sizes context array initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (invariant : selectedInvariant rows columns width length sizes context array initial index.val state) :
    arrayFoldGuardedAllowed (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns (hermiteStageWorkspace width))
      (hermiteStageUpdateAllowed rows columns (hermiteStageWorkspace width)) sizes context state (array index) := by
  intro active
  obtain ⟨count, selection, matrix, left, original⟩ := valid
  have before : index.val < count := of_decide_eq_true ((selection.2.1 index).symm.trans active)
  have current := invariant count selection matrix left original
  simp only [Nat.min_eq_left (Nat.le_of_lt before)] at current
  have fits := IntegerMatrix.hermiteRowStage_prefix_fits (Row := Fin (MvPolynomial.eval sizes rows))
    (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width)
    (context 0) (context 1) original.1 (context 2)
    ((List.ofFn (prefixRows rows length sizes array)).take count) selection.2.2.1 selection.2.2.2.1 selection.2.2.2.2
    matrix left original.2.1 original.2.2.1 original.2.2.2.1 index.val
    (by simp only [List.length_take, List.length_ofFn]; have := selection.1; omega)
  simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt before), List.getElem_take, List.getElem_ofFn] at fits
  change stageNextAllowed rows columns (hermiteStageWorkspace width) sizes context (array index).2
    (pairValues rows columns (hermiteStageWorkspace width) sizes state)
  rw [current]
  have capacity : MvPolynomial.eval sizes (hermiteStageWorkspace width) = 4 * MvPolynomial.eval sizes width + 3 := by
    simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]
    omega
  simpa only [stageNextAllowed, prefixRows, capacity] using fits

private theorem selected_preserves (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteStageContext rows columns name).Carrier sizes)
    (array : ((booleans.prod (boundedIndex rows)).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteStageWorkspace width)).Carrier sizes)
    (valid : selectedInitialAllowed rows columns width length sizes context array initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (invariant : selectedInvariant rows columns width length sizes context array initial index.val state) :
    selectedInvariant rows columns width length sizes context array initial (index.val + 1)
      (arrayFoldGuardedUpdate (hermiteStageContext rows columns) (boundedIndex rows)
        (hermiteColumnState rows columns (hermiteStageWorkspace width))
        (hermiteStageUpdate rows columns (hermiteStageWorkspace width)) sizes context state (array index)) := by
  have permitted := selected_permits rows columns width length sizes context array initial state valid index invariant
  by_cases active : (array index).1 = true
  · have computed := hermiteStageUpdate_correct rows columns (hermiteStageWorkspace width) sizes context state
      (array index).2 (permitted active)
    intro count selection matrix left original
    have before : index.val < count := of_decide_eq_true ((selection.2.1 index).symm.trans active)
    have next : index.val + 1 ≤ count := by omega
    have current := invariant count selection matrix left original
    simp only [Nat.min_eq_left (Nat.le_of_lt before)] at current
    have recurrence := IntegerMatrix.hermiteRowStage_prefix_succ (Row := Fin (MvPolynomial.eval sizes rows))
      (Column := Fin (MvPolynomial.eval sizes columns)) (context 0) (context 1) original.1 (context 2)
      ((List.ofFn (prefixRows rows length sizes array)).take count) selection.2.2.1 selection.2.2.2.1 selection.2.2.2.2
      matrix left original.2.1 index.val
      (by simp only [List.length_take, List.length_ofFn]; have := selection.1; omega)
    simp only [List.take_take, Nat.min_eq_left (Nat.le_of_lt before), Nat.min_eq_left next,
      List.getElem_take, List.getElem_ofFn, prefixRows] at recurrence
    simp only [arrayFoldGuardedUpdate, active, Nat.min_eq_left next]
    exact computed.trans ((congrArg (fun pair => IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (context 0) (context 1) (context 2) [(array index).2] pair.1 pair.2) current).trans recurrence.symm)
  · intro count selection matrix left original
    have after : count ≤ index.val := by
      by_contra notAfter
      have before : index.val < count := by omega
      exact active ((selection.2.1 index).trans (by simp only [before, decide_true]))
    have next : count ≤ index.val + 1 := by omega
    have inactive : (array index).1 = false := by
      cases equal : (show Bool from (array index).1)
      · exact equal
      · exact False.elim (active equal)
    have current := invariant count selection matrix left original
    simpa only [arrayFoldGuardedUpdate, inactive, Nat.min_eq_right after, Nat.min_eq_right next] using current

/-- Traverse fixed storage while updating only its runtime-selected prefix. -/
noncomputable def hermiteStagePrefixController (rows columns width length : MvPolynomial Parameter ℕ) :=
  arrayFold (hermiteStageContext rows columns) (booleans.prod (boundedIndex rows))
    (hermiteColumnState rows columns (hermiteStageWorkspace width)) length
    (selectedInitialAllowed rows columns width length)
    (arrayFoldGuardedUpdate (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns (hermiteStageWorkspace width))
      (hermiteStageUpdate rows columns (hermiteStageWorkspace width)))

theorem hermiteStagePrefixController_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (hermiteStagePrefixController rows columns width length).Realizable := by
  apply arrayFold_realizable (hermiteStageContext rows columns) (booleans.prod (boundedIndex rows))
    (hermiteColumnState rows columns (hermiteStageWorkspace width)) length
    (selectedInitialAllowed rows columns width length)
    (arrayFoldGuardedUpdate (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns (hermiteStageWorkspace width))
      (hermiteStageUpdate rows columns (hermiteStageWorkspace width)))
    (arrayFoldGuardedAllowed (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns (hermiteStageWorkspace width))
      (hermiteStageUpdateAllowed rows columns (hermiteStageWorkspace width)))
    (hermiteStageSelectedUpdate_realizable rows columns (hermiteStageWorkspace width))
    (selectedInvariant rows columns width length)
  · intro sizes context array initial _valid
    exact selected_starts rows columns width length sizes context array initial
  · intro sizes context array initial valid index state invariant
    exact selected_permits rows columns width length sizes context array initial state valid index invariant
  · intro sizes context array initial valid index state invariant
    exact selected_preserves rows columns width length sizes context array initial state valid index invariant

/-- Every selected prefix returns exactly its mathematical stage on the original matrices. -/
theorem hermiteStagePrefixController_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteStagePrefixController rows columns width length).Arguments sizes //
      (hermiteStagePrefixController rows columns width length).precondition sizes arguments})
    (count : ℕ) (selection : selectionAllowed rows columns length sizes
      (fun name => arguments.val (.inl name)) (arguments.val (.inr true)) count)
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (original : originalAllowed rows columns width sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr false)) matrix left) :
    let result := (hermiteStagePrefixController rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStage
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (arguments.val (.inl 0)) (arguments.val (.inl 1)) (arguments.val (.inl 2))
      ((List.ofFn (prefixRows rows length sizes (arguments.val (.inr true)))).take count) matrix left := by
  have invariant := ArrayFold.prefix_invariant
    (arrayFoldGuardedUpdate (hermiteStageContext rows columns) (boundedIndex rows)
      (hermiteColumnState rows columns (hermiteStageWorkspace width))
      (hermiteStageUpdate rows columns (hermiteStageWorkspace width)) sizes (fun name => arguments.val (.inl name)))
    (arguments.val (.inr true)) (arguments.val (.inr false))
    (selectedInvariant rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false)))
    (selected_starts rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false)))
    (fun index state valid => selected_preserves rows columns width length sizes
      (fun name => arguments.val (.inl name)) (arguments.val (.inr true))
      (arguments.val (.inr false)) state arguments.property index valid)
  simpa only [Nat.min_eq_right selection.1, pairValues, hermiteStagePrefixController, arrayFold] using
    invariant count selection matrix left original

end Polytime2.Computation.Realizable.Internal




