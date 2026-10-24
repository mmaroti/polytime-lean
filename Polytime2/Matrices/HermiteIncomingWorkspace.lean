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

import Polytime2.Matrices.HermiteIncomingStage
import Polytime2.Matrices.HermiteIncomingBounds
import Polytime2.Matrices.IntegerPairNarrow

/-! # Incoming stages within a fixed workspace

The enclosing incoming-prefix invariant proves that the next two matrices fit
the shared workspace. Compose the existing incoming stage with matrix-pair
narrowing; its logical fit premise adds no runtime test.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Extra capacity needed to hold both matrices throughout an incoming traversal. -/
noncomputable def hermiteIncomingWorkspaceExtra (width pivots : MvPolynomial Parameter ℕ) :=
  let pairWidth := (pivots + 1) * (width + (pivots + 1)) + 1
  pivots * (width + (pivots + 1) * (3 * pairWidth + 3) + 2 * pairWidth + 3)

/-- Common matrix and basis capacity, derived from the original width and pivot count. -/
noncomputable def hermiteIncomingWorkspace (width pivots : MvPolynomial Parameter ℕ) :=
  width + hermiteIncomingWorkspaceExtra width pivots

omit [Fintype Parameter] in
/-- Every incoming prefix fits the capacity derived from its original input. -/
theorem hermiteIncomingWorkspace_bound (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (count : ℕ) (within : count ≤ MvPolynomial.eval sizes pivots)
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns))
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin (MvPolynomial.eval sizes pivots), column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ MvPolynomial.eval sizes width)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ MvPolynomial.eval sizes width) :
    let result := IntegerMatrix.hermiteIncomingPrefix selectedRows pivotColumns count matrix left
    (∀ row column, (result.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteIncomingWorkspace width pivots)) ∧
    (∀ row column, (result.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteIncomingWorkspace width pivots)) := by
  simpa only [hermiteIncomingWorkspace, hermiteIncomingWorkspaceExtra, map_add, map_mul, map_one, map_ofNat] using
    IntegerMatrix.hermiteIncomingPrefix_uniform_bound (MvPolynomial.eval sizes width) count within
      selectedRows pivotColumns matrix left positive upper entryBound basisBound

/-- The stage is admissible and its exact result fits the enclosing workspace. -/
def hermiteIncomingWithinAllowed (rows columns workspace pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (hermiteIncomingStage rows columns workspace pivots).Arguments sizes) : Prop :=
  ∃ permitted : (hermiteIncomingStage rows columns workspace pivots).precondition sizes arguments,
    let result := (hermiteIncomingStage rows columns workspace pivots).compute sizes ⟨arguments, permitted⟩
    (∀ row column, (result.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (result.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace)

/-- The mathematical prefix invariant supplies admissibility and the next-state fit proof. -/
theorem hermiteIncomingWithinAllowed_of_prefix (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (hermiteIncomingStage rows columns (hermiteIncomingWorkspace width pivots) pivots).Arguments sizes)
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns))
    (selected : successorValues pivots sizes (arguments 0) = selectedRows)
    (selectedColumns : arguments 1 = (fun index => pivotColumns index))
    (matrix : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (left : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin (MvPolynomial.eval sizes pivots), column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ MvPolynomial.eval sizes width)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ MvPolynomial.eval sizes width)
    (invariant : ((arguments 3).val, (arguments 4).val) =
      IntegerMatrix.hermiteIncomingPrefix selectedRows pivotColumns (arguments 2).val matrix left) :
    hermiteIncomingWithinAllowed rows columns (hermiteIncomingWorkspace width pivots) pivots sizes arguments := by
  have permitted := hermiteIncomingStage_permitted rows columns (hermiteIncomingWorkspace width pivots)
    pivots sizes arguments selectedRows selected (by
      have unchanged := IntegerMatrix.hermiteIncomingPrefix_future_row selectedRows pivotColumns
        (arguments 2).val (arguments 2) le_rfl matrix left
      have sameEntry := congrArg₂ (fun current column => current (selectedRows (arguments 2).castSucc) column)
        (congrArg Prod.fst invariant) (congrFun selectedColumns (arguments 2))
      have restored := sameEntry.trans (congrFun unchanged.1 (pivotColumns (arguments 2)))
      exact lt_of_lt_of_eq (positive (arguments 2)) restored.symm)
  refine ⟨permitted, ?_⟩
  have recurrence := hermiteIncomingStage_prefix rows columns (hermiteIncomingWorkspace width pivots) pivots
    sizes ⟨arguments, permitted⟩ selectedRows selected matrix left (by simpa only [selectedColumns] using invariant)
  have nextBound : (arguments 2).val + 1 ≤ MvPolynomial.eval sizes pivots := (arguments 2).isLt
  have bounds := hermiteIncomingWorkspace_bound rows columns width pivots sizes ((arguments 2).val + 1)
    nextBound selectedRows pivotColumns matrix left positive upper entryBound basisBound
  dsimp only at recurrence
  simp only [selectedColumns] at recurrence
  constructor
  · intro row column
    have sameEntry := congrFun (congrFun (congrArg Prod.fst recurrence) row) column
    exact lt_of_eq_of_lt (congrArg Int.natAbs sameEntry) (bounds.1 row column)
  · intro row column
    have sameEntry := congrFun (congrFun (congrArg Prod.snd recurrence) row) column
    exact lt_of_eq_of_lt (congrArg Int.natAbs sameEntry) (bounds.2 row column)

/-- Narrow an incoming stage's result back to the enclosing controller's capacity. -/
noncomputable def hermiteIncomingStageWithin (rows columns workspace pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 5) :=
  ((hermiteIncomingStage rows columns workspace pivots).withPrecondition
    (hermiteIncomingWithinAllowed rows columns workspace pivots) (fun _ _ valid => valid.choose)).followedBy
    (integerMatrixPairNarrow rows columns rows rows (hermiteStageWorkspace workspace)
      (hermiteStageWorkspace workspace) workspace) rfl (fun _ _ valid => valid.choose_spec)

/-- Realize a fixed-workspace update by certified stage execution and narrowing. -/
theorem hermiteIncomingStageWithin_realizable (rows columns workspace pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingStageWithin rows columns workspace pivots).Realizable :=
  ((hermiteIncomingStage_realizable rows columns workspace pivots).withPrecondition
    (hermiteIncomingWithinAllowed rows columns workspace pivots) (fun _ _ valid => valid.choose)).followedBy
    (integerMatrixPairNarrow_realizable rows columns rows rows (hermiteStageWorkspace workspace)
      (hermiteStageWorkspace workspace) workspace
      (by intro sizes; simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]; omega)
      (by intro sizes; simp only [hermiteStageWorkspace, map_add, map_mul, map_ofNat, map_one]; omega)) rfl
    (fun _ _ valid => valid.choose_spec)

/-- Narrowing retains both actual stage-result matrices. -/
theorem hermiteIncomingStageWithin_correct (rows columns workspace pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingStageWithin rows columns workspace pivots).Arguments sizes //
      (hermiteIncomingStageWithin rows columns workspace pivots).precondition sizes arguments}) :
    let narrowed := (hermiteIncomingStageWithin rows columns workspace pivots).compute sizes arguments
    let result := (hermiteIncomingStage rows columns workspace pivots).compute sizes
      ⟨arguments.val, arguments.property.choose⟩
    (narrowed.1.val, narrowed.2.val) = (result.1.val, result.2.val) := rfl

end Polytime2.Computation.Realizable.Internal
