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

import Polytime2.Matrices.HermiteProcessedMath

/-! # A mathematical outer row-normalization traversal

Process input rows in their original order. The state retains the actual matrix
and unimodular left basis, together with active row and pivot-column embeddings.
Each step either keeps the rank or appends the incoming row and its new pivot.
The invariant records the normalized pivot block, processed zero rows, and basis
support on processed inputs. Pivot reordering and alternating row/column sweeps
are separate from this traversal.
-/

namespace Polytime2.IntegerMatrix

/-- Ordinary matrices and dependent finite embeddings describe the row-normalization state. -/
abbrev HermiteRowState (rows columns : ℕ) :=
  (Matrix (Fin rows) (Fin columns) ℤ × Matrix (Fin rows) (Fin rows) ℤ) ×
    (Σ rank : ℕ, (Fin rank ↪ Fin rows) × (Fin rank ↪ Fin columns))

/-- Mathematical invariants after processing precisely the first `processed` input rows. -/
def HermiteRowPrefix {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (processed : ℕ) (state : HermiteRowState rows columns) : Prop :=
  let matrix := state.1.1
  let left := state.1.2
  let activeRows := state.2.2.1
  let pivotColumns := state.2.2.2
  left * original = matrix ∧ IsUnit left.det ∧
    (∀ index, (activeRows index).val < processed) ∧
    (∀ row : Fin rows, row.val < processed → row ∉ Set.range activeRows → matrix row = 0) ∧
    (matrix.submatrix activeRows pivotColumns).IsUpperTriangular ∧
    (∀ index, 0 < matrix (activeRows index) (pivotColumns index)) ∧
    (∀ row column, row < column →
      0 ≤ matrix (activeRows row) (pivotColumns column) ∧
        matrix (activeRows row) (pivotColumns column) < matrix (activeRows column) (pivotColumns column)) ∧
    (∀ row : Fin rows, row.val < processed →
      ∀ column : Fin rows, processed ≤ column.val → left row column = 0) ∧
    (∀ row : Fin rows, processed ≤ row.val → left row = (1 : Matrix (Fin rows) (Fin rows) ℤ) row)

/-- Future input rows retain their original mathematical values. -/
theorem HermiteRowPrefix.future_row {rows columns processed : ℕ}
    {original : Matrix (Fin rows) (Fin columns) ℤ} {state : HermiteRowState rows columns}
    (invariant : HermiteRowPrefix original processed state) (row : Fin rows) (after : processed ≤ row.val) :
    state.1.1 row = original row := by
  obtain ⟨equation, _, _, _, _, _, _, _, future⟩ := invariant
  calc
    state.1.1 row = (state.1.2 * original) row := congrArg (fun matrix => matrix row) equation.symm
    _ = ((1 : Matrix (Fin rows) (Fin rows) ℤ) * original) row := by
      funext column
      simp only [Matrix.mul_apply, future row after]
    _ = original row := by rw [Matrix.one_mul]

/-- The empty prefix has rank zero and the identity left transformation. -/
def hermiteRowInitial {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    {state : HermiteRowState rows columns // HermiteRowPrefix original 0 state} := by
  let noRows : Fin 0 ↪ Fin rows := ⟨Fin.elim0, by intro index; exact index.elim0⟩
  let noColumns : Fin 0 ↪ Fin columns := ⟨Fin.elim0, by intro index; exact index.elim0⟩
  refine ⟨((original, 1), ⟨0, noRows, noColumns⟩), ?_⟩
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro index; exact index.elim0
  · intro row before; omega
  · intro row; exact row.elim0
  · intro index; exact index.elim0
  · intro row; exact row.elim0
  · intro row before; omega
  · intro row after; rfl

/-- Insert the next input row, carrying all prefix invariants through either rank outcome. -/
def hermiteRowAdvance {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) (processed : Fin rows)
    (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state}) :
    {state : HermiteRowState rows columns // HermiteRowPrefix original (processed.val + 1) state} := by
  rcases state with ⟨⟨⟨matrix, left⟩, rank, activeRows, pivotColumns⟩, invariant⟩
  obtain ⟨equation, unit, oldRows, support, upper, positive, reduced, basisSupport, future⟩ := invariant
  have excluded : processed ∉ Set.range activeRows := by
    rintro ⟨index, same⟩
    have before := oldRows index
    rw [same] at before
    exact (lt_irrefl _ before)
  let selected := Fin.Embedding.snoc activeRows excluded
  let inserted := hermiteInsertRow selected pivotColumns matrix left
  have selectedOld : ∀ index : Fin rank, (selected index.castSucc).val < processed.val := by
    simpa only [selected, Fin.Embedding.snoc_castSucc] using oldRows
  have selectedLast : (selected (Fin.last rank)).val = processed.val := by
    simp only [selected, Fin.Embedding.snoc_last]
  have selectedPositive : ∀ index, 0 < matrix (selected index.castSucc) (pivotColumns index) := by
    simpa only [selected, Fin.Embedding.snoc_castSucc] using positive
  have selectedUpper : ∀ row column : Fin rank, column < row →
      matrix (selected row.castSucc) (pivotColumns column) = 0 := by
    intro row column below
    simpa only [selected, Fin.Embedding.snoc_castSucc, Matrix.submatrix_apply] using upper below
  have selectedSupport : ∀ row : Fin rows, row.val < processed.val →
      row ∉ Set.range (Fin.Embedding.init selected) → matrix row = 0 := by
    simpa only [selected, Fin.Embedding.init_snoc] using support
  have preserved := hermiteInsertRow_preserves selected pivotColumns matrix original left 1
    (by simpa only [Matrix.mul_one] using equation) unit
  have newBasis := hermiteInsertRow_processed_basis selected pivotColumns selectedOld selectedLast
    matrix left basisSupport future
  let next : {indices : (Σ rank : ℕ, (Fin rank ↪ Fin rows) × (Fin rank ↪ Fin columns)) //
      HermiteRowPrefix original (processed.val + 1) (inserted.1, indices)} :=
    match found : inserted.2 with
    | none => by
      have normalized := hermiteInsertRow_normalized_none selected pivotColumns matrix left selectedPositive selectedUpper found
      have newSupport := hermiteInsertRow_processed_support_none selected pivotColumns selectedLast matrix left selectedSupport found
      refine ⟨⟨rank, activeRows, pivotColumns⟩, ?_⟩
      refine ⟨?_, preserved.2, (fun index => Nat.lt_succ_of_lt (oldRows index)), ?_, ?_, ?_, ?_, newBasis.1, newBasis.2⟩
      · simpa only [Matrix.mul_one] using preserved.1
      · simpa only [selected, Fin.Embedding.init_snoc] using newSupport
      · simpa only [selected, Fin.Embedding.snoc_castSucc] using normalized.1
      · simpa only [selected, Fin.Embedding.snoc_castSucc] using normalized.2.1
      · simpa only [selected, Fin.Embedding.snoc_castSucc] using normalized.2.2
    | some column => by
      have normalized := hermiteInsertRow_normalized_some selected pivotColumns matrix left selectedPositive selectedUpper column found
      let newColumns := Fin.Embedding.snoc pivotColumns normalized.1
      have newSupport := hermiteInsertRow_processed_support selected pivotColumns selectedLast matrix left selectedSupport
      refine ⟨⟨rank + 1, selected, newColumns⟩, ?_⟩
      refine ⟨?_, preserved.2, ?_, newSupport, ?_, ?_, ?_, newBasis.1, newBasis.2⟩
      · simpa only [Matrix.mul_one] using preserved.1
      · intro index
        cases index using Fin.lastCases
        · rw [selectedLast]; omega
        · exact Nat.lt_succ_of_lt (selectedOld _)
      · simpa only [newColumns, Fin.Embedding.coe_snoc] using normalized.2.1
      · simpa only [newColumns, Fin.Embedding.coe_snoc] using normalized.2.2.1
      · simpa only [newColumns, Fin.Embedding.coe_snoc] using normalized.2.2.2
  exact ⟨(inserted.1, next.val), next.property⟩

/-- The proof-carrying advance returns exactly the matrix pair computed by insertion. -/
theorem hermiteRowAdvance_pair {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (processed : Fin rows) (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state})
    (excluded : processed ∉ Set.range state.val.2.2.1) :
    (hermiteRowAdvance original processed state).val.1 =
      (hermiteInsertRow (Fin.Embedding.snoc state.val.2.2.1 excluded) state.val.2.2.2 state.val.1.1 state.val.1.2).1 := by
  rcases state with ⟨⟨⟨matrix, left⟩, rank, activeRows, pivotColumns⟩, invariant⟩
  rfl

/-- A dependent outer transition retains the old rank and pivot embeddings. -/
theorem hermiteRowAdvance_selection_none {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (processed : Fin rows) (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state})
    (excluded : processed ∉ Set.range state.val.2.2.1)
    (found : (hermiteInsertRow (Fin.Embedding.snoc state.val.2.2.1 excluded)
      state.val.2.2.2 state.val.1.1 state.val.1.2).2 = none) :
    (hermiteRowAdvance original processed state).val.2 = state.val.2 := by
  rcases state with ⟨⟨⟨matrix, left⟩, rank, activeRows, pivotColumns⟩, invariant⟩
  dsimp only [hermiteRowAdvance]
  split
  · rfl
  · rename_i column present
    have impossible := found.symm.trans present
    contradiction

/-- An independent outer transition appends exactly the incoming row and new column. -/
theorem hermiteRowAdvance_selection_some {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ)
    (processed : Fin rows) (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state})
    (excluded : processed ∉ Set.range state.val.2.2.1) (column : Fin columns)
    (newColumn : column ∉ Set.range state.val.2.2.2)
    (found : (hermiteInsertRow (Fin.Embedding.snoc state.val.2.2.1 excluded)
      state.val.2.2.2 state.val.1.1 state.val.1.2).2 = some column) :
    (hermiteRowAdvance original processed state).val.2 =
      ⟨state.val.2.1 + 1, Fin.Embedding.snoc state.val.2.2.1 excluded,
        Fin.Embedding.snoc state.val.2.2.2 newColumn⟩ := by
  rcases state with ⟨⟨⟨matrix, left⟩, rank, activeRows, pivotColumns⟩, invariant⟩
  dsimp only [hermiteRowAdvance]
  split
  · rename_i absent
    have impossible := absent.symm.trans found
    contradiction
  · rename_i selected present
    have same : selected = column := Option.some.inj (present.symm.trans found)
    subst column
    rfl

/-- Iterate insertion through a bounded input-row prefix; logical invariants are proof fields. -/
def hermiteRowsPrefix {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    (processed : ℕ) → processed ≤ rows →
      {state : HermiteRowState rows columns // HermiteRowPrefix original processed state}
  | 0, _ => hermiteRowInitial original
  | processed + 1, within =>
    hermiteRowAdvance original ⟨processed, by omega⟩ (hermiteRowsPrefix original processed (by omega))

/-- The complete mathematical row traversal returns its actual basis and normalized active block. -/
def hermiteRowsSweep {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    HermiteRowState rows columns := (hermiteRowsPrefix original rows (by rfl)).val

theorem hermiteRowsSweep_correct {rows columns : ℕ} (original : Matrix (Fin rows) (Fin columns) ℤ) :
    HermiteRowPrefix original rows (hermiteRowsSweep original) := (hermiteRowsPrefix original rows (by rfl)).property

/-- Equal finite dimensions and input entries preserve the sweep's rank and
both actual output matrices, independently of index proof representations. -/
theorem hermiteRowsSweep_congr {firstRows secondRows firstColumns secondColumns : ℕ}
    (rowsEqual : firstRows = secondRows) (columnsEqual : firstColumns = secondColumns)
    (firstMatrix : Matrix (Fin firstRows) (Fin firstColumns) ℤ)
    (secondMatrix : Matrix (Fin secondRows) (Fin secondColumns) ℤ)
    (entries : ∀ (firstRow : Fin firstRows) (secondRow : Fin secondRows)
      (firstColumn : Fin firstColumns) (secondColumn : Fin secondColumns),
      firstRow.val = secondRow.val → firstColumn.val = secondColumn.val →
      firstMatrix firstRow firstColumn = secondMatrix secondRow secondColumn) :
    (hermiteRowsSweep firstMatrix).2.1 = (hermiteRowsSweep secondMatrix).2.1 ∧
    (∀ (firstRow : Fin firstRows) (secondRow : Fin secondRows)
      (firstColumn : Fin firstColumns) (secondColumn : Fin secondColumns),
      firstRow.val = secondRow.val → firstColumn.val = secondColumn.val →
      (hermiteRowsSweep firstMatrix).1.1 firstRow firstColumn =
        (hermiteRowsSweep secondMatrix).1.1 secondRow secondColumn) ∧
    (∀ (firstRow : Fin firstRows) (secondRow : Fin secondRows)
      (firstColumn : Fin firstRows) (secondColumn : Fin secondRows),
      firstRow.val = secondRow.val → firstColumn.val = secondColumn.val →
      (hermiteRowsSweep firstMatrix).1.2 firstRow firstColumn =
        (hermiteRowsSweep secondMatrix).1.2 secondRow secondColumn) := by
  subst secondRows
  subst secondColumns
  have equal : firstMatrix = secondMatrix := by
    ext row column
    exact entries row row column column rfl rfl
  subst secondMatrix
  refine ⟨rfl, ?_, ?_⟩
  all_goals
    intro firstRow secondRow firstColumn secondColumn rowValues columnValues
    have rowEqual := Fin.ext rowValues
    have columnEqual := Fin.ext columnValues
    subst secondRow
    subst secondColumn
    rfl

/-- The dependent active embeddings bound the mathematical rank by both matrix dimensions. -/
theorem hermiteRowState_rank_le {rows columns : ℕ} (state : HermiteRowState rows columns) :
    state.2.1 ≤ rows ∧ state.2.1 ≤ columns := by
  constructor
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective state.2.2.1 state.2.2.1.injective
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective state.2.2.2 state.2.2.2.injective

/-- Every valid outer prefix has a matrix-width bound in the original input sizes. -/
theorem hermiteRowPrefix_matrix_bound {rows columns : ℕ} (width processed : ℕ) (within : processed ≤ rows)
    (original : Matrix (Fin rows) (Fin columns) ℤ) (state : HermiteRowState rows columns)
    (invariant : HermiteRowPrefix original processed state)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ row column, (state.1.1 row column).natAbs <
      2 ^ (2 * (rows * (width + rows) + 1) + width + 2 * rows + 2) := by
  have futureRows := invariant.future_row
  obtain ⟨equation, unit, oldRows, support, upper, positive, reduced, basisSupport, future⟩ := invariant
  let active : Fin state.2.1 ↪ Fin processed := ⟨fun index => ⟨(state.2.2.1 index).val, oldRows index⟩, by
    intro first second same
    have values := congrArg Fin.val same
    apply state.2.2.1.injective
    exact Fin.ext values⟩
  have activeEq (index) : Fin.castLE within (active index) = state.2.2.1 index := Fin.ext rfl
  have processedSupport : ∀ row : Fin processed, row ∉ Set.range active →
      ∀ column, state.1.1 (Fin.castLE within row) column = 0 := by
    intro row outside column
    have notActive : Fin.castLE within row ∉ Set.range state.2.2.1 := by
      rintro ⟨index, same⟩
      apply outside
      refine ⟨index, ?_⟩
      have values := congrArg Fin.val same
      exact Fin.ext values
    exact congrFun (support _ row.isLt notActive) column
  have processedBound := normalized_processed_rows_bound width within active state.2.2.2 original state.1.1 state.1.2
    equation unit basisSupport future processedSupport
    (by simpa only [activeEq] using upper) (by simpa only [activeEq] using positive)
    (by simpa only [activeEq] using reduced) entryBound
  intro row column
  by_cases before : row.val < processed
  · let index : Fin processed := ⟨row.val, before⟩
    have rowEq : Fin.castLE within index = row := Fin.ext rfl
    have bounded := processedBound index column
    rw [rowEq] at bounded
    have rankLe := (hermiteRowState_rank_le state).1
    have productLe := Nat.mul_le_mul rankLe (Nat.add_le_add_left rankLe width)
    exact bounded.trans_le (pow_le_pow_right₀ (by decide) (by omega))
  · have futureRow := futureRows row (by omega)
    rw [congrFun futureRow column]
    exact (entryBound row column).trans_le (pow_le_pow_right₀ (by decide) (by omega))

/-- In particular the completed row traversal has original-input polynomial entry widths. -/
theorem hermiteRowsSweep_matrix_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ row column, ((hermiteRowsSweep original).1.1 row column).natAbs <
      2 ^ (2 * (rows * (width + rows) + 1) + width + 2 * rows + 2) :=
  hermiteRowPrefix_matrix_bound width rows (by rfl) original (hermiteRowsSweep original)
    (hermiteRowsSweep_correct original) entryBound

/-- A fixed polynomial budget for the basis-width growth of one outer insertion. -/
def hermiteSweepBasisIncrement {Scalar : Type} [Semiring Scalar] (rows width : Scalar) : Scalar :=
  let matrixWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
  let pairWidth := (rows + 1) * (matrixWidth + (rows + 1)) + 1
  let workWidth := matrixWidth + rows * (3 * pairWidth + 3)
  rows * (workWidth + 2 * pairWidth + 3) + workWidth + 1

private theorem hermiteRowAdvance_basis_bound {rows columns : ℕ} (width basisWidth : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ) (processed : Fin rows)
    (state : {state : HermiteRowState rows columns // HermiteRowPrefix original processed.val state})
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width)
    (basisBound : ∀ row column, (state.val.1.2 row column).natAbs < 2 ^ basisWidth) :
    ∀ row column, ((hermiteRowAdvance original processed state).val.1.2 row column).natAbs <
      2 ^ (basisWidth + hermiteSweepBasisIncrement rows width) := by
  let matrixWidth := 2 * (rows * (width + rows) + 1) + width + 2 * rows + 2
  let rank := state.val.2.1
  let pairWidth := (rows + 1) * (matrixWidth + (rows + 1)) + 1
  let localPairWidth := (rank + 1) * (matrixWidth + (rank + 1)) + 1
  have correct := state.property
  obtain ⟨equation, unit, oldRows, support, upper, positive, reduced, basisSupport, future⟩ := correct
  have excluded : processed ∉ Set.range state.val.2.2.1 := by
    rintro ⟨index, same⟩
    have before := oldRows index
    rw [same] at before
    exact lt_irrefl _ before
  let selected := Fin.Embedding.snoc state.val.2.2.1 excluded
  have matrixBound := hermiteRowPrefix_matrix_bound width processed.val processed.isLt.le original state.val state.property entryBound
  have inserted := hermiteInsertRow_bound matrixWidth basisWidth selected state.val.2.2.2 state.val.1.1 state.val.1.2
    (by simpa only [selected, Fin.Embedding.snoc_castSucc] using positive) (by
      intro row column below
      simpa only [selected, Fin.Embedding.snoc_castSucc, Matrix.submatrix_apply] using upper below)
    matrixBound basisBound
  have rankLe : rank ≤ rows := (hermiteRowState_rank_le state.val).1
  have pairLe : localPairWidth ≤ pairWidth := by dsimp [localPairWidth, pairWidth]; gcongr
  have workLe : matrixWidth + rank * (3 * localPairWidth + 3) ≤ matrixWidth + rows * (3 * pairWidth + 3) := by gcongr
  have growthLe : rank * (matrixWidth + rank * (3 * localPairWidth + 3) + 2 * localPairWidth + 3) ≤
      rows * (matrixWidth + rows * (3 * pairWidth + 3) + 2 * pairWidth + 3) := by gcongr
  rw [hermiteRowAdvance_pair original processed state excluded]
  intro row column
  exact (inserted.2 row column).trans_le (pow_le_pow_right₀ (by decide) (by
    change matrixWidth + rank * (3 * localPairWidth + 3) +
      (basisWidth + rank * (matrixWidth + rank * (3 * localPairWidth + 3) + 2 * localPairWidth + 3)) + 1 ≤ _
    change _ ≤ basisWidth + (rows * (matrixWidth + rows * (3 * pairWidth + 3) + 2 * pairWidth + 3) +
      (matrixWidth + rows * (3 * pairWidth + 3)) + 1)
    omega))

/-- The accumulated left basis has a polynomial original-input width at every outer prefix. -/
theorem hermiteRowsPrefix_basis_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width)
    (processed : ℕ) (within : processed ≤ rows) :
    ∀ row column, ((hermiteRowsPrefix original processed within).val.1.2 row column).natAbs <
      2 ^ (1 + processed * hermiteSweepBasisIncrement rows width) := by
  induction processed with
  | zero =>
    intro row column
    change ((1 : Matrix (Fin rows) (Fin rows) ℤ) row column).natAbs < 2 ^ (1 + 0 * hermiteSweepBasisIncrement rows width)
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  | succ processed induction =>
    have bounded := hermiteRowAdvance_basis_bound width (1 + processed * hermiteSweepBasisIncrement rows width)
      original ⟨processed, by omega⟩ (hermiteRowsPrefix original processed (by omega)) entryBound (induction (by omega))
    intro row column
    exact (bounded row column).trans_le (pow_le_pow_right₀ (by decide) (by simp only [Nat.add_mul, one_mul]; omega))

/-- The complete traversal retains an actual unimodular basis with polynomial entry widths. -/
theorem hermiteRowsSweep_basis_bound {rows columns : ℕ} (width : ℕ)
    (original : Matrix (Fin rows) (Fin columns) ℤ)
    (entryBound : ∀ row column, (original row column).natAbs < 2 ^ width) :
    ∀ row column, ((hermiteRowsSweep original).1.2 row column).natAbs <
      2 ^ (1 + rows * hermiteSweepBasisIncrement rows width) :=
  hermiteRowsPrefix_basis_bound width original entryBound rows (by rfl)

end Polytime2.IntegerMatrix
