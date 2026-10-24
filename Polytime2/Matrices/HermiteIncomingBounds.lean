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

import Polytime2.Matrices.HermiteIncomingMath
import Mathlib.Data.Fin.Tuple.Embedding

/-! # Polynomial widths for an incoming-row traversal

For distinct pivot columns and positive upper-triangular input pivot rows,
truncated original minors bound every incoming-row prefix. Small selected-pair
elimination and small-source normalization then bound the entire working matrix
and accumulated left basis polynomially in the input dimensions and bit width.
This covers one incoming row; outer rank growth and successive Hermite passes
still need separate invariants and bounds.
-/

namespace Polytime2.IntegerMatrix

variable {Row Column : Type} [DecidableEq Row] [DecidableEq Column] {pivots : ℕ}

/-- Every incoming-row prefix has a uniform original-width bound, using truncated minors. -/
theorem hermiteIncomingPrefix_incoming_row_bound (width count : ℕ) (within : count ≤ pivots)
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots ↪ Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width) :
    ∀ column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
      (selectedRows (Fin.last pivots)) column).natAbs <
      2 ^ ((pivots + 1) * (width + (pivots + 1)) + 1) := by
  let prefixRows : Fin count ↪ Row := ⟨fun index => selectedRows (Fin.castLE within index).castSucc, by
    intro first second equal
    have values := congrArg Fin.val (selectedRows.injective equal)
    exact Fin.ext values⟩
  let prefixColumns : Fin count ↪ Column := ⟨fun index => pivotColumns (Fin.castLE within index), by
    intro first second equal
    have values := congrArg Fin.val (pivotColumns.injective equal)
    exact Fin.ext values⟩
  have targetExcluded : selectedRows (Fin.last pivots) ∉ Set.range prefixRows := by
    rintro ⟨index, equal⟩
    have values := congrArg Fin.val (selectedRows.injective equal)
    change index.val = pivots at values
    exact (ne_of_lt (lt_of_lt_of_le index.isLt within)) values
  let minorRows := Fin.Embedding.snoc prefixRows targetExcluded
  intro column
  by_cases visited : column ∈ Set.range prefixColumns
  · obtain ⟨index, rfl⟩ := visited
    have zero := (hermiteIncomingPrefix_entries selectedRows pivotColumns count within matrix left positive upper
      (Fin.castLE within index) index.isLt).2.1
    rw [show prefixColumns index = pivotColumns (Fin.castLE within index) from rfl, zero, Int.natAbs_zero]
    positivity
  · let minorColumns := Fin.Embedding.snoc prefixColumns visited
    have bounded := hermiteIncomingPrefix_truncated_bound width count within selectedRows pivotColumns
      minorRows minorColumns (by intro index; exact Fin.Embedding.snoc_castSucc)
      Fin.Embedding.snoc_last (by intro index; exact Fin.Embedding.snoc_castSucc)
      matrix left positive upper entryBound
    have result : ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1
        (selectedRows (Fin.last pivots)) column).natAbs <
        2 ^ ((count + 1) * (width + (count + 1)) + 1) := by
      simpa only [minorColumns, Fin.Embedding.snoc_last] using bounded
    exact result.trans_le (pow_le_pow_right₀ (by decide)
      (Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1))

/-- Bounded selected pairs give polynomial matrix and actual basis widths at every prefix. -/
theorem hermiteIncomingPrefix_bound_of_pairs (pairWidth matrixWidth basisWidth count : ℕ)
    (within : count ≤ pivots) (selectedRows : Fin (pivots + 1) ↪ Row)
    (pivotColumns : Fin pivots → Column) (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (sourceBound : ∀ (index : Fin pivots) column, (matrix (selectedRows index.castSucc) column).natAbs < 2 ^ pairWidth)
    (incomingBound : ∀ stage ≤ pivots, ∀ column,
      ((hermiteIncomingPrefix selectedRows pivotColumns stage matrix left).1
        (selectedRows (Fin.last pivots)) column).natAbs < 2 ^ pairWidth)
    (matrixBound : ∀ row column, (matrix row column).natAbs < 2 ^ matrixWidth)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ basisWidth) :
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 row column).natAbs <
      2 ^ (matrixWidth + count * (3 * pairWidth + 3))) ∧
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 row column).natAbs <
      2 ^ (basisWidth + count * (matrixWidth + count * (3 * pairWidth + 3) + 2 * pairWidth + 3))) := by
  induction count with
  | zero =>
    simpa only [hermiteIncomingPrefix, List.take_zero, List.foldl_nil, zero_mul, add_zero] using
      And.intro matrixBound basisBound
  | succ count induction =>
    let pivot : Fin pivots := ⟨count, by omega⟩
    let state := hermiteIncomingPrefix selectedRows pivotColumns count matrix left
    have previous := induction (by omega)
    have unchanged := hermiteIncomingPrefix_future_row selectedRows pivotColumns count pivot (by rfl) matrix left
    have sourceSmall : ∀ column, (state.1 (selectedRows pivot.castSucc) column).natAbs < 2 ^ pairWidth := by
      intro column
      rw [show state.1 (selectedRows pivot.castSucc) = matrix (selectedRows pivot.castSucc) from unchanged.1]
      exact sourceBound pivot column
    have sourcePositive : 0 < state.1 (selectedRows pivot.castSucc) (pivotColumns pivot) := by
      rw [show state.1 (selectedRows pivot.castSucc) = matrix (selectedRows pivot.castSucc) from unchanged.1]
      exact positive pivot
    have different : selectedRows pivot.castSucc ≠ selectedRows (Fin.last pivots) := by
      intro same
      have values := congrArg Fin.val (selectedRows.injective same)
      simp only [Fin.val_castSucc, Fin.val_last] at values
      exact (ne_of_lt pivot.isLt) values
    have excluded : selectedRows pivot.castSucc ∉
        (hermiteColumnTargets pivot.castSucc pivot.val).map selectedRows := by
      simpa only [List.mem_map, selectedRows.injective.eq_iff, exists_eq_right] using
        hermiteColumnTargets_excluded pivot.castSucc pivot.val
    have smallIncoming := incomingBound count (by omega)
    have step := hermiteRowStage_bound_of_small_pair pairWidth pairWidth
      (matrixWidth + count * (3 * pairWidth + 3))
      (basisWidth + count * (matrixWidth + count * (3 * pairWidth + 3) + 2 * pairWidth + 3))
      _ _ different (pivotColumns pivot) _
      ((hermiteColumnTargets_distinct pivot.castSucc pivot.val).map selectedRows.injective)
      excluded state.1 state.2 sourcePositive (sourceSmall _) (smallIncoming _)
      sourceSmall smallIncoming previous.1 previous.2
    rw [show count + 1 = pivot.val + 1 from rfl, hermiteIncomingPrefix_succ]
    constructor
    · intro row column
      exact (step.1 row column).trans_le (pow_le_pow_right₀ (by decide) (by dsimp [pivot]; ring_nf; omega))
    · intro row column
      exact (step.2 row column).trans_le (pow_le_pow_right₀ (by decide) (by dsimp [pivot]; ring_nf; omega))

/-- One incoming-row traversal has polynomial widths derived only from its original input. -/
theorem hermiteIncomingPrefix_bound (width basisWidth count : ℕ) (within : count ≤ pivots)
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots ↪ Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ basisWidth) :
    let pairWidth := (pivots + 1) * (width + (pivots + 1)) + 1
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 row column).natAbs <
      2 ^ (width + count * (3 * pairWidth + 3))) ∧
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 row column).natAbs <
      2 ^ (basisWidth + count * (width + count * (3 * pairWidth + 3) + 2 * pairWidth + 3))) := by
  apply hermiteIncomingPrefix_bound_of_pairs _ width basisWidth count within selectedRows pivotColumns matrix left positive
  · intro index column
    exact (entryBound _ _).trans_le (pow_le_pow_right₀ (by decide) (by nlinarith))
  · intro stage within column
    exact hermiteIncomingPrefix_incoming_row_bound width stage within selectedRows pivotColumns matrix left
      positive upper entryBound column
  · exact entryBound
  · exact basisBound

/-- A common polynomial workspace bounds both matrices at every incoming prefix. -/
theorem hermiteIncomingPrefix_uniform_bound (width count : ℕ) (within : count ≤ pivots)
    (selectedRows : Fin (pivots + 1) ↪ Row) (pivotColumns : Fin pivots ↪ Column)
    (matrix : Matrix Row Column ℤ) (left : Matrix Row Row ℤ)
    (positive : ∀ index, 0 < matrix (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin pivots, column < row →
      matrix (selectedRows row.castSucc) (pivotColumns column) = 0)
    (entryBound : ∀ row column, (matrix row column).natAbs < 2 ^ width)
    (basisBound : ∀ row column, (left row column).natAbs < 2 ^ width) :
    let pairWidth := (pivots + 1) * (width + (pivots + 1)) + 1
    let workspace := width + pivots * (width + (pivots + 1) * (3 * pairWidth + 3) + 2 * pairWidth + 3)
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).1 row column).natAbs <
      2 ^ workspace) ∧
    (∀ row column, ((hermiteIncomingPrefix selectedRows pivotColumns count matrix left).2 row column).natAbs <
      2 ^ workspace) := by
  have bounded := hermiteIncomingPrefix_bound width width count within selectedRows pivotColumns matrix left
    positive upper entryBound basisBound
  dsimp only at bounded ⊢
  constructor
  · intro row column
    apply (bounded.1 row column).trans_le
    apply pow_le_pow_right₀ (by decide)
    gcongr
    have enough : 3 * ((pivots + 1) * (width + (pivots + 1)) + 1) + 3 ≤
        (pivots + 1) * (3 * ((pivots + 1) * (width + (pivots + 1)) + 1) + 3) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  · intro row column
    apply (bounded.2 row column).trans_le
    apply pow_le_pow_right₀ (by decide)
    gcongr
    omega

end Polytime2.IntegerMatrix
