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

import Polytime2.Matrices.DiagonalPairMath

/-! # Shared weighted diagonal progress

A positive diagonal is represented by its active natural entries. A pair update
replaces two entries by their gcd and lcm and leaves all others unchanged.
Adjacent updates preserve the total product and halve the weighted product when
the earlier entry does not divide the later entry. The initial measure has
polynomial bit length in the number of entries and their common input width.
The shared pair lemmas also cover transfers between nonadjacent indices. They
do not by themselves bound complete Hermite sweeps on a rectangular matrix.
-/

namespace Polytime2.IntegerMatrix

variable {length : ℕ}

/-- Ordinary active diagonal entries after one gcd/lcm replacement. -/
def diagonalNormalizePair (diagonal : Fin length → ℕ) (first second : Fin length) : Fin length → ℕ :=
  Function.update (Function.update diagonal first (Nat.gcd (diagonal first) (diagonal second)))
    second (Nat.lcm (diagonal first) (diagonal second))

/-- A weighted product whose bit length bounds strict divisibility repairs. -/
def diagonalPotential (diagonal : Fin length → ℕ) : ℕ :=
  ∏ index, diagonal index ^ (length - index.val)

private theorem product_split (values : Fin length → ℕ) (first second : Fin length)
    (different : first ≠ second) :
    (∏ index, values index) = values first * values second *
      ∏ index ∈ (Finset.univ.erase first).erase second, values index := by
  rw [← Finset.mul_prod_erase Finset.univ values (a := first) (Finset.mem_univ first),
    ← Finset.mul_prod_erase (Finset.univ.erase first) values (a := second) (by simp [different.symm])]
  ring

private theorem pair_outside_product (original current : Fin length → ℕ)
    (first second : Fin length) (operation : Fin length → ℕ → ℕ)
    (outside : ∀ index, index ≠ first → index ≠ second → current index = original index) :
    (∏ index ∈ (Finset.univ.erase first).erase second, operation index (current index)) =
      ∏ index ∈ (Finset.univ.erase first).erase second, operation index (original index) := by
  apply Finset.prod_congr rfl
  intro index within
  have notSecond := (Finset.mem_erase.mp within).1
  have notFirst := (Finset.mem_erase.mp (Finset.mem_erase.mp within).2).1
  rw [outside index notFirst notSecond]

/-- A two-entry product-preserving change halves the potential when its earlier entry halves. -/
theorem diagonalPotential_halves_of_pair (original current : Fin length → ℕ)
    (first second : Fin length) (ordered : first < second)
    (outside : ∀ index, index ≠ first → index ≠ second → current index = original index)
    (sameProduct : current first * current second = original first * original second)
    (halved : 2 * current first ≤ original first) :
    2 * diagonalPotential current ≤ diagonalPotential original := by
  have different : first ≠ second := ne_of_lt ordered
  have exponents : length - first.val = (length - second.val) + (second.val - first.val) := by
    have bounded := second.isLt
    omega
  have gapPositive : 0 < second.val - first.val := by exact Nat.sub_pos_of_lt ordered
  unfold diagonalPotential
  rw [product_split (fun index => current index ^ (length - index.val)) first second different,
    product_split (fun index => original index ^ (length - index.val)) first second different]
  rw [pair_outside_product original current first second (fun index value => value ^ (length - index.val)) outside]
  rw [exponents]
  have decreased := IntegerArithmetic.weightedPair_halves_of_product (length - second.val) (second.val - first.val)
    (original first) (original second) (current first) (current second) gapPositive sameProduct halved
  simpa only [mul_assoc] using Nat.mul_le_mul_right
    (∏ index ∈ (Finset.univ.erase first).erase second, original index ^ (length - index.val)) decreased

/-- The bit measure strictly decreases for a positive product-preserving pair update. -/
theorem diagonalPotential_size_decreases_of_pair (original current : Fin length → ℕ)
    (positive : ∀ index, 0 < current index) (first second : Fin length) (ordered : first < second)
    (outside : ∀ index, index ≠ first → index ≠ second → current index = original index)
    (sameProduct : current first * current second = original first * original second)
    (halved : 2 * current first ≤ original first) :
    (diagonalPotential current).size < (diagonalPotential original).size := by
  apply IntegerArithmetic.size_lt_of_double_le
  · exact Finset.prod_pos (fun index _ => pow_pos (positive index) _)
  · exact diagonalPotential_halves_of_pair original current first second ordered outside sameProduct halved

/-- Entries outside the normalized pair retain their original values. -/
theorem diagonalNormalizePair_other (diagonal : Fin length → ℕ) (first second index : Fin length)
    (notFirst : index ≠ first) (notSecond : index ≠ second) :
    diagonalNormalizePair diagonal first second index = diagonal index := by
  simp only [diagonalNormalizePair, Function.update_of_ne notSecond, Function.update_of_ne notFirst]

theorem diagonalNormalizePair_positive (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (first second : Fin length) :
    ∀ index, 0 < diagonalNormalizePair diagonal first second index := by
  intro index
  by_cases atSecond : index = second
  · subst index
    simpa [diagonalNormalizePair] using Nat.lcm_pos (positive first) (positive second)
  · by_cases atFirst : index = first
    · subst index
      simpa [diagonalNormalizePair, Function.update_of_ne atSecond] using
        Nat.gcd_pos_of_pos_left (diagonal second) (positive first)
    · simpa [diagonalNormalizePair, Function.update_of_ne atSecond, Function.update_of_ne atFirst] using
        positive index

theorem diagonalNormalizePair_product (diagonal : Fin length → ℕ) (first second : Fin length)
    (different : first ≠ second) :
    (∏ index, diagonalNormalizePair diagonal first second index) = ∏ index, diagonal index := by
  rw [product_split _ first second different, product_split diagonal first second different]
  rw [pair_outside_product diagonal (diagonalNormalizePair diagonal first second) first second (fun _ value => value)
    (fun index notFirst notSecond => diagonalNormalizePair_other diagonal first second index notFirst notSecond)]
  simp only [diagonalNormalizePair, Function.update_self, Function.update_of_ne different]
  rw [Nat.gcd_mul_lcm]

theorem diagonalNormalizePair_halves (diagonal : Fin length → ℕ)
    (first second : Fin length) (adjacent : second.val = first.val + 1)
    (firstPositive : 0 < diagonal first) (notDivides : ¬diagonal first ∣ diagonal second) :
    2 * diagonalPotential (diagonalNormalizePair diagonal first second) ≤ diagonalPotential diagonal := by
  have different : first ≠ second := by intro same; subst second; omega
  apply diagonalPotential_halves_of_pair diagonal (diagonalNormalizePair diagonal first second) first second
    (by show first.val < second.val; omega)
  · intro index notFirst notSecond
    exact diagonalNormalizePair_other diagonal first second index notFirst notSecond
  · simpa only [diagonalNormalizePair, Function.update_self, Function.update_of_ne different] using
      Nat.gcd_mul_lcm (diagonal first) (diagonal second)
  · simpa only [diagonalNormalizePair, Function.update_self, Function.update_of_ne different] using
      ExtendedGcd.gcd_halves_of_not_dvd (diagonal first) (diagonal second) firstPositive notDivides

/-- Includes the empty diagonal: its potential is one, so one extra bit is necessary. -/
theorem diagonalPotential_initial_size_bound (width : ℕ) (diagonal : Fin length → ℕ)
    (entryBound : ∀ index, diagonal index < 2 ^ width) :
    (diagonalPotential diagonal).size ≤ width * length * length + 1 := by
  have oneBound : (1 : ℕ) ≤ 2 ^ width := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos width))
  have bound : diagonalPotential diagonal ≤ 2 ^ (width * length * length) := by
    unfold diagonalPotential
    calc
      _ ≤ ∏ _index : Fin length, (2 ^ width) ^ length := by
        apply Finset.prod_le_prod
        intro index _within
        exact (Nat.pow_le_pow_left (entryBound index).le _).trans
          (pow_le_pow_right₀ oneBound (Nat.sub_le length index.val))
      _ = 2 ^ (width * length * length) := by simp [← pow_mul]
  apply Nat.size_le.mpr
  exact bound.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos (width * length * length); omega)

/-- Each effective cleanup step consumes at least one bit of the global measure. -/
theorem diagonalNormalizePair_size_decreases (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (first second : Fin length)
    (adjacent : second.val = first.val + 1) (notDivides : ¬diagonal first ∣ diagonal second) :
    (diagonalPotential (diagonalNormalizePair diagonal first second)).size < (diagonalPotential diagonal).size := by
  apply IntegerArithmetic.size_lt_of_double_le
  · apply Finset.prod_pos
    intro index _within
    exact pow_pos (diagonalNormalizePair_positive diagonal positive first second index) _
  · exact diagonalNormalizePair_halves diagonal first second adjacent (positive first) notDivides

/-- A bounded total product controls every positive entry, independently of the schedule. -/
theorem diagonalEntries_bound (productWidth : ℕ) (diagonal : Fin length → ℕ)
    (positive : ∀ index, 0 < diagonal index) (productBound : (∏ index, diagonal index) ≤ 2 ^ productWidth) :
    ∀ index, diagonal index < 2 ^ (productWidth + 1) := by
  intro index
  calc
    diagonal index ≤ ∏ index, diagonal index :=
      Finset.single_le_prod (fun index _ => positive index) (Finset.mem_univ index)
    _ ≤ 2 ^ productWidth := productBound
    _ < 2 ^ (productWidth + 1) := by
      rw [pow_succ]
      have := Nat.two_pow_pos productWidth
      omega

/-- Preserving the total product controls every positive intermediate entry. -/
theorem diagonalEntries_bound_of_product (width : ℕ) (original current : Fin length → ℕ)
    (entryBound : ∀ index, original index < 2 ^ width) (positive : ∀ index, 0 < current index)
    (sameProduct : (∏ index, current index) = ∏ index, original index) :
    ∀ index, current index < 2 ^ (width * length + 1) := by
  apply diagonalEntries_bound (width * length) current positive
  calc
    (∏ index, current index) = ∏ index, original index := sameProduct
    _ ≤ ∏ _index : Fin length, 2 ^ width := Finset.prod_le_prod (fun index _ => (entryBound index).le)
    _ = 2 ^ (width * length) := by simp [← pow_mul]

end Polytime2.IntegerMatrix
