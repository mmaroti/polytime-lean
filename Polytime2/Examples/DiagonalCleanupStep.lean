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

import Polytime2.Matrices.DiagonalCleanupStep
import Polytime2.TM0.Computation

/-! # Complete guarded diagonal cleanup examples

A positive diagonal exercises selection, both basis updates, narrowing, and
storage. A singleton already forms a chain. Empty dimensions remain admissible.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.DiagonalCleanupStep

open Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

example (length width : MvPolynomial Parameter ℕ) : (diagonalStorePair length width).TM0Realizable :=
  (diagonalStorePair_realizable length width).tm0

example (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalRepair length productWidth basisWidth).TM0Realizable :=
  (diagonalRepair_realizable length productWidth basisWidth).tm0

example (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalCleanupStep length productWidth basisWidth).TM0Realizable :=
  (diagonalCleanupStep_realizable length productWidth basisWidth).tm0

private noncomputable def arguments :
    (diagonalCleanupStep (Parameter := Empty) 3 10 49).Arguments Empty.elim
  | 0 => fun index => if index.val = 0 then ⟨6, by norm_num⟩
      else if index.val = 1 then ⟨10, by norm_num⟩ else ⟨15, by norm_num⟩
  | 1 | 2 => ⟨1, by
      intro row column
      by_cases same : row = column <;> simp [Matrix.one_apply, same]⟩

private theorem arguments_valid :
    (diagonalCleanupStep (Parameter := Empty) 3 10 49).precondition Empty.elim arguments := by
  refine ⟨?_, ?_, 2, ?_, ?_, ?_⟩
  · intro index
    dsimp only [arguments]
    split_ifs <;> norm_num
  · change (∏ index, (arguments 0 index).val) ≤ 2 ^ MvPolynomial.eval Empty.elim (10 : MvPolynomial Empty ℕ)
    rw [← Fin.prod_ofFn]
    rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)]
    norm_num [arguments, List.ofFn_succ]
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 2
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 2
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · norm_num

private theorem violation :
    Polytime2.IntegerMatrix.diagonalViolation (fun index => (arguments 0 index).val) =
      some (⟨0, by norm_num⟩, ⟨1, by norm_num⟩) := by
  let flags := Polytime2.ArraySearch.adjacentFlags (fun first second : ℕ => first ∣ second)
    (fun index => (arguments 0 index).val)
  have found : Polytime2.ArraySearch.firstFalse flags = some ⟨0, by norm_num⟩ := by
    apply (Polytime2.ArraySearch.firstFalse_some_iff flags _).mpr
    rw [List.ofFn_congr (show MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) = 3 by norm_num)]
    norm_num [flags, Polytime2.ArraySearch.adjacentFlags, arguments, List.ofFn_succ]
    decide +kernel
  unfold Polytime2.IntegerMatrix.diagonalViolation
  change (Polytime2.ArraySearch.firstFalse flags).bind _ = _
  rw [found]
  change (if next : (0 : ℕ) + 1 < MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ) then
    some ((⟨0, by norm_num⟩ : Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ))),
      (⟨1, next⟩ : Fin (MvPolynomial.eval Empty.elim (3 : MvPolynomial Empty ℕ)))) else none) = _
  rw [dite_eq_left (by norm_num)]

example :
    let result := (diagonalCleanupStep (Parameter := Empty) 3 10 49).compute Empty.elim ⟨arguments, arguments_valid⟩
    ((result.1 ⟨0, by norm_num⟩).val, (result.1 ⟨1, by norm_num⟩).val, (result.1 ⟨2, by norm_num⟩).val) =
      (2, 30, 15) := by
  have correct := diagonalCleanupStep_correct (Parameter := Empty) 3 10 49 Empty.elim ⟨arguments, arguments_valid⟩
  rw [Polytime2.IntegerMatrix.diagonalCleanupWithBases, violation] at correct
  have entries := congrArg (fun result => (result.1 ⟨0, by norm_num⟩,
    result.1 ⟨1, by norm_num⟩, result.1 ⟨2, by norm_num⟩)) correct
  norm_num [Polytime2.IntegerMatrix.diagonalCleanupWithBases,
    Polytime2.IntegerMatrix.diagonalNormalizePair, arguments, Function.update_apply] at entries
  exact Prod.ext entries.1 (Prod.ext entries.2.1 entries.2.2)

private noncomputable def singletonArguments :
    (diagonalCleanupStep (Parameter := Empty) 1 0 8).Arguments Empty.elim
  | 0 => fun _ => ⟨1, by norm_num⟩
  | 1 | 2 => ⟨1, by
      intro row column
      by_cases same : row = column <;> simp [Matrix.one_apply, same]⟩

private theorem singleton_valid :
    (diagonalCleanupStep (Parameter := Empty) 1 0 8).precondition Empty.elim singletonArguments := by
  refine ⟨?_, ?_, 1, ?_, ?_, ?_⟩
  · intro index; norm_num [singletonArguments]
  · change (∏ _index : Fin (MvPolynomial.eval Empty.elim (1 : MvPolynomial Empty ℕ)), (1 : ℕ)) ≤ _
    simp
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 1
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · intro row column
    change ((1 : Matrix _ _ ℤ) row column).natAbs < 2 ^ 1
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · norm_num

example :
    let result := (diagonalCleanupStep (Parameter := Empty) 1 0 8).compute Empty.elim
      ⟨singletonArguments, singleton_valid⟩
    (fun index => (result.1 index).val) = (fun _ => 1) ∧ result.2.1.val = 1 ∧ result.2.2.val = 1 := by
  have chain : Polytime2.IntegerMatrix.diagonalDivisibilityChain
      (fun index => (singletonArguments 0 index).val) := fun _ _ _ => dvd_rfl
  have stopped := (Polytime2.IntegerMatrix.diagonalViolation_none _).mpr chain
  have correct := diagonalCleanupStep_correct (Parameter := Empty) 1 0 8 Empty.elim
    ⟨singletonArguments, singleton_valid⟩
  rw [Polytime2.IntegerMatrix.diagonalCleanupWithBases, stopped] at correct
  exact ⟨congrArg Prod.fst correct, congrArg (Prod.fst ∘ Prod.snd) correct,
    congrArg (Prod.snd ∘ Prod.snd) correct⟩

example (productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (diagonalCleanupStep 0 productWidth basisWidth).Arguments sizes)
    (room : 1 + (4 * MvPolynomial.eval sizes (productWidth + 1) + 3) ≤ MvPolynomial.eval sizes basisWidth) :
    (diagonalCleanupStep 0 productWidth basisWidth).precondition sizes arguments := by
  refine ⟨?_, ?_, 1, ?_, ?_, room⟩
  · intro index; have bound := index.isLt; norm_num at bound
  · have empty : IsEmpty (Fin (MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ))) := by
      have zero : MvPolynomial.eval sizes (0 : MvPolynomial Parameter ℕ) = 0 := by simp
      rw [zero]
      infer_instance
    simp
    exact Nat.one_le_two_pow
  · intro row column; have bound := row.isLt; norm_num at bound
  · intro row column; have bound := row.isLt; norm_num at bound

end Polytime2.Examples.DiagonalCleanupStep
