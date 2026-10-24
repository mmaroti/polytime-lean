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

import Polytime2.Matrices.IntegerEuclideanReduction
import Polytime2.Matrices.EuclideanSweepMath
import Polytime2.Matrices.HermiteColumnBounds
import Polytime2.Matrices.HermiteWorkspace
import Polytime2.Matrices.HermiteColumnTraversalMath
import Polytime2.Arrays.BoundedPositions
import Polytime2.TM0.Computation

/-! # Euclidean reductions with retained bases

A positive pivot reduces negative entries to nonnegative remainders. Divisible
entries vanish while the pivot row stays fixed. Column reduction transposes the
same operation, including the accumulated basis.
-/

namespace Polytime2.Examples.EuclideanReduction

open Polytime2.Computation Polytime2.IntegerMatrix

variable {Parameter : Type} [Fintype Parameter]

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerRowRemainderWithLeft rows columns width).TM0Realizable :=
  (integerRowRemainderWithLeft_realizable rows columns width).tm0

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerColumnRemainderWithRight rows columns width).TM0Realizable :=
  (integerColumnRemainderWithRight_realizable rows columns width).tm0

private def sample (entry : ℤ) : Matrix (Fin 2) (Fin 3) ℤ :=
  !![6, 1, 2; entry, 4, 5]

example : rowRemainderWithLeft 0 1 0 (sample (-17)) 1 =
    (!![6, 1, 2; 1, 7, 11], !![1, 0; 3, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [rowRemainderWithLeft, rowRemainder, rowAdd, sample, Matrix.updateRow, Function.update, Matrix.one_apply]

example : rowRemainderWithLeft 0 1 0 (sample 18) 1 =
    (!![6, 1, 2; 0, 1, -1], !![1, 0; -3, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [rowRemainderWithLeft, rowRemainder, rowAdd, sample, Matrix.updateRow, Function.update, Matrix.one_apply]

example : columnRemainderWithRight 0 1 0 (sample (-17)).transpose 1 =
    (!![6, 1; 1, 7; 2, 11], !![1, 3; 0, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [columnRemainderWithRight, rowRemainderWithLeft, rowRemainder,
      rowAdd, sample, Matrix.updateRow, Matrix.transpose_apply, Function.update, Matrix.one_apply]

example : rowRemainder 0 1 1 (!![0, 6, 1; 5, -17, 4] : Matrix (Fin 2) (Fin 3) ℤ) 1 0 = 5 := by
  exact rowRemainder_zero_column 0 1 1 0 _ rfl 1

/-- Several targets share the pivot without compounding its row changes. -/
example : rowRemainderSweep 0 0 [1, 2, 3]
    (!![6, 1, 0; -17, 4, 5; 18, 2, -1; 0, 7, 9] : Matrix (Fin 4) (Fin 3) ℤ) 1 =
    (!![6, 1, 0; 1, 7, 5; 0, -1, -1; 0, 7, 9],
      !![1, 0, 0, 0; 3, 1, 0, 0; -3, 0, 1, 0; 0, 0, 0, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [rowRemainderSweep, List.foldr_cons, rowRemainderWithLeft, rowRemainder,
      rowAdd, Matrix.updateRow, Function.update, Matrix.one_apply]

example : rowRemainderSweep 0 0 [] (sample (-17)) 1 = (sample (-17), 1) := rfl

/-- A divisible target uses cancellation rather than changing the source row. -/
example : hermiteRowStep 0 1 0 (sample 18) 1 =
    (!![6, 1, 2; 0, 1, -1], !![1, 0; -3, 1]) := by
  apply Prod.ext <;> ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [hermiteRowStep, rowRemainderWithLeft, rowRemainder, rowAdd, sample,
      Matrix.updateRow, Function.update, Matrix.one_apply]

/-- A negative coprime target gives the positive unit pivot. -/
example : (hermiteRowStep 0 1 0 (sample (-17)) 1).1 0 0 = 1 ∧
    (hermiteRowStep 0 1 0 (sample (-17)) 1).1 1 0 = 0 := by
  have entries := hermiteRowStep_entries (0 : Fin 2) 1 (by decide) (0 : Fin 3)
    (sample (-17)) 1 (by norm_num [sample])
  norm_num [sample] at entries ⊢
  exact entries

private def columnSample : Matrix (Fin 3) (Fin 2) ℤ := !![6, 1; -17, 4; 18, 2]

/-- A changing-pivot sweep clears a rectangular column, retaining its basis. -/
example :
    let result := hermiteColumnSweep 0 0 [1, 2] columnSample 1
    result.1 0 0 = 1 ∧ result.1 1 0 = 0 ∧ result.1 2 0 = 0 := by
  decide +kernel

example : hermiteColumnPivotChanges 0 0 [1, 2] columnSample 1 = 1 := by
  decide +kernel

/-- The matrix and identity basis retain distinct polynomial width bounds. -/
example :
    (∀ row column, ((hermiteColumnSweep 0 0 [1, 2] columnSample 1).1 row column).natAbs < 2 ^ 29) ∧
    (∀ row column, ((hermiteColumnSweep 0 0 [1, 2] columnSample 1).2 row column).natAbs < 2 ^ 25) := by
  have bounds := hermiteColumnSweep_bound 5 5 1 (0 : Fin 3) (0 : Fin 2) [1, 2]
    (by decide) (by decide) columnSample 1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact bounds

example (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRowStep rows columns width).TM0Realizable :=
  (integerHermiteRowStep_realizable rows columns width).tm0

private noncomputable def hermiteArguments (entry : ℤ) (bound : entry.natAbs < 32) :
    (integerHermiteRowStep (Parameter := Empty) 2 2 5).Arguments Empty.elim
  | 0 => ⟨0, by norm_num⟩
  | 1 => ⟨1, by norm_num⟩
  | 2 => ⟨0, by norm_num⟩
  | 3 => ⟨fun row column => if row.val = 0 then (if column.val = 0 then 6 else 1)
        else (if column.val = 0 then entry else 4), by
      intro row column
      dsimp only
      split_ifs <;> norm_num
      exact bound⟩
  | 4 => ⟨1, by
      intro row column
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num⟩

private theorem hermiteArguments_valid (entry : ℤ) (bound : entry.natAbs < 32) :
    (integerHermiteRowStep (Parameter := Empty) 2 2 5).precondition Empty.elim (hermiteArguments entry bound) := by
  constructor
  · intro equal
    have valueEqual := congrArg Fin.val equal
    norm_num [hermiteArguments] at valueEqual
  · norm_num [hermiteArguments]

/-- The actual quotient branch retains the elementary shear basis. -/
example : ((integerHermiteRowStep (Parameter := Empty) 2 2 5).compute Empty.elim
    ⟨hermiteArguments 18 (by norm_num), hermiteArguments_valid 18 (by norm_num)⟩).2.val
      ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = -3 := by
  decide +kernel

/-- The actual nondivisible branch retains the Bézout basis. -/
example : ((integerHermiteRowStep (Parameter := Empty) 2 2 5).compute Empty.elim
    ⟨hermiteArguments (-17) (by norm_num), hermiteArguments_valid (-17) (by norm_num)⟩).2.val
      ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 17 := by
  decide +kernel

example (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) :
    (Realizable.Internal.integerHermiteRowStepWithin rows columns columnWidth workspace).TM0Realizable :=
  (Realizable.Internal.integerHermiteRowStepWithin_realizable rows columns columnWidth workspace).tm0

private noncomputable def workspaceArguments (entry : ℤ) (bound : entry.natAbs < 32) :
    (Realizable.Internal.integerHermiteRowStepWithin (Parameter := Empty) 2 2 5 20).Arguments Empty.elim
  | 0 => hermiteArguments entry bound 0
  | 1 => hermiteArguments entry bound 1
  | 2 => hermiteArguments entry bound 2
  | 3 => ⟨(hermiteArguments entry bound 3).val,
      fun row column => ((hermiteArguments entry bound 3).property row column).trans_le (by norm_num)⟩
  | 4 => ⟨(hermiteArguments entry bound 4).val,
      fun row column => ((hermiteArguments entry bound 4).property row column).trans_le (by norm_num)⟩

private theorem workspaceArguments_valid (entry : ℤ) (bound : entry.natAbs < 32) :
    (Realizable.Internal.integerHermiteRowStepWithin (Parameter := Empty) 2 2 5 20).precondition Empty.elim
      (workspaceArguments entry bound) := by
  refine ⟨hermiteArguments_valid entry bound, ?_, ?_, 5, ?_, ?_, ?_⟩
  · simpa only [workspaceArguments] using
      (hermiteArguments entry bound 3).property (hermiteArguments entry bound 0) (hermiteArguments entry bound 2)
  · simpa only [workspaceArguments] using
      (hermiteArguments entry bound 3).property (hermiteArguments entry bound 1) (hermiteArguments entry bound 2)
  · simpa [workspaceArguments] using (hermiteArguments entry bound 3).property
  · simpa [workspaceArguments] using (hermiteArguments entry bound 4).property
  · norm_num

/-- The fixed workspace retains the actual Bézout basis after narrowing. -/
example : ((Realizable.Internal.integerHermiteRowStepWithin (Parameter := Empty) 2 2 5 20).compute Empty.elim
    ⟨workspaceArguments (-17) (by norm_num), workspaceArguments_valid (-17) (by norm_num)⟩).2.val
      ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 17 := by
  decide +kernel

example (length : MvPolynomial Parameter ℕ) : (arrayBoundedPositions length).TM0Realizable :=
  (arrayBoundedPositions_realizable length).tm0

example (sizes : Parameter → ℕ) : (arrayBoundedPositions (0 : MvPolynomial Parameter ℕ)).outputDomain.width sizes = 0 := by
  simp [arrayBoundedPositions, arrayTabulate, EncodedDomain.arrayOfLength, EncodedDomain.width]

/-- The source may occur in the middle of the row enumeration. -/
example : hermiteColumnTargets (1 : Fin 3) 3 = [2, 0] := by decide

example :
    let result := hermiteColumnPrefix 1 (0 : Fin 2) 3
      (!![-17, 4; 6, 1; 18, 2] : Matrix (Fin 3) (Fin 2) ℤ) 1
    result.1 1 0 = 1 ∧ result.1 0 0 = 0 ∧ result.1 2 0 = 0 := by
  decide +kernel

/-- Prefix bounds include the source position that the runtime fold skips. -/
example :
    (∀ row column, ((hermiteColumnPrefix 0 0 3 columnSample 1).1 row column).natAbs < 2 ^ 41) ∧
    (∀ row column, ((hermiteColumnPrefix 0 0 3 columnSample 1).2 row column).natAbs < 2 ^ 37) := by
  exact hermiteColumnPrefix_bound 5 5 1 0 0 3 columnSample 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A three-bit source gives twelve-bit normalization of eight-bit targets. -/
example :
    let matrix : Matrix (Fin 2) (Fin 2) ℤ := !![6, 1; 129, 200]
    let result := rowRemainderSweep 0 0 [1] matrix 1
    (∀ row column, (result.1 row column).natAbs < 2 ^ 12) ∧
      (∀ row column, (result.2 row column).natAbs < 2 ^ 10) := by
  exact rowRemainderSweep_bound_of_source 8 3 1 0 0 [1]
    (by decide) (by decide) _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end Polytime2.Examples.EuclideanReduction
