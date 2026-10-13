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

import Polytime2.StandardGaussJordanEliminationAlgorithm
import Polytime2.CallingConventionSimulation

/-! # TM0 realization of standard-convention Gauss–Jordan elimination -/

namespace Polytime2.StandardGaussJordanElimination

open CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] [DecidableEq Scalar] {cardinality : ℕ}

/-- The standard simulator realizes the complete algorithm, including startup,
with polynomial time and storage and the mathematical row-equivalence contract.
No prepared scratch or source-tape markers are required. -/
theorem realizes_tm0 (enumeration : Scalar ≃ Fin cardinality) :
    CallingConvention.TM0Realizes (domains enumeration) readOnly sizeTapes (algorithm enumeration)
      (entry (StandardGaussJordanClear.zeroBits enumeration).length
        (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
        ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun sizes _ => sizes 1 < 2 ^ sizes 0 ∧ sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output =>
        let matrix := (matrixEquiv (Carrier := Scalar) sizes).symm (input ⟨inputTape, rfl⟩)
        let result := (matrixEquiv (Carrier := Scalar) sizes).symm (output ⟨workingTape, by decide⟩)
        result = GaussJordan.eliminate matrix ∧
          Matrix.RowEquivalent matrix result ∧ Matrix.IsReducedRowEchelon result) := by
  apply CallingConvention.Realizes.tm0
    (sourceExit := exit (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim))
  apply (contract enumeration).postcondition
  intro sizes input output equality
  refine ⟨equality, ?_, ?_⟩
  · rw [equality]
    exact GaussJordan.rowEquivalent _
  · rw [equality]
    exact GaussJordan.reducedRowEchelon _

end Polytime2.StandardGaussJordanElimination
