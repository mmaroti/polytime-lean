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

import Polytime2.StandardMatrixRowEntryRuns

/-! # Standard-convention contract for a matrix row-entry operation -/

namespace Polytime2.StandardMatrixRowEntry

open MultiTape CallingConvention

def outputTapes : Unit ↪ TapeName := oneTape (.inr 5)

/-- Combine the two original entries, optionally replace the source entry,
and replace the target entry in a separate result matrix. The specialization
chooses the finite scalar operation; dimensions and indices are runtime inputs. -/
theorem contract (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) :
    CallingConvention.Realizes (domains scalar) readOnly sizeTapes outputTapes (machine writeSource scalar operation)
      (entry (scalar.width Empty.elim)) (exit (scalar.width Empty.elim))
      (fun sizes input => sizes 2 < 2 ^ sizes 0 ∧
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨.inr 2, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 2 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceWithin : (input ⟨.inr 0, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
          (input ⟨.inr 2, rfl⟩ : Fin (2 ^ sizes 0)).val < MvPolynomial.eval sizes StandardMatrixEntry.length)
        (targetWithin : (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
          (input ⟨.inr 2, rfl⟩ : Fin (2 ^ sizes 0)).val < MvPolynomial.eval sizes StandardMatrixEntry.length),
        let sourceIndex := ⟨(input ⟨.inr 0, rfl⟩).val * sizes 2 + (input ⟨.inr 2, rfl⟩).val, sourceWithin⟩
        let targetIndex := ⟨(input ⟨.inr 1, rfl⟩).val * sizes 2 + (input ⟨.inr 2, rfl⟩).val, targetWithin⟩
        let array := input ⟨.inr 4, rfl⟩
        let result := effectiveOperation writeSource scalar operation Empty.elim
          (input ⟨.inr 3, rfl⟩) (array sourceIndex) (array targetIndex)
        output () = Function.update (Function.update array sourceIndex result.1) targetIndex result.2) := by
  classical
  obtain ⟨bound, execute⟩ := runs writeSource scalar operation
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), halt writeSource scalar operation, bound, ?_⟩
  intro sizes input initial valid represented headers
  let sourceRow : Fin (2 ^ sizes 0) := input ⟨.inr 0, rfl⟩
  let targetRow : Fin (2 ^ sizes 0) := input ⟨.inr 1, rfl⟩
  let column : Fin (2 ^ sizes 0) := input ⟨.inr 2, rfl⟩
  let coefficient : scalar.Carrier Empty.elim := input ⟨.inr 3, rfl⟩
  let array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes := input ⟨.inr 4, rfl⟩
  have sourceWithin : sourceRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length := by
    simp only [StandardMatrixEntry.length, map_mul, MvPolynomial.eval_X]
    have bound := Nat.mul_le_mul_right (sizes 2) (Nat.succ_le_iff.mpr valid.2.1)
    change (sourceRow.val + 1) * sizes 2 ≤ sizes 1 * sizes 2 at bound
    have columnValid : column.val < sizes 2 := valid.2.2.2.1
    nlinarith
  have targetWithin : targetRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length := by
    simp only [StandardMatrixEntry.length, map_mul, MvPolynomial.eval_X]
    have bound := Nat.mul_le_mul_right (sizes 2) (Nat.succ_le_iff.mpr valid.2.2.1)
    change (targetRow.val + 1) * sizes 2 ≤ sizes 1 * sizes 2 at bound
    have columnValid : column.val < sizes 2 := valid.2.2.2.1
    nlinarith
  let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨sourceRow.val * sizes 2 + column.val, sourceWithin⟩
  let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨targetRow.val * sizes 2 + column.val, targetWithin⟩
  let result := effectiveOperation writeSource scalar operation Empty.elim coefficient (array sourceIndex) (array targetIndex)
  let resultArray := Function.update (Function.update array sourceIndex result.1) targetIndex result.2
  obtain ⟨ticks, final, cost, trace, resultEq⟩ :=
    execute sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin
      valid.1 valid.2.1 valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2
      (represented.1 (.inr 0) rfl) (represented.1 (.inr 1) rfl) (represented.1 (.inr 2) rfl)
      ((represented.1 (.inr 3) rfl).trans (encoded_constant scalar sizes _)) (represented.1 (.inr 4) rfl) headers represented.region
  let output : Outputs (domains scalar) outputTapes sizes := fun _ => resultArray
  refine ⟨ticks, output, final, cost, trace, ?_, ?_⟩
  · exact ⟨sourceWithin, targetWithin, by rfl⟩
  · intro name
    cases name
    exact resultEq

end Polytime2.StandardMatrixRowEntry
