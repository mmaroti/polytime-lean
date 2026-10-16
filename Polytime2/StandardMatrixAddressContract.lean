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

import Polytime2.StandardMatrixAddress

/-! # Standard-convention row-major address calculation -/

namespace Polytime2.StandardMatrixAddress

open MultiTape CallingConvention
open Binary (word value)

def outputTapes : Unit ↪ Sum (Fin 3) (Fin 9) := oneTape (.inr 7)

/-- The column dimension comes from its unary size tape. The row and column
indices remain unchanged; only the address must be a valid encoding on return. -/
theorem contract : CallingConvention.Realizes domains readOnly sizeTapes outputTapes machine entry exit
    (fun sizes input => sizes 2 < 2 ^ sizes 0 ∧
      (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
        (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes 0)).val < 2 ^ sizes 0)
    (fun sizes input output =>
      (output () : Fin (2 ^ sizes 0)).val =
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
          (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes 0)).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), halt,
    MvPolynomial.X 2 * (4 * MvPolynomial.X 0 + 8) +
      MvPolynomial.X 0 * (6 * MvPolynomial.X 0 + 14) + 12 * MvPolynomial.X 0 + 29, ?_⟩
  intro sizes input initial valid represented sizeHeaders
  let row := List.ofFn (fun index : Fin (sizes 0) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  let column := List.ofFn (fun index : Fin (sizes 0) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  have rowLength : row.length = sizes 0 := List.length_ofFn
  have columnLength : column.length = sizes 0 := List.length_ofFn
  have rowValue : value row = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ sizes 0)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  have columnValue : value column = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ sizes 0)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  obtain ⟨oldProduct, productLength, productEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldNext, nextLength, nextEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldColumns, columnsLength, columnsEq⟩ := represented.2 (.inr 5) rfl
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr 7) rfl
  obtain ⟨multiplyFlags, multiplyFlagLength, multiplyFlagEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨addFlags, addFlagLength, addFlagEq⟩ := represented.2 (.inr 8) rfl
  norm_num [domains, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at multiplyFlagLength addFlagLength
  obtain ⟨multiplyFlag, rfl⟩ := List.length_eq_one_iff.mp multiplyFlagLength
  obtain ⟨addFlag, rfl⟩ := List.length_eq_one_iff.mp addFlagLength
  have rowEq : initial (.inr 1) = buffer (word row) :=
    (represented.1 (.inr 1) rfl).trans (encoded_binaryNaturals_value 0 sizes _)
  have columnEq : initial (.inr 6) = buffer (word column) :=
    (represented.1 (.inr 6) rfl).trans (encoded_binaryNaturals_value 0 sizes _)
  simp [domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at productLength shiftedLength nextLength columnsLength resultLength
  have addressFit : value row * sizes 2 + value column < 2 ^ sizes 0 := by
    rw [rowValue, columnValue]
    exact valid.2
  obtain ⟨scratch, scratchLength, trace⟩ := runs sizes row column rowLength columnLength
    oldProduct oldShifted oldNext oldColumns oldResult productLength shiftedLength
    nextLength columnsLength resultLength multiplyFlag addFlag valid.1 addressFit
  have initialEq : frame sizes row column oldProduct oldShifted oldNext oldColumns oldResult
      multiplyFlag addFlag = initial := by
    funext name
    cases name with
    | inl parameter => exact (sizeHeaders parameter).symm
    | inr name =>
      fin_cases name
      · exact productEq.symm
      · exact rowEq.symm
      · exact shiftedEq.symm
      · exact nextEq.symm
      · exact multiplyFlagEq.symm
      · exact columnsEq.symm
      · exact columnEq.symm
      · exact resultEq.symm
      · exact addFlagEq.symm
  rw [initialEq] at trace
  have scratchFits : (word scratch).length = row.length := by simp [word, scratchLength, rowLength]
  have nextFits : oldNext.length = row.length := nextLength.trans rowLength.symm
  have sameLength : column.length = row.length := columnLength.trans rowLength.symm
  let resultBits := MultiplyAdd.result row (columnBits sizes) column (word scratch) oldNext multiplyFlag
  have resultBitsLength : resultBits.length = sizes 0 :=
    (MultiplyAdd.result_length row (columnBits sizes) column (word scratch) oldNext multiplyFlag
      sameLength scratchFits nextFits).trans rowLength
  let resultNatural : Fin (2 ^ sizes 0) := ⟨value resultBits,
    by simpa only [resultBitsLength] using Binary.value_lt_pow_length resultBits⟩
  let output : Outputs domains outputTapes sizes := fun _ => resultNatural
  refine ⟨_, output, _, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    exact le_rfl
  · change value resultBits = _
    have fits : value row * value (columnBits sizes) + value column < 2 ^ row.length := by
      rwa [columnBits_value sizes valid.1, rowLength]
    simpa only [rowValue, columnValue, columnBits_value sizes valid.1] using
      MultiplyAdd.result_value row (columnBits sizes) column (word scratch) oldNext multiplyFlag
        sameLength scratchFits nextFits fits
  · intro name
    cases name
    exact (encoded_binaryNaturals 0 sizes resultBits resultBitsLength).symm

end Polytime2.StandardMatrixAddress
