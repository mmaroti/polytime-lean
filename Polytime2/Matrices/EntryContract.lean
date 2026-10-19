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

import Polytime2.Matrices.Entry

/-! # Mathematical contract for matrix-entry lookup -/

namespace Polytime2.StandardMatrixEntry

open MultiTape CallingConvention
open Binary (word value)

/-- Valid row and column indices give a valid row-major array coordinate. -/
theorem index_lt (sizes : Fin 3 → ℕ) (row column : ℕ) (rowValid : row < sizes 1) (columnValid : column < sizes 2) :
    row * sizes 2 + column < MvPolynomial.eval sizes length := by
  simp only [length, map_mul, MvPolynomial.eval_X]
  have bound := Nat.mul_le_mul_right (sizes 2) (Nat.succ_le_iff.mpr rowValid)
  nlinarith

/-- Mathematical arguments for an entry lookup; unary sizes have singleton
carriers and no writable tape is included among the inputs. -/
def inputValues (element : EncodedDomain.{0, 0} (Fin 3)) (sizes : Fin 3 → ℕ)
    (row column : Fin (2 ^ sizes 0)) (array : (element.arrayOfLength length).Carrier sizes) :
    Inputs (domains element) readOnly sizes := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl name => cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases isRow : name = 1
      · subst name; exact row
      · by_cases isColumn : name = 6
        · subst name; exact column
        · have impossible : readOnly (.inl (.inr name)) = false := by
            simp [readOnly, StandardMatrixAddress.readOnly, isRow, isColumn]
          rw [impossible] at readonly
          contradiction
  | inr name => cases name with
    | false => exact array
    | true => contradiction

def outputTapes : Unit ↪ TapeName := oneTape (.inr true)

/-- Lookup uses separate immutable binary row and column indices. Dimensions
are unary size inputs; the matrix has the canonical row-major encoding. -/
theorem contract (element : EncodedDomain.{0, 0} (Fin 3)) (elementWidth : ℕ)
    (fixedWidth : ∀ sizes, element.width sizes = elementWidth) :
    CallingConvention.Realizes (domains element) readOnly sizeTapes outputTapes (machine elementWidth)
      (entry elementWidth) (exit elementWidth)
      (fun sizes input => sizes 2 < 2 ^ sizes 0 ∧
        (input ⟨.inl (.inr 1), rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨.inl (.inr 6), rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 2 ∧
        sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃ within :
        (input ⟨.inl (.inr 1), rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
          (input ⟨.inl (.inr 6), rfl⟩ : Fin (2 ^ sizes 0)).val < MvPolynomial.eval sizes length,
        output () = input ⟨.inr false, rfl⟩
          ⟨(input ⟨.inl (.inr 1), rfl⟩).val * sizes 2 +
            (input ⟨.inl (.inr 6), rfl⟩).val, within⟩) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), halt elementWidth, ?_⟩
  refine ⟨
    MvPolynomial.X 2 * (4 * MvPolynomial.X 0 + 8) +
      MvPolynomial.X 0 * (6 * MvPolynomial.X 0 + 14) + 12 * MvPolynomial.X 0 + 30 +
      length * (6 * MvPolynomial.X 0 + MvPolynomial.C (2 * elementWidth + 11)) +
      6 * MvPolynomial.X 0 + MvPolynomial.C (2 * elementWidth + 15), ?_⟩
  intro sizes input initial valid represented sizeHeaders
  let row := List.ofFn (fun index : Fin (sizes 0) =>
    (BitVec.ofFin (input ⟨.inl (.inr 1), rfl⟩)).getLsbD index.val)
  let column := List.ofFn (fun index : Fin (sizes 0) =>
    (BitVec.ofFin (input ⟨.inl (.inr 6), rfl⟩)).getLsbD index.val)
  let array : (element.arrayOfLength length).Carrier sizes := input ⟨.inr false, rfl⟩
  have rowLength : row.length = sizes 0 := List.length_ofFn
  have columnLength : column.length = sizes 0 := List.length_ofFn
  have rowValue : value row = (input ⟨.inl (.inr 1), rfl⟩ : Fin (2 ^ sizes 0)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inl (.inr 1), rfl⟩))
  have columnValue : value column = (input ⟨.inl (.inr 6), rfl⟩ : Fin (2 ^ sizes 0)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inl (.inr 6), rfl⟩))
  have within : value row * sizes 2 + value column < MvPolynomial.eval sizes length := by
    simp only [length, map_mul, MvPolynomial.eval_X]
    rw [rowValue, columnValue]
    have bound := Nat.mul_le_mul_right (sizes 2) (Nat.succ_le_iff.mpr valid.2.1)
    nlinarith [valid.2.2.1]
  have addressFit : value row * sizes 2 + value column < 2 ^ sizes 0 :=
    within.trans_le (by simpa only [length, map_mul, MvPolynomial.eval_X] using valid.2.2.2)
  obtain ⟨oldElement, elementLength, elementEq⟩ := represented.2 (.inr true) rfl
  obtain ⟨oldProduct, productLength, productEq⟩ := represented.2 (.inl (.inr 0)) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inl (.inr 2)) rfl
  obtain ⟨oldNext, nextLength, nextEq⟩ := represented.2 (.inl (.inr 3)) rfl
  obtain ⟨oldColumns, columnsLength, columnsEq⟩ := represented.2 (.inl (.inr 5)) rfl
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inl (.inr 7)) rfl
  obtain ⟨multiplyFlags, multiplyFlagLength, multiplyFlagEq⟩ := represented.2 (.inl (.inr 4)) rfl
  obtain ⟨addFlags, addFlagLength, addFlagEq⟩ := represented.2 (.inl (.inr 8)) rfl
  norm_num [domains, StandardMatrixAddress.domains, EncodedDomain.booleans,
    EncodedDomain.fixed, EncodedDomain.ofCodec] at multiplyFlagLength addFlagLength
  obtain ⟨multiplyFlag, rfl⟩ := List.length_eq_one_iff.mp multiplyFlagLength
  obtain ⟨addFlag, rfl⟩ := List.length_eq_one_iff.mp addFlagLength
  have rowEq : initial (.inl (.inr 1)) = buffer (word row) :=
    (represented.1 (.inl (.inr 1)) rfl).trans (encoded_binaryNaturals_value 0 sizes _)
  have columnEq : initial (.inl (.inr 6)) = buffer (word column) :=
    (represented.1 (.inl (.inr 6)) rfl).trans (encoded_binaryNaturals_value 0 sizes _)
  have arrayEq : initial (.inr false) = encoded (element.arrayOfLength length) sizes array :=
    represented.1 (.inr false) rfl
  simp [domains, StandardMatrixAddress.domains, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] at productLength shiftedLength nextLength columnsLength resultLength
  obtain ⟨ticks, addressBits, addressBitsLength, addressValue, cost, trace⟩ :=
    runs element sizes row column rowLength columnLength array oldElement oldProduct oldShifted oldNext
      oldColumns oldResult elementLength productLength shiftedLength nextLength columnsLength resultLength
      multiplyFlag addFlag valid.1 addressFit within
  have initialEq : frame sizes row column (encoded (element.arrayOfLength length) sizes array)
      oldElement oldProduct oldShifted oldNext oldColumns oldResult multiplyFlag addFlag = initial := by
    funext name
    cases name with
    | inl name =>
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
    | inr name => cases name with
      | false => exact arrayEq.symm
      | true => exact elementEq.symm
  rw [initialEq] at trace
  let selected := array ⟨value row * sizes 2 + value column, within⟩
  let output : Outputs (domains element) outputTapes sizes := fun _ => selected
  have chosenWidth := fixedWidth sizes
  subst elementWidth
  refine ⟨ticks, output, _, ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
    simpa only [Nat.add_assoc] using cost
  · refine ⟨?_, ?_⟩
    · simpa only [rowValue, columnValue] using within
    · change array ⟨value row * sizes 2 + value column, within⟩ = _
      apply congrArg array
      apply Fin.ext
      simp only [rowValue, columnValue]
  · intro name
    cases name
    rfl

end Polytime2.StandardMatrixEntry
