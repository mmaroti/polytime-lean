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

import Polytime2.StandardArrayUpdate
import Polytime2.EncodedArray

/-! # Standard-convention matrix update

The source and result are mathematical matrices. Their physical tapes use
the canonical row-major array encoding.
-/

namespace Polytime2.StandardMatrixUpdate

open CallingConvention

-- parameterLevel: unary size-parameter names; matrix entries are fixed types.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

noncomputable def domains (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 7) → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 1 | .inr 3 => EncodedDomain.matrix element rows columns
  | .inr 2 => element
  | .inr 4 | .inr 5 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 6 => EncodedDomain.booleans

noncomputable def equivalence (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (name : Sum Parameter (Fin 7)) (assignment : Parameter → ℕ) :
    (domains element indexCapacity rows columns name).Carrier assignment ≃
      (StandardArrayUpdate.domainsSized element indexCapacity (rows * columns) name).Carrier
        assignment :=
  match name with
  | .inl _ => Equiv.refl _
  | .inr 0 => Equiv.refl _
  | .inr 1 => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
  | .inr 2 => Equiv.refl _
  | .inr 3 => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
  | .inr 4 => Equiv.refl _
  | .inr 5 => Equiv.refl _
  | .inr 6 => Equiv.refl _

def readOnly : Sum Parameter (Fin 7) → Bool :=
  StandardArrayUpdate.argumentReadOnlySized

def sizeTapes : Parameter ↪ Sum Parameter (Fin 7) :=
  StandardArrayUpdate.sizeTapesSized

noncomputable def algorithm (elementWidth : ℕ) :
    MultiTape.Machine (CallingConvention.Alphabet (Sum Parameter (Fin 7)))
      (StandardArrayUpdate.State elementWidth) :=
  StandardArrayUpdate.algorithmSized elementWidth

/-- Matrix and flat-array presentations have identical physical encodings. -/
private theorem encodingEqual (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (name : Sum Parameter (Fin 7)) (assignment : Parameter → ℕ)
    (value : (domains element indexCapacity rows columns name).Carrier assignment) :
    CallingConvention.encoded (domains element indexCapacity rows columns name)
        assignment value =
      CallingConvention.encoded (StandardArrayUpdate.domainsSized element indexCapacity
        (rows * columns) name) assignment
        (equivalence element indexCapacity rows columns name assignment value) := by
  cases name with
  | inl parameter => rfl
  | inr name =>
    fin_cases name
    · rfl
    · simp only [domains] at value
      change CallingConvention.encoded (EncodedDomain.matrix element rows columns)
          assignment value =
        CallingConvention.encoded (EncodedDomain.arrayOfLength element (rows * columns))
          assignment (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment value)
      change CallingConvention.tape _ = CallingConvention.tape _
      rfl
    · rfl
    · simp only [domains] at value
      change CallingConvention.encoded (EncodedDomain.matrix element rows columns)
          assignment value =
        CallingConvention.encoded (EncodedDomain.arrayOfLength element (rows * columns))
          assignment (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment value)
      change CallingConvention.tape _ = CallingConvention.tape _
      rfl
    · rfl
    · rfl
    · rfl

/-- Updating one row-major coordinate returns a fresh valid matrix tape and
canonical values on every private scratch tape. -/
theorem contract (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (elementWidth : ℕ) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domains element indexCapacity rows columns)
      readOnly sizeTapes (algorithm elementWidth)
      (StandardArrayUpdate.entry elementWidth) (StandardArrayUpdate.exit elementWidth)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment (rows * columns))
      (fun assignment input output => ∃ within :
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment (rows * columns),
        EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
            (output ⟨.inr 3, rfl⟩) =
          Function.update
            (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
              (input ⟨.inr 1, rfl⟩))
            ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩)) := by
  apply CallingConvention.realizes_reindex
    (equivalence element indexCapacity rows columns)
    (by intro name assignment; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (encodingEqual element indexCapacity rows columns)
    readOnly sizeTapes (algorithm elementWidth)
    (StandardArrayUpdate.entry elementWidth) (StandardArrayUpdate.exit elementWidth)
    (fun assignment input =>
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns))
    (fun assignment input =>
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns))
    (fun assignment input output => ∃ within :
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns),
      EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
          (output ⟨.inr 3, rfl⟩) =
        Function.update
          (EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
            (input ⟨.inr 1, rfl⟩))
          ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩))
    (fun assignment input output => ∃ within :
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns),
      output ⟨.inr 3, rfl⟩ = Function.update (input ⟨.inr 1, rfl⟩)
        ⟨(input ⟨.inr 0, rfl⟩).val, within⟩ (input ⟨.inr 2, rfl⟩))
    (by intro assignment input valid; exact valid)
    (by
      intro assignment input output correctness
      obtain ⟨within, equality⟩ := correctness
      refine ⟨within, ?_⟩
      rw [show EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
          ((equivalence element indexCapacity rows columns (.inr 3) assignment).symm
            (output ⟨.inr 3, rfl⟩)) = output ⟨.inr 3, rfl⟩ by
        change equivalence element indexCapacity rows columns (.inr 3) assignment
            ((equivalence element indexCapacity rows columns (.inr 3) assignment).symm
              (output ⟨.inr 3, rfl⟩)) = output ⟨.inr 3, rfl⟩
        exact Equiv.apply_symm_apply _ _]
      dsimp [equivalence] at equality ⊢
      exact equality)
    (StandardArrayUpdate.contractSized element elementWidth indexCapacity
      (rows * columns) fixedWidth)

end Polytime2.StandardMatrixUpdate
