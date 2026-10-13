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

import Polytime2.StandardArrayLookupSizedContract
import Polytime2.EncodedArray

/-! # Standard-convention matrix lookup

The routine operates on the canonical row-major encoding of a matrix. -/

namespace Polytime2.StandardMatrixLookup

open Polytime2.StandardArrayLookupSized
open CallingConvention

-- parameterLevel: unary size-parameter names; matrix entries are fixed types.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

noncomputable def domains (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 6) → EncodedDomain.{parameterLevel, 0} Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 1 => EncodedDomain.matrix element rows columns
  | .inr 2 => element
  | .inr 3 | .inr 4 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 5 => EncodedDomain.booleans

noncomputable def equivalence (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (name : Sum Parameter (Fin 6)) (assignment : Parameter → ℕ) :
    (domains element indexCapacity rows columns name).Carrier assignment ≃
      (domainsSized element indexCapacity (rows * columns) name).Carrier assignment :=
  match name with
  | .inl _ => Equiv.refl _
  | .inr 0 => Equiv.refl _
  | .inr 1 => EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
  | .inr 2 => Equiv.refl _
  | .inr 3 => Equiv.refl _
  | .inr 4 => Equiv.refl _
  | .inr 5 => Equiv.refl _

def readOnly : Sum Parameter (Fin 6) → Bool :=
  StandardArrayLookupSized.argumentReadOnly

def sizeTapes : Parameter ↪ Sum Parameter (Fin 6) :=
  StandardArrayLookupSized.sizeTapes

noncomputable def algorithm (elementWidth : ℕ) :
    MultiTape.Machine (CallingConvention.Alphabet (Sum Parameter (Fin 6)))
      (StandardArrayLookup.State elementWidth) :=
  StandardArrayLookupSized.algorithmSized elementWidth

private theorem encodingEqual (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (rows columns : MvPolynomial Parameter ℕ)
    (name : Sum Parameter (Fin 6)) (assignment : Parameter → ℕ)
    (value : (domains element indexCapacity rows columns name).Carrier assignment) :
    CallingConvention.encoded (domains element indexCapacity rows columns name)
        assignment value =
      CallingConvention.encoded (domainsSized element indexCapacity (rows * columns) name)
        assignment (equivalence element indexCapacity rows columns name assignment value) := by
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
    · rfl
    · rfl
    · rfl

/-- The matrix is treated as a mathematical matrix; its canonical encoding
is the row-major array consumed by the same standard-convention lookup. -/
theorem contract (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (elementWidth : ℕ) (indexCapacity : Parameter)
    (rows columns : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domains element indexCapacity rows columns)
      readOnly sizeTapes (algorithm elementWidth)
      (StandardArrayLookup.entry elementWidth) (StandardArrayLookup.exit elementWidth)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment (rows * columns))
      (fun assignment input output => ∃ within :
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
          MvPolynomial.eval assignment (rows * columns),
        output ⟨.inr 2, rfl⟩ =
          EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
            (input ⟨.inr 1, rfl⟩)
            ⟨(input ⟨.inr 0, rfl⟩).val, within⟩) := by
  apply CallingConvention.realizes_reindex
    (equivalence element indexCapacity rows columns)
    (by intro name assignment; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (encodingEqual element indexCapacity rows columns)
    readOnly sizeTapes (algorithm elementWidth)
    (StandardArrayLookup.entry elementWidth) (StandardArrayLookup.exit elementWidth)
    (fun assignment input =>
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns))
    (fun assignment input =>
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns))
    (fun assignment input output => ∃ within :
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns),
      output ⟨.inr 2, rfl⟩ =
        EncodedDomain.MatrixEncoding.flattenPolynomial rows columns assignment
          (input ⟨.inr 1, rfl⟩)
          ⟨(input ⟨.inr 0, rfl⟩).val, within⟩)
    (fun assignment input output => ∃ within :
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment indexCapacity)).val <
        MvPolynomial.eval assignment (rows * columns),
      output ⟨.inr 2, rfl⟩ = input ⟨.inr 1, rfl⟩
        ⟨(input ⟨.inr 0, rfl⟩).val, within⟩)
    (by intro assignment input valid; exact valid)
    (by
      intro assignment input output correctness
      obtain ⟨within, equality⟩ := correctness
      exact ⟨within, equality⟩)
    (StandardArrayLookupSized.contractSized element elementWidth indexCapacity
      (rows * columns) fixedWidth)

end Polytime2.StandardMatrixLookup
