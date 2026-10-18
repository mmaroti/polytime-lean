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

import Polytime2.StandardMatrixRowEntryAccess

/-! # Matrix-replacement calls inside a shared row-entry workspace -/

namespace Polytime2.StandardMatrixRowEntry

open MultiTape CallingConvention

private def replacementInput (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (row column : Fin (2 ^ sizes 0))
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (replacement : scalar.Carrier Empty.elim) :
    Inputs (StandardMatrixReplace.domains scalar.constant) StandardMatrixReplace.readOnly sizes := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl name =>
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases isRow : name = 1
      · subst name
        exact row
      · by_cases isColumn : name = 6
        · subst name
          exact column
        · have impossible : StandardMatrixReplace.readOnly (.inl (.inr name)) = false := by
            simp [StandardMatrixReplace.readOnly, StandardMatrixAddress.readOnly, isRow, isColumn]
          rw [impossible] at readonly
          contradiction
  | inr name =>
    by_cases isArray : name = 0
    · subst name
      exact array
    · by_cases isElement : name = 1
      · subst name
        exact replacement
      · have isResult : name = 2 := by omega
        subst name
        contradiction

/-- First replace the source entry into the intermediate matrix, then replace
the target entry into the result. Local input preservation includes private
intermediate matrices and the scalar results of the preceding combine call. -/
theorem replace_runs (source : Bool) (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (row column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (replacement : scalar.Carrier Empty.elim)
      (within : row.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → row.val < sizes 1 → column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (.inr (if source then 0 else 1)) = encoded (EncodedDomain.binaryNaturals 0) sizes row →
      initial (.inr 2) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial (.inr (if source then 4 else 6)) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial (.inr (if source then 9 else 10)) = encoded scalar Empty.elim replacement →
      (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (replace source (scalar.width Empty.elim)) ticks
          (StandardMatrixReplace.entry (scalar.width Empty.elim)) (fun _ => 0) initial
          (StandardMatrixReplace.exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (.inr (if source then 6 else 5)) =
          encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes
            (Function.update array ⟨row.val * sizes 2 + column.val, within⟩ replacement) ∧
        (∀ name, name ∉ Set.range (replaceWiring source) → final name = initial name) ∧
        (∀ name, StandardMatrixReplace.readOnly name = true → final (replaceWiring source name) = initial (replaceWiring source name)) := by
  obtain ⟨bound, execute⟩ := (StandardMatrixReplace.contract scalar.constant (scalar.width Empty.elim)
    (fun _ => by simp [EncodedDomain.constant, EncodedDomain.ofCodec])).wired_runs (replaceWiring source)
  refine ⟨bound, ?_⟩
  intro sizes initial row column array replacement within columnsFit rowValid columnValid capacity
    rowEq columnEq arrayEq replacementEq headers regions
  let input := replacementInput scalar sizes row column array replacement
  have sameDomain : ∀ name, domains scalar (replaceWiring source name) = StandardMatrixReplace.domains scalar.constant name := by
    intro name
    cases source <;> fin_cases name <;> rfl
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; rw [sameDomain name])
      (by
        intro name premise
        simp only [replaceWiring_apply] at premise
        cases source <;> fin_cases name <;>
          first | rfl | norm_num [readOnly, addressSlot] at premise)
      ⟨columnsFit, rowValid, columnValid, capacity⟩
      (by
        intro name readonly
        cases name with
        | inl name =>
          cases name with
          | inl parameter =>
            change initial (.inl parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
            rw [encoded_unary]
            exact headers parameter
          | inr name =>
            by_cases isRow : name = 1
            · subst name
              cases source <;> exact rowEq
            · by_cases isColumn : name = 6
              · subst name
                exact columnEq
              · have impossible : StandardMatrixReplace.readOnly (.inl (.inr name)) = false := by
                  simp [StandardMatrixReplace.readOnly, StandardMatrixAddress.readOnly, isRow, isColumn]
                rw [impossible] at readonly
                contradiction
        | inr name =>
          by_cases isArray : name = 0
          · subst name
            exact arrayEq
          · by_cases isElement : name = 1
            · subst name
              exact replacementEq.trans (encoded_constant scalar sizes _).symm
            · have isResult : name = 2 := by omega
              subst name
              contradiction)
      (by intro name writable; exact regions (replaceWiring source name)) headers
  obtain ⟨otherWithin, valueEq⟩ := correct
  change output () = Function.update array ⟨row.val * sizes 2 + column.val, otherWithin⟩ replacement at valueEq
  refine ⟨ticks, final, cost, trace, ?_, outside, immutable⟩
  · have result := canonical ()
    rw [valueEq] at result
    exact result

end Polytime2.StandardMatrixRowEntry
