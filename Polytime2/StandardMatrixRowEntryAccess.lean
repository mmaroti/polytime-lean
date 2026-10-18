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

import Polytime2.StandardMatrixRowEntry

/-! # Matrix-read calls inside a shared row-entry workspace -/

namespace Polytime2.StandardMatrixRowEntry

open MultiTape CallingConvention

/-- Read either row's current entry using the common arithmetic scratch.
Tapes outside the call and immutable inputs are preserved. -/
theorem access_runs (target : Bool) (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (row column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (within : row.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → row.val < sizes 1 → column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (.inr (if target then 1 else 0)) = encoded (EncodedDomain.binaryNaturals 0) sizes row →
      initial (.inr 2) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial (.inr 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (access target (scalar.width Empty.elim)) ticks
          (StandardMatrixEntry.entry (scalar.width Empty.elim)) (fun _ => 0) initial
          (StandardMatrixEntry.exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (.inr (if target then 8 else 7)) = encoded scalar Empty.elim (array ⟨row.val * sizes 2 + column.val, within⟩) ∧
        (∀ name, name ∉ Set.range (accessWiring target) → final name = initial name) ∧
        (∀ name, StandardMatrixEntry.readOnly name = true → final (accessWiring target name) = initial (accessWiring target name)) := by
  obtain ⟨bound, execute⟩ := (StandardMatrixEntry.contract scalar.constant (scalar.width Empty.elim)
    (fun _ => by simp [EncodedDomain.constant, EncodedDomain.ofCodec])).wired_runs (accessWiring target)
  refine ⟨bound, ?_⟩
  intro sizes initial row column array within columnsFit rowValid columnValid capacity rowEq columnEq arrayEq headers regions
  let input := StandardMatrixEntry.inputValues scalar.constant sizes row column array
  have sameDomain : ∀ name, domains scalar (accessWiring target name) = StandardMatrixEntry.domains scalar.constant name := by
    intro name
    cases target <;> fin_cases name <;> rfl
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; rw [sameDomain name])
      (by
        intro name premise
        simp only [accessWiring_apply] at premise
        cases target <;> fin_cases name <;>
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
              exact rowEq
            · by_cases isColumn : name = 6
              · subst name
                exact columnEq
              · have impossible : StandardMatrixEntry.readOnly (.inl (.inr name)) = false := by
                  simp [StandardMatrixEntry.readOnly, StandardMatrixAddress.readOnly, isRow, isColumn]
                rw [impossible] at readonly
                contradiction
        | inr name => cases name with
          | false => exact arrayEq
          | true => contradiction)
      (by intro name writable; exact regions (accessWiring target name))
      headers
  obtain ⟨otherWithin, valueEq⟩ := correct
  change output () = array ⟨row.val * sizes 2 + column.val, otherWithin⟩ at valueEq
  refine ⟨ticks, final, cost, trace, ?_, outside, immutable⟩
  · have result := canonical ()
    rw [valueEq] at result
    exact result.trans (encoded_constant scalar sizes _)

end Polytime2.StandardMatrixRowEntry
