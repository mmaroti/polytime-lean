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

import Polytime2.StandardMatrixRowField
import Mathlib.Data.ZMod.Basic

/-! # Adding two rows of an ordinary rectangular finite-field matrix -/

namespace Polytime2.Examples.MatrixRowField

open MultiTape CallingConvention StandardMatrixRows

private abbrev sizes : Fin 3 → ℕ := ![3, 2, 3]
private abbrev enumeration := (ZMod.finEquiv 2).toEquiv.symm
private abbrev scalar := FieldRow.scalarDomain enumeration
private def original : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 0, 1], ![0, 1, 0]]
private def expected : Matrix (Fin 2) (Fin 3) (ZMod 2) := ![![1, 0, 1], ![1, 1, 1]]

private def input : Inputs (mathematicalDomains scalar) readOnly sizes := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl name => cases name with
    | inl name => cases name with
      | inl parameter => exact PUnit.unit
      | inr name =>
        by_cases source : name = 0
        · subst name; exact (0 : Fin 8)
        · by_cases target : name = 1
          · subst name; exact (1 : Fin 8)
          · have accepted : name = 0 ∨ name = 1 ∨ name = 3 := of_decide_eq_true readonly
            have coefficient : name = 3 := accepted.resolve_left source |>.resolve_left target
            subst name
            exact (1 : ZMod 2)
    | inr name => contradiction
  | inr name =>
    have isOriginal : name = 3 := of_decide_eq_true readonly
    subst name
    exact original

private noncomputable def initial : Tapes Alphabet := fun name =>
  if readonly : readOnly name = true then encoded (mathematicalDomains scalar name) sizes (input ⟨name, readonly⟩)
  else buffer (List.replicate ((mathematicalDomains scalar name).width sizes) 0)

/-- A full row-addition machine accepts a `2 × 3` mathematical matrix and
returns the expected matrix. Every writable tape is initially entirely blank;
inputs remain unchanged and every head is restored on return. -/
theorem add_rectangular :
    ∃ ticks final,
      Runs (fun name => (mathematicalDomains scalar name).width sizes) readOnly
        (machine false scalar (fun _ => Polytime2.MatrixRowField.add (Scalar := ZMod 2))) ticks
        (entry 1) (fun _ => 0) initial (exit 1) (fun _ => 0) final ∧
      final (dataTape 5) = encoded (matrixDomain scalar) sizes expected := by
  obtain ⟨sizeReadOnly, halts, bound, execute⟩ := StandardMatrixRowField.add_contract enumeration
  have represented : Entry (mathematicalDomains scalar) readOnly sizes input initial := by
    refine ⟨?_, ?_⟩
    · intro name readonly
      simp only [initial, dite_eq_left readonly]
    · intro name writable
      have notReadonly : ¬ readOnly name = true := by rw [writable]; decide
      exact ⟨List.replicate ((mathematicalDomains scalar name).width sizes) 0, List.length_replicate,
        by simp only [initial, dite_eq_right notReadonly]⟩
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ := execute sizes input initial
    (by change 0 < 2 ∧ 1 < 2 ∧ 3 < 8 ∧ 2 * 3 ≤ 8; decide) represented
    (by
      intro parameter
      have header := represented.1 (sizeTape parameter) rfl
      change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit at header
      exact header.trans (encoded_unary parameter sizes))
  obtain ⟨sourceValid, targetValid, correct⟩ := correct
  change output ⟨dataTape 5, rfl⟩ = Function.update original (1 : Fin 2)
    (fun column => original 1 column + (1 : ZMod 2) * original 0 column) at correct
  have changed : Function.update original (1 : Fin 2)
      (fun column => original 1 column + (1 : ZMod 2) * original 0 column) = expected := by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [original, expected]
  have outputEq := correct.trans changed
  have finalEq := canonical (dataTape 5) rfl
  refine ⟨ticks, final, trace, ?_⟩
  exact finalEq.trans (congrArg (encoded (matrixDomain scalar) sizes) outputEq)

end Polytime2.Examples.MatrixRowField
