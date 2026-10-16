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

import Polytime2.StandardMatrixRowEntryContract

/-! # Full row-entry execution with coincident source and target rows -/

namespace Polytime2.Examples.MatrixRowController

open Polytime2.StandardMatrixRowEntry CallingConvention

private def input (scalar : EncodedDomain.{0, 0} Empty) (value : scalar.Carrier Empty.elim) :
    Inputs (domains scalar) readOnly ![1, 1, 1] := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl parameter => exact PUnit.unit
  | inr name =>
    by_cases zero : name = 0
    · subst name
      exact (0 : Fin 2)
    · by_cases one : name = 1
      · subst name
        exact (0 : Fin 2)
      · by_cases two : name = 2
        · subst name
          exact (0 : Fin 2)
        · by_cases three : name = 3
          · subst name
            exact value
          · by_cases four : name = 4
            · subst name
              exact fun _ => value
            · have low : name.val < 5 := of_decide_eq_true readonly
              omega

private noncomputable def initial (scalar : EncodedDomain.{0, 0} Empty) (value : scalar.Carrier Empty.elim) :
    MultiTape.Tapes Alphabet := fun name =>
  if readonly : readOnly name = true then encoded (domains scalar name) ![1, 1, 1] (input scalar value ⟨name, readonly⟩)
  else buffer (List.replicate ((domains scalar name).width ![1, 1, 1]) 2)

/-- The source write deliberately changes the selected scalar. The target
write must still use the original target scalar, which was read before either
write. Every writable region starts with arbitrary contents. -/
theorem coincident_rows (scalar : EncodedDomain.{0, 0} Empty) (value : scalar.Carrier Empty.elim)
    (changeValue : ∀ sizes, scalar.Carrier sizes → scalar.Carrier sizes) :
    ∃ ticks final,
      Runs (fun name => (domains scalar name).width ![1, 1, 1]) readOnly
        (machine true scalar (fun sizes _ source target => (changeValue sizes source, target))) ticks
        (entry (scalar.width Empty.elim)) (fun _ => 0) (initial scalar value)
        (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
      final (.inr 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) ![1, 1, 1] (fun _ => value) := by
  have represented : Entry (domains scalar) readOnly ![1, 1, 1] (input scalar value) (initial scalar value) := by
    constructor
    · intro name readonly
      simp only [initial, dite_eq_left readonly]
    · intro name writable
      refine ⟨List.replicate ((domains scalar name).width ![1, 1, 1]) 2, List.length_replicate, ?_⟩
      simp only [initial, writable, Bool.false_eq_true, ↓reduceDIte]
  obtain ⟨sizeReadonly, outputsWritable, halts, bound, execute⟩ := contract true scalar
    (fun sizes _ source target => (changeValue sizes source, target))
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute ![1, 1, 1] (input scalar value) (initial scalar value)
      (by change 1 < 2 ∧ 0 < 1 ∧ 0 < 1 ∧ 0 < 1 ∧ 1 * 1 ≤ 2; decide) represented
      (by
        intro parameter
        change initial scalar value (.inl parameter) = unary (![1, 1, 1] parameter)
        rw [represented.1 (.inl parameter) rfl]
        change encoded (EncodedDomain.unary parameter) ![1, 1, 1] PUnit.unit = unary (![1, 1, 1] parameter)
        exact encoded_unary parameter ![1, 1, 1])
  obtain ⟨sourceWithin, targetWithin, resultEq⟩ := correct
  dsimp only at resultEq
  change output () = Function.update
    (Function.update (fun _ => value) ⟨0, sourceWithin⟩ (changeValue Empty.elim value)) ⟨0, targetWithin⟩ value at resultEq
  rw [Function.update_idem, Function.update_eq_self] at resultEq
  refine ⟨ticks, final, trace, ?_⟩
  change final (outputTapes ()) = _
  rw [canonical (), resultEq]
  rfl

-- A real source change: true becomes false, then the coincident target write
-- restores the original true value rather than reading the intermediate one.
example : ∃ ticks final,
    Runs (fun name => (domains (EncodedDomain.booleans (Parameter := Empty)) name).width ![1, 1, 1]) readOnly
      (machine true EncodedDomain.booleans (fun _ _ (source target : Bool) => (!source, target))) ticks
      (entry 1) (fun _ => 0) (initial EncodedDomain.booleans true) (exit 1) (fun _ => 0) final ∧
    final (.inr 5) = encoded (EncodedDomain.booleans.constant.arrayOfLength StandardMatrixEntry.length)
      ![1, 1, 1] (fun _ => true) := coincident_rows EncodedDomain.booleans true (fun _ (value : Bool) => !value)

-- The same complete controller works when every scalar and matrix word has
-- zero-bit width; binary index and arithmetic tapes retain their fixed width.
example : ∃ ticks final,
    Runs (fun name => (domains (EncodedDomain.fixed (Equiv.refl (Fin 1))) name).width ![1, 1, 1]) readOnly
      (machine true (EncodedDomain.fixed (Equiv.refl (Fin 1))) (fun _ _ (source target : Fin 1) => (source, target))) ticks
      (entry 0) (fun _ => 0) (initial (EncodedDomain.fixed (Equiv.refl (Fin 1))) (0 : Fin 1))
      (exit 0) (fun _ => 0) final ∧
    final (.inr 5) = encoded ((EncodedDomain.fixed (Equiv.refl (Fin 1))).constant.arrayOfLength StandardMatrixEntry.length)
      ![1, 1, 1] (fun _ => (0 : Fin 1)) :=
  coincident_rows (EncodedDomain.fixed (Equiv.refl (Fin 1))) (0 : Fin 1) (fun _ (value : Fin 1) => value)

end Polytime2.Examples.MatrixRowController
