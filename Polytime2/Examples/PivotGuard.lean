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

import Polytime2.StandardPivotSearchAlgorithm

/-! # Preparing a pivot workspace and executing its first guard -/

namespace Polytime2.Examples.PivotGuard

open MultiTape CallingConvention StandardPivotSearch

private noncomputable abbrev scalar := EncodedDomain.booleans (Parameter := Empty)
private abbrev sizes (rows : Fin 2) : Fin 3 → ℕ := ![1, rows.val, 1]
private abbrev isZero (_assignment : Empty → ℕ) (value : Bool) : Bool := !value

private def input (rows : Fin 2) (value : Bool) : Inputs (domains scalar) readOnly (sizes rows) := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl name => cases name with
    | inl name => cases name with
      | inl parameter => exact PUnit.unit
      | inr name =>
        have isColumn : name = 6 := of_decide_eq_true readonly
        subst name
        exact (0 : Fin 2)
    | inr name => cases name with
      | false => exact fun _ => value
      | true => contradiction
  | inr name =>
    have isStart : name = 0 := of_decide_eq_true readonly
    subst name
    exact (0 : Fin 2)

private noncomputable def initial (rows : Fin 2) (value : Bool) : Tapes Alphabet := fun name =>
  if readonly : readOnly name = true then encoded (domains scalar name) (sizes rows) (input rows value ⟨name, readonly⟩)
  else buffer (List.replicate ((domains scalar name).width (sizes rows)) 2)

private noncomputable def preparedGuard :=
  MultiTape.sequence initialization
    (MultiTape.sequence readLimit (guard scalar isZero) (guardEntry (scalar.width Empty.elim))) (.inl StandardSizeRead.entry)

/-- Runtime row counts zero and one use the same finite controller. All
writable tapes start with arbitrary contents, and preparation is part of the run. -/
theorem first_guard (rows : Fin 2) (value : Bool) :
    ∃ ticks final,
      Runs (fun name => (domains scalar name).width (sizes rows)) readOnly preparedGuard ticks
        (.inl 0) (fun _ => 0) (initial rows value)
        (.inr (.inr (guardExit (scalar.width Empty.elim)))) (fun _ => 0) final ∧
      final foundTape = encoded EncodedDomain.booleans (sizes rows) (decide (0 < rows.val)) ∧
      final continueTape = encoded EncodedDomain.booleans (sizes rows) (if 0 < rows.val then !value else false) := by
  have represented : Entry (domains scalar) readOnly (sizes rows) (input rows value) (initial rows value) := by
    refine ⟨?_, ?_⟩
    · intro name readonly
      simp only [initial, dite_eq_left readonly]
    · intro name writable
      have notReadonly : ¬ readOnly name = true := by rw [writable]; decide
      exact ⟨List.replicate ((domains scalar name).width (sizes rows)) 2, List.length_replicate,
        by simp only [initial, dite_eq_right notReadonly]⟩
  have headers (parameter : Fin 3) : initial rows value (sizeTape parameter) = unary (sizes rows parameter) := by
    have header := represented.1 (sizeTape parameter) rfl
    change initial rows value (sizeTape parameter) = encoded (EncodedDomain.unary parameter) (sizes rows) PUnit.unit at header
    exact header.trans (encoded_unary parameter (sizes rows))
  have initTrace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
    (sizes rows) (0 : Fin 2) startTape (counterTape 1) (by decide)
    (fun name => (domains scalar name).width (sizes rows)) readOnly rfl rfl rfl
    (initial rows value) (represented.1 startTape rfl) (represented.region (counterTape 1))
  let initialized := Function.update (initial rows value) (counterTape 1)
    (encoded (EncodedDomain.binaryNaturals 0) (sizes rows) (0 : Fin 2))
  have candidateEq : initialized (counterTape 1) =
      encoded (EncodedDomain.binaryNaturals 0) (sizes rows) (0 : Fin 2) := Function.update_self _ _ _
  let initTicks := 2 * (sizes rows) 0 + 2
  simp only [EncodedDomain.binaryNaturals_width] at initTrace
  have initializedRegions : ∀ name, Region ((domains scalar name).width (sizes rows)) 0 (initialized name) :=
    fun name => initTrace.region name (represented.region name)
  obtain ⟨readBound, executeRead⟩ := readLimit_runs scalar
  obtain ⟨readTicks, prepared, readCost, readTrace, limitEq, scratchEq, readOutside⟩ :=
    executeRead (sizes rows) initialized rows.isLt
      (fun parameter => (initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (by simpa [domains, rowLimitTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions rowLimitTape)
      (by simpa [domains, counterTape, StandardMatrixEntry.domains, StandardMatrixAddress.domains,
        EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions (counterTape 2))
  obtain ⟨guardBound, executeGuard⟩ := guard_runs scalar isZero
  obtain ⟨guardTicks, final, guardCost, guardTrace, finalCandidate, finalLimit, foundEq, continueEq⟩ :=
    executeGuard (sizes rows) prepared 0 0 (fun _ => value) rows.isLt
      (by simp [sizes]) (by simp [sizes])
      (by have bound := rows.isLt; change rows.val * 1 ≤ 2; omega)
      ((readOutside (counterTape 1) (by decide) (by decide)).trans candidateEq)
      ((readTrace.readOnly_tape (counterTape 6) rfl).trans ((initTrace.readOnly_tape (counterTape 6) rfl).trans
        (represented.1 (counterTape 6) rfl))) limitEq
      ((readTrace.readOnly_tape matrixTape rfl).trans ((initTrace.readOnly_tape matrixTape rfl).trans
        (represented.1 matrixTape rfl)))
      (fun parameter => (readTrace.readOnly_tape (sizeTape parameter) rfl).trans
        ((initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      (fun name => readTrace.region name (initializedRegions name))
  have tail := readTrace.sequence (guard scalar isZero) (guardEntry (scalar.width Empty.elim)) readLimit_halt guardTrace
  have complete := initTrace.sequence _ (Sum.inl StandardSizeRead.entry) (by intro symbols; rfl) tail
  refine ⟨initTicks + (readTicks + guardTicks + 1) + 1, final, complete, foundEq, ?_⟩
  have continueValueEq : continueValue scalar isZero (sizes rows) (fun _ => value) 0 0
      (by simp [sizes]) =
      if 0 < rows.val then !value else false := by
    fin_cases rows <;> simp [continueValue, sizes]
  exact continueEq.trans (congrArg (encoded EncodedDomain.booleans (sizes rows)) continueValueEq)

end Polytime2.Examples.PivotGuard
