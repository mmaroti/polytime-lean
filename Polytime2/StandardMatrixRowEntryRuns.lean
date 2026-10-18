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

import Polytime2.StandardMatrixRowEntryReplace

/-! # Complete execution of one column of a matrix row operation -/

namespace Polytime2.StandardMatrixRowEntry

open MultiTape CallingConvention

private theorem replace_scalar_preserved (source : Bool) (initial final : Tapes Alphabet)
    (outside : ∀ name, name ∉ Set.range (replaceWiring source) → final name = initial name)
    (immutable : ∀ name, StandardMatrixReplace.readOnly name = true →
      final (replaceWiring source name) = initial (replaceWiring source name))
    (name : Fin 18) (scalarSlot : 7 ≤ name.val ∧ name.val ≤ 10) : final (.inr name) = initial (.inr name) := by
  apply preserved_of_wiring (replaceWiring source) StandardMatrixReplace.readOnly initial final outside immutable
  intro localName equal
  cases source <;> fin_cases localName <;> first
    | rfl
    | have coordinate := congrArg (fun name : TapeName => match name with | .inl _ => 0 | .inr slot => slot.val) equal
      norm_num [replaceWiring_apply, addressSlot] at coordinate
      omega

/-- Both matrix reads precede both writes, so coincident source and target
indices still use the original entries. Only the result matrix needs an
encoding on return; private scratch needs only bounded regions. -/
theorem runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (coefficient : scalar.Carrier Empty.elim)
      (sourceWithin : sourceRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length)
      (targetWithin : targetRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → sourceRow.val < sizes 1 → targetRow.val < sizes 1 →
      column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (.inr 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (.inr 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (.inr 2) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial (.inr 3) = encoded scalar Empty.elim coefficient →
      initial (.inr 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (.inl parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨sourceRow.val * sizes 2 + column.val, sourceWithin⟩
      let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨targetRow.val * sizes 2 + column.val, targetWithin⟩
      let result := effectiveOperation writeSource scalar operation Empty.elim coefficient (array sourceIndex) (array targetIndex)
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (machine writeSource scalar operation) ticks
          (entry (scalar.width Empty.elim)) (fun _ => 0) initial (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (.inr 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes
          (Function.update (Function.update array sourceIndex result.1) targetIndex result.2)  := by
  obtain ⟨sourceReadBound, readSource⟩ := access_runs false scalar
  obtain ⟨targetReadBound, readTarget⟩ := access_runs true scalar
  obtain ⟨scalarBound, combineScalars⟩ := combine_runs writeSource scalar operation
  obtain ⟨sourceWriteBound, writeSourceEntry⟩ := replace_runs true scalar
  obtain ⟨targetWriteBound, writeTargetEntry⟩ := replace_runs false scalar
  refine ⟨sourceReadBound + targetReadBound + sourceWriteBound + targetWriteBound + MvPolynomial.C (scalarBound + 4), ?_⟩
  intro sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin columnsFit
    sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers regions
  intro sourceIndex targetIndex result
  obtain ⟨sourceTicks, afterSource, sourceCost, sourceTrace, sourceValueEq, sourceOutside, sourceImmutable⟩ :=
    readSource sizes initial sourceRow column array sourceWithin columnsFit sourceValid columnValid capacity
      sourceEq columnEq arrayEq headers regions
  have sourceRegions : ∀ name, Region ((domains scalar name).width sizes) 0 (afterSource name) :=
    fun name => sourceTrace.region name (regions name)
  obtain ⟨targetTicks, afterTarget, targetCost, targetTrace, targetValueEq, targetOutside, targetImmutable⟩ :=
    readTarget sizes afterSource targetRow column array targetWithin columnsFit targetValid columnValid capacity
      ((sourceTrace.readOnly_tape (.inr 1) rfl).trans targetEq)
      ((sourceTrace.readOnly_tape (.inr 2) rfl).trans columnEq)
      ((sourceTrace.readOnly_tape (.inr 4) rfl).trans arrayEq)
      (fun parameter => (sourceTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter)) sourceRegions
  have sourcePreserved : afterTarget (.inr 7) = afterSource (.inr 7) := by
    apply preserved_of_wiring (accessWiring true) StandardMatrixEntry.readOnly afterSource afterTarget targetOutside targetImmutable
    intro localName equal
    fin_cases localName <;> first
      | rfl
      | have coordinate := congrArg (fun name : TapeName => match name with | .inl _ => 0 | .inr slot => slot.val) equal
        norm_num [accessWiring_apply, addressSlot] at coordinate
  have targetRegions : ∀ name, Region ((domains scalar name).width sizes) 0 (afterTarget name) :=
    fun name => targetTrace.region name (sourceRegions name)
  obtain ⟨combineTicks, afterCombine, combineCost, combineTrace, newSourceEq, newTargetEq, combineOutside, combineImmutable⟩ :=
    combineScalars sizes afterTarget coefficient (array sourceIndex) (array targetIndex)
      ((targetTrace.readOnly_tape (.inr 3) rfl).trans ((sourceTrace.readOnly_tape (.inr 3) rfl).trans coefficientEq))
      (sourcePreserved.trans sourceValueEq) targetValueEq targetRegions
  have combineRegions : ∀ name, Region ((domains scalar name).width sizes) 0 (afterCombine name) :=
    fun name => combineTrace.region name (targetRegions name)
  obtain ⟨firstWriteTicks, afterFirstWrite, firstWriteCost, firstWriteTrace, intermediateEq, firstWriteOutside, firstWriteImmutable⟩ :=
    writeSourceEntry sizes afterCombine sourceRow column array result.1 sourceWithin
      columnsFit sourceValid columnValid capacity
      ((combineTrace.readOnly_tape (.inr 0) rfl).trans ((targetTrace.readOnly_tape (.inr 0) rfl).trans
        ((sourceTrace.readOnly_tape (.inr 0) rfl).trans sourceEq)))
      ((combineTrace.readOnly_tape (.inr 2) rfl).trans ((targetTrace.readOnly_tape (.inr 2) rfl).trans
        ((sourceTrace.readOnly_tape (.inr 2) rfl).trans columnEq)))
      ((combineTrace.readOnly_tape (.inr 4) rfl).trans ((targetTrace.readOnly_tape (.inr 4) rfl).trans
        ((sourceTrace.readOnly_tape (.inr 4) rfl).trans arrayEq)))
      newSourceEq
      (fun parameter => (combineTrace.readOnly_tape (.inl parameter) rfl).trans
        ((targetTrace.readOnly_tape (.inl parameter) rfl).trans
          ((sourceTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter)))) combineRegions
  have firstWriteRegions : ∀ name, Region ((domains scalar name).width sizes) 0 (afterFirstWrite name) :=
    fun name => firstWriteTrace.region name (combineRegions name)
  have firstScalars := replace_scalar_preserved true afterCombine afterFirstWrite firstWriteOutside firstWriteImmutable
  obtain ⟨lastWriteTicks, final, lastWriteCost, lastWriteTrace, resultEq, lastWriteOutside, lastWriteImmutable⟩ :=
    writeTargetEntry sizes afterFirstWrite targetRow column (Function.update array sourceIndex result.1) result.2 targetWithin
      columnsFit targetValid columnValid capacity
      ((firstWriteTrace.readOnly_tape (.inr 1) rfl).trans ((combineTrace.readOnly_tape (.inr 1) rfl).trans
        ((targetTrace.readOnly_tape (.inr 1) rfl).trans ((sourceTrace.readOnly_tape (.inr 1) rfl).trans targetEq))))
      ((firstWriteTrace.readOnly_tape (.inr 2) rfl).trans ((combineTrace.readOnly_tape (.inr 2) rfl).trans
        ((targetTrace.readOnly_tape (.inr 2) rfl).trans ((sourceTrace.readOnly_tape (.inr 2) rfl).trans columnEq))))
      intermediateEq ((firstScalars 10 (by decide)).trans newTargetEq)
      (fun parameter => (firstWriteTrace.readOnly_tape (.inl parameter) rfl).trans
        ((combineTrace.readOnly_tape (.inl parameter) rfl).trans ((targetTrace.readOnly_tape (.inl parameter) rfl).trans
          ((sourceTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter))))) firstWriteRegions
  have writes := firstWriteTrace.sequence _ (StandardMatrixReplace.entry (scalar.width Empty.elim))
    (by intro symbols; simp [replace, MultiTape.wire]) lastWriteTrace
  have combined := combineTrace.sequence _ (Sum.inl (StandardMatrixReplace.entry (scalar.width Empty.elim)))
    (by intro symbols; simp [combine, MultiTape.wire, StandardRowCombine.algorithm]) writes
  have readThenCombined := targetTrace.sequence _ (Sum.inl StandardRowCombine.entry)
    (by intro symbols; simp [access, MultiTape.wire]) combined
  have complete := sourceTrace.sequence _ (Sum.inl (StandardMatrixEntry.entry (scalar.width Empty.elim)))
    (by intro symbols; simp [access, MultiTape.wire]) readThenCombined
  refine ⟨sourceTicks + (targetTicks + (combineTicks + (firstWriteTicks + lastWriteTicks + 1) + 1) + 1) + 1,
    final, ?_, ?_, resultEq⟩
  · simp only [map_add, MvPolynomial.eval_C]
    omega
  · simpa only [machine, entry, exit] using complete
end Polytime2.StandardMatrixRowEntry
