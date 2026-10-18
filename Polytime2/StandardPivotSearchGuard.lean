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

import Polytime2.StandardPivotSearchCalls

/-! # A pivot guard that tests the bound before matrix lookup -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

def continueValue (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) (sizes : Fin 3 → ℕ)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (candidate column : Fin (2 ^ sizes 0)) (columnValid : column.val < sizes 2) : Bool :=
  if valid : candidate.val < sizes 1 then
    isZero Empty.elim (array ⟨candidate.val * sizes 2 + column.val,
      StandardMatrixEntry.index_lt sizes candidate.val column.val valid columnValid⟩) else false

/-- All three branch outputs remain typed and bounded. An exhausted candidate
sets both status bits to false and never calls matrix lookup. An eligible
candidate preserves its index and tests the original matrix entry. -/
theorem guard_runs (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (rowFits : sizes 1 < 2 ^ sizes 0) (columnValid : column.val < sizes 2),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowFits⟩ →
      initial matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (guard scalar isZero) ticks
          (guardEntry (scalar.width Empty.elim)) (fun _ => 0) initial
          (guardExit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes candidate ∧
        final rowLimitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 1, rowFits⟩ ∧
        final foundTape = encoded EncodedDomain.booleans sizes (decide (candidate.val < sizes 1)) ∧
        final continueTape = encoded EncodedDomain.booleans sizes (continueValue scalar isZero sizes array candidate column columnValid) := by
  obtain ⟨compareBound, executeCompare⟩ := compare_runs scalar
  obtain ⟨readBound, executeRead⟩ := readEntry_runs scalar
  obtain ⟨testBound, executeTest⟩ := zeroTest_runs scalar isZero
  refine ⟨compareBound + readBound + MvPolynomial.C (testBound + 4), ?_⟩
  intro sizes initial candidate column array rowFits columnValid columnsFit capacity candidateEq columnEq limitEq arrayEq headers regions
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  obtain ⟨compareTicks, compared, compareCost, compareTrace, foundEq, difference, compareOutside⟩ :=
    executeCompare sizes initial candidate ⟨sizes 1, rowFits⟩ (headers 0) candidateEq limitEq
      (by simpa [domains, differenceTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using regions differenceTape)
      (by simpa [domains, foundTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
        show Nat.clog 2 2 = 1 from by decide] using regions foundTape)
  have comparedRegions : ∀ name, Region (width name) 0 (compared name) :=
    fun name => compareTrace.region name (regions name)
  have selected : found (MultiTape.read compared) = decide (candidate.val < sizes 1) := by
    unfold found MultiTape.read
    rw [foundEq, encoded_booleans]
    cases decide (candidate.val < sizes 1) <;> rfl
  by_cases valid : candidate.val < sizes 1
  · let within := StandardMatrixEntry.index_lt sizes candidate.val column.val valid columnValid
    let value := array (⟨candidate.val * sizes 2 + column.val, within⟩ : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length))
    obtain ⟨readTicks, afterRead, readCost, readTrace, elementEq, candidateAfterRead, readOutside⟩ :=
      executeRead sizes compared candidate column array within columnsFit valid columnValid capacity
        ((compareOutside (counterTape 1) (by decide) (by decide)).trans candidateEq)
        ((compareTrace.readOnly_tape (counterTape 6) rfl).trans columnEq)
        ((compareTrace.readOnly_tape matrixTape rfl).trans arrayEq)
        (fun parameter => (compareTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)) comparedRegions
    have readRegions : ∀ name, Region (width name) 0 (afterRead name) :=
      fun name => readTrace.region name (comparedRegions name)
    obtain ⟨testTicks, final, testCost, testTrace, continueEq, testOutside⟩ :=
      executeTest sizes afterRead value elementEq (by simpa [width, domains, unitTape, StandardFinitePredicate.unitDomain, EncodedDomain.constant,
          EncodedDomain.fixed, EncodedDomain.ofCodec] using readRegions unitTape)
        (by simpa [width, domains, continueTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
          show Nat.clog 2 2 = 1 from by decide] using readRegions continueTape)
    have readTestTrace := readTrace.sequence (zeroTest scalar isZero) StandardFiniteTable.entry
      (by intro symbols; simp [readEntry, MultiTape.wire, StandardMatrixEntry.halt]) testTrace
    have selectTrace := readTestTrace.branch_true found stop false
      (by simpa only [valid, decide_true] using selected)
      (by intro symbols; rfl)
    have complete := compareTrace.sequence (select scalar isZero) (.inl (.inl ()))
      (by intro symbols; simp [compare, MultiTape.wire, BinarySubtraction.algorithm, BinarySubtraction.exit,
        StandardBinaryArithmetic.algorithm, StandardBinaryArithmetic.exit, MultiTape.withExit]) selectTrace
    refine ⟨compareTicks + (readTicks + testTicks + 1 + 2) + 1, final, ?_, ?_,
      (testOutside (counterTape 1) (by decide)).trans candidateAfterRead, ?_, ?_, ?_⟩
    · simp only [map_add, MvPolynomial.eval_C]
      omega
    · simpa only [guard, guardEntry, guardExit, select, readTest, readTestEntry, readTestExit] using complete
    · exact (testOutside rowLimitTape (by decide)).trans ((readOutside 1).trans
        ((compareOutside rowLimitTape (by decide) (by decide)).trans limitEq))
    · exact (testOutside foundTape (by decide)).trans ((readOutside 3).trans foundEq)
    · have selectedValue : continueValue scalar isZero sizes array candidate column columnValid = isZero Empty.elim value := by
        unfold continueValue
        exact dite_eq_left valid
      exact continueEq.trans (congrArg (encoded EncodedDomain.booleans sizes) selectedValue.symm)
  · obtain ⟨old, length, oldEq⟩ := (comparedRegions continueTape).exists_buffer
    norm_num [width, domains, continueTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] at length
    obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp length
    have stopTrace := StandardTapeCommands.setBoolean_runs continueTape false width readOnly rfl
      (by norm_num [width, domains, continueTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec]) compared oldBit oldEq
    have booleanEq : buffer [Binary.data false] = encoded EncodedDomain.booleans sizes false := (encoded_booleans sizes false).symm
    rw [booleanEq] at stopTrace
    have selectTrace := stopTrace.branch_false found (readTest scalar isZero) (readTestEntry (scalar.width Empty.elim))
      (by simpa only [valid, decide_false] using selected)
      (by intro symbols; simp [StandardTapeCommands.setBoolean, MultiTape.wire, StandardTapeCommands.booleanMachine])
    have complete := compareTrace.sequence (select scalar isZero) (.inl (.inl ()))
      (by intro symbols; simp [compare, MultiTape.wire, BinarySubtraction.algorithm, BinarySubtraction.exit,
        StandardBinaryArithmetic.algorithm, StandardBinaryArithmetic.exit, MultiTape.withExit]) selectTrace
    refine ⟨compareTicks + (1 + 2) + 1, Function.update compared continueTape (encoded EncodedDomain.booleans sizes false),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [map_add, MvPolynomial.eval_C]
      omega
    · simpa only [guard, guardEntry, guardExit, select, stop] using complete
    · exact (Function.update_of_ne (by decide : counterTape 1 ≠ continueTape) _ _).trans
        ((compareOutside (counterTape 1) (by decide) (by decide)).trans candidateEq)
    · exact (Function.update_of_ne (by decide : rowLimitTape ≠ continueTape) _ _).trans
        ((compareOutside rowLimitTape (by decide) (by decide)).trans limitEq)
    · exact (Function.update_of_ne (by decide : foundTape ≠ continueTape) _ _).trans foundEq
    · have stoppedValue : continueValue scalar isZero sizes array candidate column columnValid = false := by
        unfold continueValue
        exact dite_eq_right valid
      exact (Function.update_self _ _ _).trans (congrArg (encoded EncodedDomain.booleans sizes) stoppedValue.symm)
end Polytime2.StandardPivotSearch
