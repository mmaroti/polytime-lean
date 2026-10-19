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

import Polytime2.GaussJordan.PivotSearchLoop

/-! # Pivot search with internal workspace preparation -/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

noncomputable def initialization : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy startTape (counterTape 1) (by decide)

abbrev AlgorithmState (loopWidth : ℕ) :=
  Sum (Fin 3) (Sum StandardSizeRead.State (LoopState loopWidth))

noncomputable instance algorithmStateFinite (loopWidth : ℕ) : Fintype (AlgorithmState loopWidth) := by
  letI : Fintype (LoopState loopWidth) := by
    letI : Fintype (StandardMatrixEntry.State loopWidth) := inferInstance
    letI : Fintype (StandardFinitePredicate.State loopWidth) := inferInstance
    letI : Fintype (ReadTestState loopWidth) := inferInstance
    letI : Fintype (SelectState loopWidth) := inferInstance
    letI : Fintype (GuardState loopWidth) := inferInstance
    letI : Fintype LoopBodyState := inferInstance
    unfold LoopState
    infer_instance
  dsimp only [AlgorithmState]
  infer_instance

noncomputable def algorithm (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) :
    Machine Alphabet (AlgorithmState (scalar.width Empty.elim)) :=
  MultiTape.sequence initialization
    (MultiTape.sequence readLimit (loop scalar isZero) (loopEntry (scalar.width Empty.elim)))
    (.inl StandardSizeRead.entry)

def algorithmEntry (loopWidth : ℕ) : AlgorithmState loopWidth := .inl 0

def algorithmExit (loopWidth : ℕ) : AlgorithmState loopWidth :=
  .inr (.inr (loopExit loopWidth))

@[simp] theorem algorithm_halt (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) (symbols : Symbols Alphabet) :
    algorithm scalar isZero (algorithmExit (scalar.width Empty.elim)) symbols = none := rfl

/-! The workspace preparation, unary row-limit read, and bounded search are one
  caller-facing routine. Writable regions may begin with arbitrary contents. -/
theorem runs (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (start column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (startValid : start.val ≤ sizes 1) (columnValid : column.val < sizes 2)
      (rowFits : sizes 1 < 2 ^ sizes 0) (columnsFit : sizes 2 < 2 ^ sizes 0),
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial startTape = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial (counterTape 6) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial matrixTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly
          (algorithm scalar isZero) ticks
          (algorithmEntry (scalar.width Empty.elim))
          (fun _ => 0) initial
          (algorithmExit (scalar.width Empty.elim))
          (fun _ => 0) final ∧
        ∃ resultCount : Fin (2 ^ sizes 0), (start.val ≤ resultCount.val ∧ resultCount.val ≤ sizes 1) ∧
          final (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes resultCount ∧
          (∀ row : Fin (sizes 1), start.val ≤ row.val → row.val < resultCount.val →
            zeroAt scalar isZero sizes array column columnValid row = true) ∧
          (resultCount.val = sizes 1 ∨
            ∃ row : Fin (sizes 1), row.val = resultCount.val ∧
              zeroAt scalar isZero sizes array column columnValid row = false) ∧
          final foundTape = encoded EncodedDomain.booleans sizes (decide (resultCount.val < sizes 1)) ∧
          final continueTape = encoded EncodedDomain.booleans sizes false  := by
  obtain ⟨readBound, executeRead⟩ := readLimit_runs scalar
  obtain ⟨loopBound, executeLoop⟩ := loop_runs scalar isZero
  let initBound : MvPolynomial (Fin 3) ℕ :=
    2 * MvPolynomial.X 0 + 2
  refine ⟨initBound + readBound + loopBound + MvPolynomial.C (2 : ℕ), ?_⟩
  intro sizes initial start column array startValid columnValid rowFits columnsFit capacity
    startEq columnEq matrixEq headers regions
  have initTrace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0) sizes start
    startTape (counterTape 1) (by decide) (fun name => (domains scalar name).width sizes) readOnly
    rfl rfl rfl initial startEq (regions (counterTape 1))
  let initialized := Function.update initial (counterTape 1) (encoded (EncodedDomain.binaryNaturals 0) sizes start)
  have startAfterInit : initialized (counterTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start :=
    Function.update_self _ _ _
  let initTicks := 2 * sizes 0 + 2
  have initCost : initTicks ≤ MvPolynomial.eval sizes initBound := by simp [initTicks, initBound]
  simp only [EncodedDomain.binaryNaturals_width] at initTrace
  have initializedRegions : ∀ name, Region ((domains scalar name).width sizes) 0
      (initialized name) := fun name => initTrace.region name (regions name)
  obtain ⟨readTicks, prepared, readCost, readTrace, limitAfterRead,
      extraCanonical, readOutside⟩ :=
    executeRead sizes initialized rowFits
      (fun parameter => (initTrace.readOnly_tape (sizeTape parameter) rfl).trans
        (headers parameter))
      (by simpa [domains, rowLimitTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions rowLimitTape)
      (by simpa [domains, counterTape, StandardMatrixEntry.domains, StandardMatrixAddress.domains,
        EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions (counterTape 2))
  have preparedRegions : ∀ name, Region ((domains scalar name).width sizes) 0
      (prepared name) := fun name => readTrace.region name (initializedRegions name)
  have startPrepared : prepared (counterTape 1) =
      encoded (EncodedDomain.binaryNaturals 0) sizes start :=
    (readOutside (counterTape 1) (by decide) (by decide)).trans startAfterInit
  have columnPrepared : prepared (counterTape 6) =
      encoded (EncodedDomain.binaryNaturals 0) sizes column :=
    (readTrace.readOnly_tape (counterTape 6) rfl).trans
      ((initTrace.readOnly_tape (counterTape 6) rfl).trans columnEq)
  have matrixPrepared : prepared matrixTape =
      encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array :=
    (readTrace.readOnly_tape matrixTape rfl).trans
      ((initTrace.readOnly_tape matrixTape rfl).trans matrixEq)
  obtain ⟨loopTicks, final, resultCount, loopCost, loopTrace, resultBound,
      resultEq, resultPrefix, resultStop, finalFound, finalFlag⟩ :=
    executeLoop sizes prepared start column array startValid columnValid rowFits columnsFit
      capacity startPrepared columnPrepared limitAfterRead matrixPrepared
      (by
        intro parameter
        exact (readTrace.readOnly_tape (sizeTape parameter) rfl).trans
          ((initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      preparedRegions
  have completeRead := readTrace.sequence (loop scalar isZero)
    (loopEntry (scalar.width Empty.elim)) readLimit_halt loopTrace
  have complete := initTrace.sequence
    (MultiTape.sequence readLimit (loop scalar isZero) (loopEntry (scalar.width Empty.elim)))
    (Sum.inl StandardSizeRead.entry)
    (by intro symbols; rfl) completeRead
  refine ⟨initTicks + (readTicks + loopTicks + 1) + 1, final, ?_, ?_, resultCount,
    resultBound, resultEq, resultPrefix, resultStop, finalFound, finalFlag⟩
  · simp only [map_add, MvPolynomial.eval_C]
    omega
  · simpa only [algorithm, algorithmEntry, algorithmExit, initialization, initTicks] using complete

end Polytime2.StandardPivotSearch
