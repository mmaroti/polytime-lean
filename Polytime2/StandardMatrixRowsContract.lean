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

import Polytime2.StandardMatrixRowsLoop

/-! # Complete standard-convention matrix row operations -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

abbrev State (width : ℕ) := Sum (Pipeline.State InitStageState) (Sum StandardSizeRead.State (LoopState width))

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (Pipeline.State InitStageState) := inferInstance
  letI : Fintype (LoopState width) := inferInstance
  dsimp only [State]
  infer_instance

noncomputable def machine (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (State (scalar.width Empty.elim)) :=
  MultiTape.sequence initialization
    (MultiTape.sequence readLimit (loop writeSource scalar operation) (loopEntry (scalar.width Empty.elim)))
    (.inl StandardSizeRead.entry)

def entry (width : ℕ) : State width := .inl (Pipeline.position initEntry 0)
def exit (width : ℕ) : State width := .inr (.inr (loopExit width))

@[simp] theorem halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (symbols : Symbols Alphabet) : machine writeSource scalar operation (exit (scalar.width Empty.elim)) symbols = none := rfl

/-- Formatting, unary size reading, and the guarded row traversal form one
machine. No output or private tape requires a pre-existing valid encoding. -/
theorem runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (coefficient : scalar.Carrier Empty.elim)
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (_columnsFit : sizes 2 < 2 ^ sizes 0), sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (dataTape 3) = encoded scalar Empty.elim coefficient →
      initial inputTape = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (machine writeSource scalar operation) ticks
          (entry (scalar.width Empty.elim)) (fun _ => 0) initial (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes
          (processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array (sizes 2)) := by
  obtain ⟨readBound, executeRead⟩ := readLimit_runs scalar
  obtain ⟨loopBound, executeLoop⟩ := loop_runs writeSource scalar operation
  let matrixBound := (scalar.constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨3 * (2 * matrixBound + 2 * MvPolynomial.X 0 + 3) +
    readBound + loopBound + 2, ?_⟩
  intro sizes initial sourceRow targetRow sourceValid targetValid coefficient array fits capacity
    sourceEq targetEq coefficientEq arrayEq headers regions
  obtain ⟨initTicks, initialized, initCost, initTrace, workEq, matrixEq, columnEq⟩ :=
    initialization_runs scalar sizes array initial arrayEq (headers 0) regions
  have initializedRegions : ∀ name, Region ((domains scalar name).width sizes) 0 (initialized name) :=
    fun name => initTrace.region name (regions name)
  obtain ⟨readTicks, prepared, readCost, readTrace, limitEq, scratchEq, readOutside⟩ :=
    executeRead sizes initialized fits
      (fun parameter => (initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (by simpa [domains, limitTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions limitTape)
      (by simpa [domains, dataTape, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains,
        EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using initializedRegions (dataTape 12))
  obtain ⟨loopTicks, final, loopCost, loopTrace, finalMatrix, finalColumn⟩ :=
    executeLoop sizes prepared sourceRow targetRow sourceValid targetValid coefficient array fits capacity
      ((readTrace.readOnly_tape (dataTape 0) rfl).trans ((initTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq))
      ((readTrace.readOnly_tape (dataTape 1) rfl).trans ((initTrace.readOnly_tape (dataTape 1) rfl).trans targetEq))
      ((readOutside (dataTape 2) (by decide) (by decide)).trans columnEq)
      ((readTrace.readOnly_tape (dataTape 3) rfl).trans ((initTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq))
      ((readOutside (dataTape 4) (by decide) (by decide)).trans workEq)
      ((readOutside (dataTape 5) (by decide) (by decide)).trans matrixEq) limitEq
      (fun parameter => (readTrace.readOnly_tape (sizeTape parameter) rfl).trans
        ((initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      (fun name => readTrace.region name (initializedRegions name))
  have tail := readTrace.sequence (loop writeSource scalar operation) (loopEntry (scalar.width Empty.elim))
    readLimit_halt loopTrace
  have complete := initTrace.sequence _ (Sum.inl StandardSizeRead.entry) (by intro symbols; rfl) tail
  refine ⟨initTicks + (readTicks + loopTicks + 1) + 1, final, ?_, ?_, finalMatrix⟩
  · simp only [EncodedDomain.width] at initCost
    simp only [matrixBound, EncodedDomain.width, map_add, map_mul, map_ofNat, MvPolynomial.eval_C, MvPolynomial.eval_X]
    omega
  · simpa only [machine, entry, exit] using complete

def outputTapes : Unit ↪ TapeName := oneTape (dataTape 5)

/-- The public arguments are immutable indices, coefficient, and original
matrix, alongside the unary sizes. The separate result and all private tapes
start arbitrary; only the result must return a valid encoding. Heads are restored. -/
theorem contract (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    CallingConvention.Realizes (domains scalar) readOnly sizeTapes outputTapes (machine writeSource scalar operation)
      (entry (scalar.width Empty.elim)) (exit (scalar.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        output () = processed writeSource scalar operation sizes
          (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩) sourceValid targetValid
          (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩) (sizes 2)) := by
  classical
  obtain ⟨bound, execute⟩ := runs writeSource scalar operation
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), halt writeSource scalar operation, bound, ?_⟩
  intro sizes input initial valid represented headers
  let resultArray := processed writeSource scalar operation sizes (input ⟨dataTape 0, rfl⟩)
    (input ⟨dataTape 1, rfl⟩) valid.1 valid.2.1 (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩) (sizes 2)
  obtain ⟨ticks, final, cost, trace, resultEq⟩ :=
    execute sizes initial (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩) valid.1 valid.2.1
      (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩) valid.2.2.1 valid.2.2.2
      (represented.1 (dataTape 0) rfl) (represented.1 (dataTape 1) rfl)
      ((represented.1 (dataTape 3) rfl).trans (encoded_constant scalar sizes _)) (represented.1 inputTape rfl) headers represented.region
  let output : Outputs (domains scalar) outputTapes sizes := fun _ => resultArray
  refine ⟨ticks, output, final, cost, trace, ⟨valid.1, valid.2.1, rfl⟩, ?_⟩
  intro name
  cases name
  exact resultEq

end Polytime2.StandardMatrixRows
