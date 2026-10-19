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

import Polytime2.GaussJordan.ClearAlgorithm

/-! # Standard-convention swap-normalize-clear pivot controller

Candidate, pivot, column, and original matrix are immutable arguments. A
private matrix supplies each row call; separate results are committed between
calls. The original candidate entry is loaded before swapping and retained as
the normalization coefficient until column clearing begins.
-/

namespace Polytime2.StandardGaussJordanPivot

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanClear.TapeName (Fin 2)
abbrev Alphabet := CallingConvention.Alphabet TapeName

instance tapeNamesDecidableEq : DecidableEq TapeName := inferInstance
instance tapeNamesFinite : Fintype TapeName := inferInstance

def dataTape (slot : Fin 18) : TapeName := .inl (StandardGaussJordanClear.dataTape slot)
def pivotTape : TapeName := dataTape 0
def candidateTape : TapeName := .inr 0
def originalTape : TapeName := .inr 1
def workingTape : TapeName := .inl StandardGaussJordanClear.originalTape
def resultTape : TapeName := .inl StandardGaussJordanClear.workingTape
def columnTape : TapeName := .inl StandardGaussJordanClear.columnTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanClear.sizeTape parameter)

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanClear.domains enumeration name
  | .inr slot => if slot = 0 then EncodedDomain.binaryNaturals 0
      else (FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length

def readOnly : TapeName → Bool
  | .inl name => if name = StandardGaussJordanClear.originalTape then false
      else StandardGaussJordanClear.readOnly name
  | .inr _ => true

def rowTarget (name : StandardMatrixRows.TapeName) : TapeName :=
  if name = StandardMatrixRows.dataTape 0 then candidateTape
  else if name = StandardMatrixRows.dataTape 1 then pivotTape
  else if name = StandardMatrixRows.inputTape then workingTape
  else .inl (StandardGaussJordanClear.rowsWiring name)

theorem rowTarget_injective : Function.Injective rowTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)

def rowWiring : StandardMatrixRows.TapeName ↪ TapeName := ⟨rowTarget, rowTarget_injective⟩

def lookupTarget : StandardMatrixEntry.TapeName → TapeName
  | .inl (.inl parameter) => sizeTape parameter
  | .inl (.inr slot) => if slot = 1 then candidateTape else if slot = 6 then columnTape
      else dataTape (StandardGaussJordanClearTarget.lookupSlot slot)
  | .inr false => workingTape
  | .inr true => dataTape 3

theorem lookupTarget_injective : Function.Injective lookupTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;>
    simp_all [lookupTarget, candidateTape, columnTape, workingTape, dataTape, sizeTape,
      StandardGaussJordanClearTarget.lookupSlot, StandardGaussJordanClear.originalTape,
      StandardGaussJordanClear.columnTape, StandardGaussJordanClear.dataTape,
      StandardGaussJordanClear.sizeTape, StandardGaussJordanClearInterval.columnTape,
      StandardGaussJordanClearInterval.dataTape, StandardGaussJordanClearInterval.sizeTape,
      StandardGaussJordanClearStep.columnTape, StandardGaussJordanClearStep.dataTape,
      StandardGaussJordanClearStep.sizeTape, StandardGaussJordanClearTarget.columnTape,
      StandardGaussJordanClearTarget.dataTape, StandardGaussJordanClearTarget.sizeTape,
      StandardMatrixRows.dataTape, StandardMatrixRows.sizeTape]

def lookupWiring : StandardMatrixEntry.TapeName ↪ TapeName :=
  ⟨lookupTarget, lookupTarget_injective⟩

def clearWiring : StandardGaussJordanClear.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def prepareMatrix : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy originalTape workingTape (by decide)

noncomputable def lookup (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixEntry.State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire lookupWiring (StandardMatrixEntry.machine ((FieldRow.scalarDomain enumeration).width Empty.elim))

noncomputable def swapRows (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixRows.State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire rowWiring (StandardMatrixRows.machine true (FieldRow.scalarDomain enumeration)
    (fun _ => MatrixRowField.swap (Scalar := Scalar)))

noncomputable def normalizeRow (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixRows.State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire rowWiring (StandardMatrixRows.machine false (FieldRow.scalarDomain enumeration)
    (fun _ => MatrixRowField.normalize (Scalar := Scalar)))

noncomputable def commit : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy (dataTape 5) workingTape (by decide)

noncomputable def clearColumn (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanClear.AlgorithmState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire clearWiring (StandardGaussJordanClear.algorithm enumeration)

abbrev State (scalarWidth : ℕ) := Sum (Fin 3)
  (Sum (StandardMatrixEntry.State scalarWidth)
    (Sum (StandardMatrixRows.State scalarWidth)
      (Sum (Fin 3) (Sum (StandardMatrixRows.State scalarWidth)
        (Sum (Fin 3) (StandardGaussJordanClear.AlgorithmState scalarWidth))))))

noncomputable instance statesFinite (scalarWidth : ℕ) : Fintype (State scalarWidth) := by
  letI : Fintype (StandardMatrixEntry.State scalarWidth) := inferInstance
  letI : Fintype (StandardMatrixRows.State scalarWidth) := inferInstance
  letI : Fintype (StandardGaussJordanClear.AlgorithmState scalarWidth) := inferInstance
  dsimp only [State]
  infer_instance

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (State
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  let width := (FieldRow.scalarDomain enumeration).width Empty.elim
  MultiTape.sequence prepareMatrix
    (MultiTape.sequence (lookup enumeration)
      (MultiTape.sequence (swapRows enumeration)
        (MultiTape.sequence commit
          (MultiTape.sequence (normalizeRow enumeration)
            (MultiTape.sequence commit (clearColumn enumeration)
              (StandardGaussJordanClear.algorithmEntry width))
            (Sum.inl 0))
          (Sum.inl (StandardMatrixRows.entry width)))
        (Sum.inl 0))
      (Sum.inl (StandardMatrixRows.entry width)))
    (Sum.inl (StandardMatrixEntry.entry width))

def entry (scalarWidth : ℕ) : State scalarWidth := .inl 0

def exit (scalarWidth : ℕ) : State scalarWidth :=
  .inr (.inr (.inr (.inr (.inr (.inr (StandardGaussJordanClear.algorithmExit scalarWidth))))))

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    algorithm enumeration (exit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [algorithm, exit, MultiTape.sequence, clearColumn, MultiTape.wire,
    StandardGaussJordanClear.algorithm_halt]

omit [Field Scalar] in
/-- The private matrix copy is the only effect of the entry stage. It derives
its extent from the immutable encoded original, including an empty array. -/
theorem prepareMatrix_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : (domains enumeration originalTape).Carrier sizes) (initial : Tapes Alphabet)
    (matrixEq : initial originalTape = encoded (domains enumeration originalTape) sizes matrix)
    (region : Region ((domains enumeration workingTape).width sizes) 0 (initial workingTape)) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly prepareMatrix
      (2 * (domains enumeration originalTape).width sizes + 2) 0 (fun _ => 0) initial
      2 (fun _ => 0)
      (Function.update initial workingTape (encoded (domains enumeration originalTape) sizes matrix)) := by
  exact StandardTapeCommands.copy_encoded_runs (domains enumeration originalTape) sizes matrix
    originalTape workingTape (by decide) (fun name => (domains enumeration name).width sizes)
    readOnly rfl rfl rfl initial matrixEq region

omit [Field Scalar] in
/-- Capture the candidate entry before swapping. The coefficient output is
fully overwritten; the candidate, column, and private matrix remain unchanged. -/
theorem lookup_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (candidate column : Fin (2 ^ sizes 0))
      (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes)
      (within : candidate.val * sizes 2 + column.val <
        MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → candidate.val < sizes 1 → column.val < sizes 2 →
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (domains enumeration workingTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (lookup enumeration) ticks
          (StandardMatrixEntry.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardMatrixEntry.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim
          (matrix ⟨candidate.val * sizes 2 + column.val, within⟩) ∧
        (∀ name, name ∉ Set.range lookupWiring → final name = initial name) ∧
        (∀ name, StandardMatrixEntry.readOnly name = true →
          final (lookupWiring name) = initial (lookupWiring name)) := by
  let scalar := FieldRow.scalarDomain enumeration
  obtain ⟨bound, execute⟩ := (StandardMatrixEntry.contract scalar.constant
    (scalar.width Empty.elim) (fun _ => by simp [EncodedDomain.constant, EncodedDomain.ofCodec])).wired_runs lookupWiring
  refine ⟨bound, ?_⟩
  intro sizes initial candidate column matrix within columnsFit candidateValid columnValid
    capacity candidateEq columnEq matrixEq headers regions
  let input := StandardMatrixEntry.inputValues scalar.constant sizes candidate column matrix
  have sameDomain : ∀ name, domains enumeration (lookupWiring name) =
      StandardMatrixEntry.domains scalar.constant name := by
    intro name
    fin_cases name <;> rfl
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; rw [sameDomain name])
      (by intro name; fin_cases name <;> decide)
      ⟨columnsFit, candidateValid, columnValid, capacity⟩
      (by
        intro name readonly
        cases name with
        | inl name => cases name with
          | inl parameter =>
            change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
            rw [encoded_unary]
            exact headers parameter
          | inr slot =>
            fin_cases slot <;> first | exact candidateEq | exact columnEq |
              norm_num [StandardMatrixEntry.readOnly, StandardMatrixAddress.readOnly] at readonly
        | inr output => cases output with
          | false => exact matrixEq
          | true => contradiction)
      (by intro name writable; exact regions (lookupWiring name)) headers
  obtain ⟨otherWithin, valueEq⟩ := correct
  change output () = matrix ⟨candidate.val * sizes 2 + column.val, otherWithin⟩ at valueEq
  have result := canonical ()
  rw [valueEq] at result
  exact ⟨ticks, final, cost, trace, result.trans (encoded_constant scalar sizes _), outside, immutable⟩

end Polytime2.StandardGaussJordanPivot

