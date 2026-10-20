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

import Polytime2.Machine.Pipeline

import Polytime2.GaussJordan.ClearTarget

/-! # Committing a cleared row and advancing its private counter

The enclosing column-clear loop owns the working matrix and target counter.
Each row-clear call reads those values immutably and writes a separate result;
the caller commits that result and advances through a separate counter output.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.StandardGaussJordanClearStep

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanClearTarget.TapeName Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev StageState (width : ℕ) : Fin 4 → Type
  | 0 => StandardGaussJordanClearTarget.State width
  | 1 | 3 => Fin 3
  | 2 => IncrementState
abbrev State (width : ℕ) := Pipeline.State (StageState width)

noncomputable instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardGaussJordanClearTarget.State width) := inferInstance
  letI (stage : Fin 4) : Fintype (StageState width stage) := by
    match stage with
    | 0 | 1 | 2 | 3 => infer_instance
  infer_instance

def dataTape (slot : Fin 18) : TapeName := .inl (StandardGaussJordanClearTarget.dataTape slot)
def workingTape : TapeName := .inl StandardGaussJordanClearTarget.inputTape
def columnTape : TapeName := .inl StandardGaussJordanClearTarget.columnTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanClearTarget.sizeTape parameter)
def nextTape : TapeName := .inr ()

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanClearTarget.domains enumeration name
  | .inr _ => EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => if name = StandardGaussJordanClearTarget.dataTape 1 ∨
      name = StandardGaussJordanClearTarget.inputTape then false
      else StandardGaussJordanClearTarget.readOnly name
  | .inr _ => false

def targetWiring : StandardGaussJordanClearTarget.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem targetWiring_apply (name : StandardGaussJordanClearTarget.TapeName) :
    targetWiring name = .inl name := rfl

def incrementWiring : Sum (Fin 3) Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl parameter => sizeTape parameter
    | .inr false => dataTape 1
    | .inr true => nextTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp_all [sizeTape, dataTape, nextTape, StandardGaussJordanClearTarget.sizeTape,
        StandardGaussJordanClearTarget.dataTape, StandardMatrixRows.sizeTape,
        StandardMatrixRows.dataTape]⟩

@[simp] theorem incrementWiring_apply (name : Sum (Fin 3) Bool) :
    incrementWiring name = match name with
      | .inl parameter => sizeTape parameter
      | .inr false => dataTape 1
      | .inr true => nextTape := rfl

noncomputable def commit : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy (dataTape 5) workingTape (by decide)

noncomputable def increment : Machine Alphabet IncrementState :=
  MultiTape.wire incrementWiring (StandardBinaryScan.algorithm BinaryScan.increment)

noncomputable def advance : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy nextTape (dataTape 1) (by decide)

noncomputable def components (enumeration : Scalar ≃ Fin cardinality) :
    ∀ stage, Machine Alphabet (StageState ((FieldRow.scalarDomain enumeration).width Empty.elim) stage)
  | 0 => MultiTape.wire targetWiring (StandardGaussJordanClearTarget.algorithm enumeration)
  | 1 => commit
  | 2 => increment
  | 3 => advance

def entries (width : ℕ) : ∀ stage, StageState width stage
  | 0 => StandardGaussJordanClearTarget.entry width
  | 1 | 3 => 0
  | 2 => .inl (.inl true)

def exits (width : ℕ) : ∀ stage, StageState width stage
  | 0 => StandardGaussJordanClearTarget.exit width
  | 1 | 3 => 2
  | 2 => .inr ()

noncomputable def machine (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  Pipeline.machine (components enumeration) (entries ((FieldRow.scalarDomain enumeration).width Empty.elim))

def entry (width : ℕ) : State width := Pipeline.position (entries width) 0
def exit (width : ℕ) : State width := none

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    machine enumeration (exit ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl


/-- One complete row-clear loop body. The working matrix and target counter
belong to the enclosing loop; each called routine preserves its own inputs. -/
theorem runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (sourceRow targetRow column : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      sizes 2 < 2 ^ sizes 0 → column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (domains enumeration workingTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (machine enumeration) ticks
          (entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        (∃ within : targetRow.val * sizes 2 + column.val <
            MvPolynomial.eval sizes StandardMatrixEntry.length,
          final workingTape = encoded (domains enumeration workingTape) sizes
            (StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
              (StandardGaussJordanClearTarget.additionOperation enumeration)
              sizes sourceRow targetRow sourceValid targetValid
              (Neg.neg (α := Scalar) (matrix ⟨targetRow.val * sizes 2 + column.val, within⟩))
              matrix (sizes 2))) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes targetRow) := by
  obtain ⟨targetBound, executeTarget⟩ := StandardGaussJordanClearTarget.runs enumeration
  obtain ⟨incrementBound, executeIncrement⟩ := StandardBinaryIncrement.wired_runs 0
    (fun sizes name => (domains enumeration name).width sizes) readOnly incrementWiring
    (by intro sizes name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)
  let matrixBound := ((FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨4 * (targetBound + incrementBound + 2 * matrixBound + 2 * MvPolynomial.X 0 + 7), ?_⟩
  intro sizes initial sourceRow targetRow column sourceValid targetValid matrix
    columnsFit columnValid capacity sourceEq targetEq columnEq matrixEq headers regions
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  obtain ⟨targetTicks, localFinal, targetCost, localTrace, ⟨within, localResult⟩⟩ :=
    executeTarget sizes (fun name => initial (.inl name)) sourceRow targetRow column
      sourceValid targetValid matrix columnsFit columnValid capacity sourceEq targetEq
      columnEq matrixEq headers (fun name => regions (.inl name))
  let resultMatrix := StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
    (StandardGaussJordanClearTarget.additionOperation enumeration)
    sizes sourceRow targetRow sourceValid targetValid
    (Neg.neg (α := Scalar) (matrix ⟨targetRow.val * sizes 2 + column.val, within⟩)) matrix (sizes 2)
  obtain ⟨afterTarget, targetTrace, afterTargetAt, _, targetImmutable⟩ :=
    localTrace.wire_restoring targetWiring width readOnly (fun _ => rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (fun _ => rfl)
  have targetFrame := targetTrace.frame ⟨regions, (by intros; rfl)⟩
  have resultEq : afterTarget (dataTape 5) =
      encoded (domains enumeration workingTape) sizes resultMatrix :=
    (afterTargetAt _).trans localResult
  have targetStill : afterTarget (dataTape 1) =
      encoded (EncodedDomain.binaryNaturals 0) sizes targetRow :=
    (targetImmutable _ rfl).trans targetEq
  have commitTrace := StandardTapeCommands.copy_encoded_runs
    (domains enumeration workingTape) sizes resultMatrix
    (dataTape 5) workingTape (by decide) width readOnly rfl rfl rfl afterTarget resultEq
    (targetFrame.1 workingTape)
  let afterCommit := Function.update afterTarget workingTape
    (encoded (domains enumeration workingTape) sizes resultMatrix)
  have commitFrame := commitTrace.frame targetFrame
  obtain ⟨incrementTicks, incremented, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes afterCommit targetRow
      ((Function.update_of_ne (by decide) _ _).trans targetStill)
      (fun parameter => (commitFrame.2 (sizeTape parameter) rfl).trans (headers parameter))
      (by simpa only [incrementWiring_apply, afterCommit,
        show width nextTape = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes]
        using commitFrame.1 nextTape)
  have incrementFrame := incrementTrace.frame commitFrame
  have advanceTrace := StandardTapeCommands.copy_encoded_runs
    (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes targetRow)
    nextTape (dataTape 1) (by decide) width readOnly rfl rfl rfl incremented nextEq
    (incrementFrame.1 (dataTape 1))
  simp only [EncodedDomain.binaryNaturals_width] at advanceTrace
  let final := Function.update incremented (dataTape 1)
    (encoded (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes targetRow))
  have finalMatrix : final workingTape =
      encoded (domains enumeration workingTape) sizes resultMatrix := by
    exact (Function.update_of_ne (by decide) _ _).trans
      ((incrementOutside workingTape (by decide)).trans (Function.update_self _ _ _))
  obtain ⟨total, totalCost, complete⟩ := Pipeline.runs_chain width readOnly (components enumeration)
    (entries ((FieldRow.scalarDomain enumeration).width Empty.elim)) (exits ((FieldRow.scalarDomain enumeration).width Empty.elim))
    ![initial, afterTarget, afterCommit, incremented, final]
    ![targetTicks, 2 * (domains enumeration workingTape).width sizes + 2, incrementTicks, 2 * sizes 0 + 2]
    (by intro stage symbols; fin_cases stage <;> rfl)
    (by intro stage; fin_cases stage <;> first
      | exact targetTrace
      | exact commitTrace
      | exact incrementTrace
      | exact advanceTrace)
  refine ⟨total, final, ?_, ?_, ⟨within, finalMatrix⟩, Function.update_self _ _ _⟩
  · simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
      Nat.add_zero, EncodedDomain.width] at totalCost
    rw [show (domains enumeration workingTape).widthPolynomial = matrixBound from rfl] at totalCost
    simp only [matrixBound, map_add, map_mul, map_ofNat, MvPolynomial.eval_X] at totalCost ⊢
    omega
  · simpa [machine, entry, exit, Fin.last, commit, advance, width, final,
      EncodedDomain.binaryNaturals_width] using complete
end Polytime2.StandardGaussJordanClearStep
