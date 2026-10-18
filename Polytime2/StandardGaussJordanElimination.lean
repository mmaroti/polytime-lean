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

import Polytime2.StandardGaussJordanColumnAlgorithm

/-! # Standard-convention outer Gauss–Jordan controller

The column routine reads the private current matrix, pivot, and column without
changing them. Between calls, the caller commits the separate matrix and row
outputs and increments the column through a separate counter output.
-/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanColumn.TapeName (Fin 5)
abbrev Alphabet := CallingConvention.Alphabet TapeName

instance tapeNamesDecidableEq : DecidableEq TapeName := by
  letI : DecidableEq StandardGaussJordanColumn.TapeName := inferInstance
  infer_instance

instance tapeNamesFinite : Fintype TapeName := by
  letI : Fintype StandardGaussJordanColumn.TapeName := inferInstance
  infer_instance

def pivotTape : TapeName := .inl StandardGaussJordanColumn.pivotTape
def columnTape : TapeName := .inl StandardGaussJordanColumn.columnTape
def workingTape : TapeName := .inl StandardGaussJordanColumn.originalTape
def resultTape : TapeName := .inl StandardGaussJordanColumn.resultTape
def nextRowTape : TapeName := .inl StandardGaussJordanColumn.nextRowTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanColumn.sizeTape parameter)
def inputTape : TapeName := .inr 0
def limitTape : TapeName := .inr 1
def differenceTape : TapeName := .inr 2
def guardTape : TapeName := .inr 3
def nextColumnTape : TapeName := .inr 4

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanColumn.domains enumeration name
  | .inr name => if name = 0 then
      (FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length
      else if name = 3 then EncodedDomain.booleans else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => if name = StandardGaussJordanColumn.pivotTape ∨
      name = StandardGaussJordanColumn.columnTape ∨
      name = StandardGaussJordanColumn.originalTape then false
      else StandardGaussJordanColumn.readOnly name
  | .inr name => decide (name = 0)

def columnWiring : StandardGaussJordanColumn.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem columnWiring_apply (name : StandardGaussJordanColumn.TapeName) :
    columnWiring name = .inl name := rfl

def sizeTapes : Fin 3 ↪ TapeName := StandardGaussJordanColumn.sizeTapes.trans columnWiring

def incrementWiring : Sum (Fin 3) Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl parameter => sizeTape parameter
    | .inr false => columnTape | .inr true => nextColumnTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

def guardWiring : Sum Unit (Fin 4) ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => columnTape | 1 => limitTape | 2 => differenceTape | _ => guardTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev GuardState := Sum StandardBinaryArithmetic.State Unit
abbrev BodyState (scalarWidth : ℕ) :=
  Sum (StandardGaussJordanColumn.AlgorithmState scalarWidth)
    (Sum (Fin 3) (Sum (Fin 3) (Sum IncrementState (Fin 3))))

noncomputable instance bodyStatesFinite (scalarWidth : ℕ) :
    Fintype (BodyState scalarWidth) := by
  letI : Fintype (StandardGaussJordanColumn.AlgorithmState scalarWidth) := inferInstance
  dsimp only [BodyState, IncrementState]
  infer_instance

noncomputable def column (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanColumn.AlgorithmState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire columnWiring (StandardGaussJordanColumn.algorithm enumeration)

noncomputable def commitMatrix : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy resultTape workingTape (by decide)

noncomputable def commitRow : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy nextRowTape pivotTape (by decide)

noncomputable def increment : Machine Alphabet IncrementState :=
  MultiTape.wire incrementWiring (StandardBinaryScan.algorithm BinaryScan.increment)

noncomputable def commitColumn : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy nextColumnTape columnTape (by decide)

noncomputable def body (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (BodyState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence (column enumeration)
    (MultiTape.sequence commitMatrix
      (MultiTape.sequence commitRow
        (MultiTape.sequence increment commitColumn 0) (.inl (.inl (.inl true))))
      (.inl 0)) (.inl 0)

def bodyEntry (scalarWidth : ℕ) : BodyState scalarWidth :=
  .inl (StandardGaussJordanColumn.algorithmEntry scalarWidth)

def bodyExit (scalarWidth : ℕ) : BodyState scalarWidth :=
  .inr (.inr (.inr (.inr 2)))

noncomputable def guard : Machine Alphabet GuardState :=
  MultiTape.wire guardWiring BinarySubtraction.algorithm

def continues (symbols : Symbols Alphabet) : Bool := decide (symbols guardTape = Binary.data true)

abbrev LoopState (scalarWidth : ℕ) :=
  Sum (Sum GuardState (BodyState scalarWidth)) Unit

noncomputable instance loopStatesFinite (scalarWidth : ℕ) :
    Fintype (LoopState scalarWidth) := by
  letI : Fintype (BodyState scalarWidth) := inferInstance
  dsimp only [LoopState, GuardState]
  infer_instance

noncomputable def loop (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (LoopState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.withExit (MultiTape.whileMachine guard (body enumeration) BinarySubtraction.entry
    (bodyEntry
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) continues)

def loopEntry (scalarWidth : ℕ) : LoopState scalarWidth :=
  .inl (.inl BinarySubtraction.entry)

def loopExit (scalarWidth : ℕ) : LoopState scalarWidth := .inr ()

@[simp] theorem column_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    column enumeration (StandardGaussJordanColumn.algorithmExit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

@[simp] theorem guard_halt (symbols : Symbols Alphabet) :
    guard BinarySubtraction.exit symbols = none := rfl

@[simp] theorem body_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    body enumeration (bodyExit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

@[simp] theorem loop_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    loop enumeration (loopExit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

/-- One column call temporarily preserves its arguments even though the outer
controller owns and may replace those arguments between iterations. -/
theorem column_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow columnIndex : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_pivotBound : pivotRow.val ≤ sizes 1) (columnValid : columnIndex.val < sizes 2),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ∃ nextRow : Fin (2 ^ sizes 0), ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (column enumeration) ticks
          (StandardGaussJordanColumn.algorithmEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (StandardGaussJordanColumn.algorithmExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).1 ∧
        nextRow.val = (GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).2 ∧
        nextRow.val ≤ sizes 1 ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes nextRow ∧
        (∀ name, name ∉ Set.range columnWiring → final name = initial name) ∧
        (∀ name, StandardGaussJordanColumn.readOnly name = true →
          final (columnWiring name) = initial (columnWiring name)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanColumn.runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial pivotRow columnIndex matrix pivotBound columnValid rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, nextEq⟩ :=
    execute sizes (fun name => initial (.inl name)) pivotRow columnIndex matrix pivotBound columnValid
      rowsFit columnsFit capacity pivotEq columnEq matrixEq headers (fun name => regions (.inl name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring columnWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanColumn.pivotTape ∨
        name = StandardGaussJordanColumn.columnTape ∨
        name = StandardGaussJordanColumn.originalTape then false
        else StandardGaussJordanColumn.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => rfl)
  have nextBound := (GaussJordan.columnStep_row_bound matrix pivotRow.val
    ⟨columnIndex.val, columnValid⟩ pivotBound).2
  let nextRow : Fin (2 ^ sizes 0) :=
    ⟨(GaussJordan.columnStep matrix pivotRow.val ⟨columnIndex.val, columnValid⟩).2,
      lt_of_le_of_lt nextBound rowsFit⟩
  refine ⟨ticks, final, nextRow, cost, trace,
    (located _).trans resultEq, rfl, nextBound,
    (located _).trans nextEq, ?_, ?_⟩
  · intro name absent
    exact outside name absent
  · intro name fixed
    exact immutable name fixed

end Polytime2.StandardGaussJordanElimination
