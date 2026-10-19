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

import Polytime2.GaussJordan.PivotAlgorithm
import Polytime2.GaussJordan.PivotSearchField

/-! # Shared standard-convention workspace for a Gauss–Jordan column

Search shares the immutable pivot, column, and matrix arguments with the pivot
routine. Its selected candidate is the pivot routine's private candidate tape.
Only the remaining writable search tapes are added to the workspace.
-/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev SearchScratch := { name : StandardPivotSearch.TapeName //
  StandardPivotSearch.readOnly name = false ∧ name ≠ StandardPivotSearch.counterTape 1 }

abbrev TapeName := Sum StandardGaussJordanPivot.TapeName (Sum SearchScratch Unit)
abbrev Alphabet := CallingConvention.Alphabet TapeName

instance tapeNamesDecidableEq : DecidableEq TapeName := by
  letI : DecidableEq StandardPivotSearch.TapeName := inferInstance
  letI : DecidableEq SearchScratch := inferInstance
  letI : DecidableEq (Sum SearchScratch Unit) := inferInstance
  infer_instance
instance tapeNamesFinite : Fintype TapeName := inferInstance

def pivotTape : TapeName := .inl StandardGaussJordanPivot.pivotTape
def candidateTape : TapeName := .inl StandardGaussJordanPivot.candidateTape
def columnTape : TapeName := .inl StandardGaussJordanPivot.columnTape
def originalTape : TapeName := .inl StandardGaussJordanPivot.originalTape
def resultTape : TapeName := .inl StandardGaussJordanPivot.resultTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanPivot.sizeTape parameter)
def nextRowTape : TapeName := .inr (.inr ())

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanPivot.domains enumeration name
  | .inr (.inl name) => StandardPivotSearch.domains (FieldRow.scalarDomain enumeration) name.val
  | .inr (.inr _) => EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => if name = StandardGaussJordanPivot.candidateTape then false
      else StandardGaussJordanPivot.readOnly name
  | .inr _ => false

def searchTarget (name : StandardPivotSearch.TapeName) : TapeName :=
  if isCandidate : name = StandardPivotSearch.counterTape 1 then candidateTape
  else if isFirstSize : name = StandardPivotSearch.sizeTape 0 then sizeTape 0
  else if isSecondSize : name = StandardPivotSearch.sizeTape 1 then sizeTape 1
  else if isThirdSize : name = StandardPivotSearch.sizeTape 2 then sizeTape 2
  else if isColumn : name = StandardPivotSearch.counterTape 6 then columnTape
  else if isMatrix : name = StandardPivotSearch.matrixTape then originalTape
  else if isStart : name = StandardPivotSearch.startTape then pivotTape
  else .inr (.inl ⟨name, by
    constructor
    · fin_cases name <;> first | rfl | contradiction
    · exact isCandidate⟩)

theorem searchTarget_injective : Function.Injective searchTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)

def searchWiring : StandardPivotSearch.TapeName ↪ TapeName :=
  ⟨searchTarget, searchTarget_injective⟩

def pivotWiring : StandardGaussJordanPivot.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def search (enumeration : Scalar ≃ Fin cardinality) :
    let scalar := FieldRow.scalarDomain enumeration
    Machine Alphabet (StandardPivotSearch.AlgorithmState (scalar.width Empty.elim)) :=
  MultiTape.wire searchWiring (StandardPivotSearch.algorithm (FieldRow.scalarDomain enumeration)
    (StandardPivotSearch.fieldIsZero enumeration))

noncomputable def pivot (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanPivot.State
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire pivotWiring (StandardGaussJordanPivot.algorithm enumeration)

/-- Search returns the mathematical first nonzero row at or after the
immutable pivot, or the row-count sentinel. Unwired pivot workspace tapes
are left untouched; private search scratch has no encoding obligation. -/
theorem search_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    let scalar := FieldRow.scalarDomain enumeration
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (start column : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_startValid : start.val ≤ sizes 1) (columnValid : column.val < sizes 2),
      sizes 1 < 2 ^ sizes 0 → sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain scalar) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (search enumeration) ticks
          (StandardPivotSearch.algorithmEntry
            (scalar.width Empty.elim)) (fun _ => 0) initial
          (StandardPivotSearch.algorithmExit
            (scalar.width Empty.elim)) (fun _ => 0) final ∧
        (∃ candidate : Fin (2 ^ sizes 0),
          (start.val ≤ candidate.val ∧ candidate.val ≤ sizes 1) ∧
          final candidateTape = encoded (EncodedDomain.binaryNaturals 0) sizes candidate ∧
          GaussJordan.findPivot (Scalar := Scalar) matrix start.val ⟨column.val, columnValid⟩ =
            (if valid : candidate.val < sizes 1 then some ⟨candidate.val, valid⟩ else none) ∧
          final (searchWiring StandardPivotSearch.foundTape) =
            encoded EncodedDomain.booleans sizes (decide (candidate.val < sizes 1))) ∧
        (∀ name, name ∉ Set.range searchWiring → final name = initial name) ∧
        (∀ name, StandardPivotSearch.readOnly name = true →
          final (searchWiring name) = initial (searchWiring name)) := by
  intro scalar
  obtain ⟨bound, execute⟩ := StandardPivotSearch.field_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial start column matrix startValid columnValid rowsFit columnsFit capacity
    startEq columnEq matrixEq headers regions
  have sameDomain : ∀ name, domains enumeration (searchWiring name) =
      StandardPivotSearch.domains scalar name := by
    intro name
    fin_cases name <;> rfl
  obtain ⟨ticks, localFinal, cost, localTrace, candidate, bounds, candidateEq, found, foundEq⟩ :=
    execute sizes (fun name => initial (searchWiring name)) start column matrix startValid columnValid
      rowsFit columnsFit capacity startEq columnEq matrixEq
      (by intro parameter; fin_cases parameter <;> exact headers _)
      (by
        intro name
        change Region ((StandardPivotSearch.domains scalar name).width sizes) 0 (initial (searchWiring name))
        rw [← sameDomain name]
        exact regions (searchWiring name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring searchWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (by intro name; rw [sameDomain name])
    (by intro name; fin_cases name <;> decide) initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace,
    ⟨candidate, bounds, (located _).trans candidateEq, found,
      (located _).trans foundEq⟩,
    ?_, ?_⟩
  · intro name absent
    exact outside name absent
  · intro name fixed
    exact immutable name fixed

def incrementWiring : Sum (Fin 3) Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl parameter => sizeTape parameter
    | .inr false => pivotTape | .inr true => nextRowTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit

noncomputable def advancePivot : Machine Alphabet IncrementState :=
  MultiTape.wire incrementWiring (StandardBinaryScan.algorithm BinaryScan.increment)

def found (symbols : Symbols Alphabet) : Bool :=
  decide (symbols (searchWiring StandardPivotSearch.foundTape) = Binary.data true)

abbrev FoundState (scalarWidth : ℕ) :=
  Sum (StandardGaussJordanPivot.State scalarWidth) IncrementState

noncomputable def foundMachine (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (FoundState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence (pivot enumeration) advancePivot (.inl (.inl true))

def idle : Machine Alphabet Unit := fun _ _ => none

abbrev SelectState (scalarWidth : ℕ) :=
  Sum (Sum Unit (Sum (FoundState scalarWidth) Unit)) Unit

noncomputable instance selectStateFinite (scalarWidth : ℕ) : Fintype (SelectState scalarWidth) := by
  letI : Fintype (StandardGaussJordanPivot.State scalarWidth) := inferInstance
  dsimp only [SelectState, FoundState, IncrementState]
  infer_instance

noncomputable def select (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (SelectState
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.withExit (MultiTape.branchMachine found (foundMachine enumeration) idle
    (.inl (StandardGaussJordanPivot.entry
      ((FieldRow.scalarDomain enumeration).width Empty.elim))) ())

def selectEntry (scalarWidth : ℕ) : SelectState scalarWidth := .inl (.inl ())
def selectExit (scalarWidth : ℕ) : SelectState scalarWidth := .inr ()

@[simp] theorem select_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    select enumeration (selectExit
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

omit [Field Scalar] in
/-- Advancing the pivot writes a separate next-row output and preserves every
argument and matrix tape. The successful branch proves ordinary increment fits. -/
theorem advancePivot_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow : Fin (2 ^ sizes 0)),
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial nextRowTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly advancePivot ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes pivotRow) ∧
        (∀ name, name ≠ nextRowTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (StandardBinaryIncrement.contract (0 : Fin 3)).wired_runs incrementWiring
  refine ⟨bound, ?_⟩
  intro sizes initial pivotRow pivotEq headers region
  let input : Inputs (StandardBinaryScan.domains (EncodedDomain.binaryNaturals (0 : Fin 3))
      (EncodedDomain.binaryNaturals 0)) StandardTerminatedCopy.readOnly sizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr output => cases output with
      | false => exact pivotRow
      | true => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name; fin_cases name <;> decide) trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr output => cases output with
          | false => exact pivotEq
          | true => contradiction)
      (by
        intro name writable
        fin_cases name <;> first
          | contradiction
          | change Region ((EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes) 0 (initial nextRowTape)
            simpa only [EncodedDomain.binaryNaturals_width] using region) headers
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = StandardBinaryIncrement.next 0 sizes pivotRow at correct
    rw [correct] at result
    exact result
  · intro name notNext
    apply preserved_of_wiring incrementWiring StandardTerminatedCopy.readOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr output => cases output with
      | false => rfl
      | true => exact False.elim (notNext equal.symm)

end Polytime2.StandardGaussJordanColumn

