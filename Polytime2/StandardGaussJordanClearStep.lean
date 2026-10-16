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

import Polytime2.StandardGaussJordanClearTarget

/-! # Committing a cleared row and advancing its private counter

The enclosing column-clear loop owns the working matrix and target counter.
Each row-clear call reads those values immutably and writes a separate result;
the caller commits that result and advances through a separate counter output.
-/

namespace Polytime2.StandardGaussJordanClearStep

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanClearTarget.TapeName Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev State (width : ℕ) := Sum (StandardGaussJordanClearTarget.State width)
  (Sum (Fin 3) (Sum IncrementState (Fin 3)))

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardGaussJordanClearTarget.State width) := inferInstance
  dsimp only [State, IncrementState]
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

noncomputable def machine (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence
    (MultiTape.wire targetWiring (StandardGaussJordanClearTarget.algorithm enumeration))
    (MultiTape.sequence commit (MultiTape.sequence increment advance 0)
      (.inl (.inl (.inl true)))) (.inl 0)

def entry (width : ℕ) : State width := .inl (StandardGaussJordanClearTarget.entry width)
def exit (width : ℕ) : State width := .inr (.inr (.inr 2))

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    machine enumeration (exit ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [machine, exit, MultiTape.sequence, advance, StandardTapeCommands.copy,
    MultiTape.wire, StandardTerminatedCopy.machine]

omit [Field Scalar] in
/-- The private target counter is read immutably and incremented into a separate
output. Every other tape, including the working matrix, stays unchanged. -/
theorem increment_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (targetRow : Fin (2 ^ sizes 0)),
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial nextTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly increment ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final nextTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes targetRow) ∧
        (∀ name, name ≠ nextTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (StandardBinaryIncrement.contract (0 : Fin 3)).wired_runs incrementWiring
  refine ⟨bound, ?_⟩
  intro sizes initial targetRow targetEq headers region
  let input : Inputs (StandardBinaryScan.domains (EncodedDomain.binaryNaturals (0 : Fin 3))
      (EncodedDomain.binaryNaturals 0)) StandardTerminatedCopy.readOnly sizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr output => cases output with
      | false => exact targetRow
      | true => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr output => cases output with
          | false => exact targetEq
          | true => contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | exact region)
      headers
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = StandardBinaryIncrement.next 0 sizes targetRow at correct
    rw [correct] at result
    exact result
  · intro name different
    apply preserved_of_wiring incrementWiring StandardTerminatedCopy.readOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr output => cases output with
      | false => rfl
      | true => exact False.elim (different equal.symm)

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
          (StandardBinaryIncrement.next 0 sizes targetRow) ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨targetBound, executeTarget⟩ := StandardGaussJordanClearTarget.runs enumeration
  obtain ⟨incrementBound, executeIncrement⟩ := increment_runs enumeration
  obtain ⟨matrixBound, matrixWidthBound⟩ :=
    ((FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length).polynomial_width
  refine ⟨targetBound + incrementBound + 2 * matrixBound + 2 * MvPolynomial.X 0 + 7, ?_⟩
  intro sizes initial sourceRow targetRow column sourceValid targetValid matrix
    columnsFit columnValid capacity sourceEq targetEq columnEq matrixEq headers regions
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  obtain ⟨targetTicks, localFinal, targetCost, localTrace, ⟨within, localResult⟩, localCanonical⟩ :=
    executeTarget sizes (fun name => initial (.inl name)) sourceRow targetRow column
      sourceValid targetValid matrix columnsFit columnValid capacity sourceEq targetEq
      columnEq matrixEq headers (fun name => regions (.inl name))
  let resultMatrix := StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
    (StandardGaussJordanClearTarget.additionOperation enumeration)
    sizes sourceRow targetRow sourceValid targetValid
    (Neg.neg (α := Scalar) (matrix ⟨targetRow.val * sizes 2 + column.val, within⟩)) matrix (sizes 2)
  let afterTarget : Tapes Alphabet := install targetWiring localFinal initial
  have targetTrace : Runs width readOnly
      (MultiTape.wire targetWiring (StandardGaussJordanClearTarget.algorithm enumeration)) targetTicks
      (StandardGaussJordanClearTarget.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun _ => 0) initial
      (StandardGaussJordanClearTarget.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun _ => 0) afterTarget := by
    have trace := localTrace.wire targetWiring width readOnly (fun _ => rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      initial (fun _ => 0)
    have positions : install targetWiring
        (fun _ : StandardGaussJordanClearTarget.TapeName => (0 : ℤ))
        (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self targetWiring _
    have start : install targetWiring (fun name => initial (.inl name)) initial = initial :=
      install_self targetWiring initial
    rw [positions, start] at trace
    exact trace
  have afterTargetAt (name : StandardGaussJordanClearTarget.TapeName) :
      afterTarget (.inl name) = localFinal name := install_at targetWiring localFinal initial name
  have resultEq : afterTarget (dataTape 5) =
      encoded (domains enumeration workingTape) sizes resultMatrix :=
    (afterTargetAt _).trans localResult
  have targetStill : afterTarget (dataTape 1) =
      encoded (EncodedDomain.binaryNaturals 0) sizes targetRow :=
    (afterTargetAt _).trans ((localTrace.readOnly_tape _ rfl).trans targetEq)
  have commitTrace := StandardTapeCommands.copy_encoded_runs
    (domains enumeration workingTape) sizes resultMatrix
    (dataTape 5) workingTape (by decide) width readOnly rfl rfl rfl afterTarget resultEq
    (targetTrace.region workingTape (regions workingTape))
  let afterCommit := Function.update afterTarget workingTape
    (encoded (domains enumeration workingTape) sizes resultMatrix)
  obtain ⟨incrementTicks, incremented, incrementCost, incrementTrace, nextEq, incrementOutside⟩ :=
    executeIncrement sizes afterCommit targetRow
      ((Function.update_of_ne (by decide) _ _).trans targetStill)
      (fun parameter => (commitTrace.readOnly_tape (sizeTape parameter) rfl).trans
        ((targetTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)))
      (commitTrace.region nextTape (targetTrace.region nextTape (regions nextTape)))
  have advanceTrace := StandardTapeCommands.copy_encoded_runs
    (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes targetRow)
    nextTape (dataTape 1) (by decide) width readOnly rfl rfl rfl incremented nextEq
    (incrementTrace.region (dataTape 1)
      (commitTrace.region (dataTape 1) (targetTrace.region (dataTape 1) (regions (dataTape 1)))))
  let final := Function.update incremented (dataTape 1)
    (encoded (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes targetRow))
  have preserve (name : TapeName) (notCounter : name ≠ dataTape 1)
      (notNext : name ≠ nextTape) (notMatrix : name ≠ workingTape) :
      final name = afterTarget name :=
    (Function.update_of_ne notCounter _ _).trans
      ((incrementOutside name notNext).trans (Function.update_of_ne notMatrix _ _))
  have finalMatrix : final workingTape =
      encoded (domains enumeration workingTape) sizes resultMatrix := by
    exact (Function.update_of_ne (by decide) _ _).trans
      ((incrementOutside workingTape (by decide)).trans (Function.update_self _ _ _))
  have tail := incrementTrace.sequence advance 0
    (by intro symbols; rfl) advanceTrace
  have middle := commitTrace.sequence _ (Sum.inl (Sum.inl (Sum.inl true)))
    (by intro symbols; rfl) tail
  have complete := targetTrace.sequence _ (Sum.inl 0)
    (by intro symbols; simp [MultiTape.wire, StandardGaussJordanClearTarget.halt]) middle
  refine ⟨targetTicks + ((2 * (domains enumeration workingTape).width sizes + 2) +
    (incrementTicks + (2 * sizes 0 + 2) + 1) + 1) + 1, final, ?_, ?_,
    ⟨within, finalMatrix⟩, Function.update_self _ _ _, ?_⟩
  · have widthBound := matrixWidthBound sizes
    change (domains enumeration workingTape).width sizes ≤ MvPolynomial.eval sizes matrixBound at widthBound
    simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · simpa only [machine, entry, exit, commit, advance, width, final,
      EncodedDomain.binaryNaturals] using complete
  · intro name writable
    by_cases isCounter : name = dataTape 1
    · subst name
      exact ⟨StandardBinaryIncrement.next 0 sizes targetRow, Function.update_self _ _ _⟩
    · by_cases isNext : name = nextTape
      · subst name
        exact ⟨StandardBinaryIncrement.next 0 sizes targetRow,
          (Function.update_of_ne (by decide) _ _).trans nextEq⟩
      · by_cases isMatrix : name = workingTape
        · subst name
          exact ⟨resultMatrix, finalMatrix⟩
        · cases name with
          | inr extra => exact False.elim (isNext rfl)
          | inl name =>
            have localWritable : StandardGaussJordanClearTarget.readOnly name = false := by
              change (if name = StandardGaussJordanClearTarget.dataTape 1 ∨
                name = StandardGaussJordanClearTarget.inputTape then false
                else StandardGaussJordanClearTarget.readOnly name) = false at writable
              rw [ite_eq_right (by
                rintro (equal | equal)
                · exact isCounter (congrArg Sum.inl equal)
                · exact isMatrix (congrArg Sum.inl equal))] at writable
              exact writable
            obtain ⟨value, encodedValue⟩ := localCanonical name localWritable
            exact ⟨value, (preserve (.inl name) isCounter isNext isMatrix).trans
              ((afterTargetAt name).trans encodedValue)⟩

end Polytime2.StandardGaussJordanClearStep
