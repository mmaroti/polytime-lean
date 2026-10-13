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

import Polytime2.StandardMatrixEntryContract
import Polytime2.StandardMatrixRowsContract
import Polytime2.StandardFiniteTable
import Polytime2.StandardTapeCommands
import Polytime2.MatrixRowField
import Polytime2.FieldRow

/-! # Standard-convention single-row pivot clearing -/

namespace Polytime2.StandardGaussJordanClearTarget

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar]
variable {cardinality : ℕ}

abbrev BaseTape := StandardMatrixRows.TapeName
abbrev TapeName := Sum BaseTape Unit
abbrev Alphabet := CallingConvention.Alphabet TapeName

def dataTape (slot : Fin 18) : TapeName := .inl (StandardMatrixRows.dataTape slot)
def inputTape : TapeName := .inl StandardMatrixRows.inputTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardMatrixRows.sizeTape parameter)
def columnTape : TapeName := .inr ()

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardMatrixRows.domains
      (Polytime2.FieldRow.scalarDomain enumeration) name
  | .inr _ => EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => if name = StandardMatrixRows.dataTape 3 then false
      else StandardMatrixRows.readOnly name
  | .inr _ => true

def sizeTapes : Fin 3 ↪ TapeName :=
  ⟨sizeTape, by intro first second equal; cases equal; rfl⟩

def lookupSlot (slot : Fin 9) : Fin 18 :=
  match slot.val with
  | 0 => 11 | 1 => 1 | 2 => 12 | 3 => 13 | 4 => 16
  | 5 => 14 | 6 => 2 | 7 => 15 | _ => 17

theorem lookupSlot_injective : Function.Injective lookupSlot := by
  intro first second equal
  fin_cases first <;> fin_cases second <;> simp [lookupSlot] at equal ⊢

def lookupTarget : StandardMatrixEntry.TapeName → TapeName
    | .inl (.inl parameter) => sizeTape parameter
    | .inl (.inr slot) => if slot = 6 then columnTape
        else dataTape (lookupSlot slot)
    | .inr false => inputTape
    | .inr true => dataTape 3

theorem lookupTarget_injective : Function.Injective lookupTarget := by
  intro first second equal
  fin_cases first <;> fin_cases second <;>
    simp_all [lookupTarget, lookupSlot, dataTape, inputTape, sizeTape,
      columnTape, StandardMatrixRows.dataTape, StandardMatrixRows.sizeTape,
      StandardMatrixRows.inputTape]

def lookupWiring : StandardMatrixEntry.TapeName ↪ TapeName where
  toFun := lookupTarget
  inj' := lookupTarget_injective

def tableTarget : Fin 3 → TapeName
    | 0 => dataTape 3
    | 1 => dataTape 16
    | _ => dataTape 7

def tableWiring : Fin 3 ↪ TapeName where
  toFun := tableTarget
  inj' := by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp_all [tableTarget, dataTape, StandardMatrixRows.dataTape]

def rowSwap : Equiv BaseTape BaseTape :=
  Equiv.swap (StandardMatrixRows.dataTape 3) (StandardMatrixRows.dataTape 7)

def rowWiring : BaseTape ↪ TapeName :=
  rowSwap.toEmbedding.trans Function.Embedding.inl

@[simp] theorem rowWiring_apply (name : BaseTape) :
    rowWiring name = .inl (rowSwap name) := rfl

@[simp] theorem rowWiring_swap (name : BaseTape) :
    rowWiring (rowSwap name) = .inl name := by
  fin_cases name <;> rfl

noncomputable def additionOperation (enumeration : Scalar ≃ Fin cardinality) :
    ∀ assignment,
      (Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment →
      (Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment →
      (Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment →
      (Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment ×
        (Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment :=
  fun assignment coefficient source target => by
    letI : Field ((Polytime2.FieldRow.scalarDomain enumeration).Carrier assignment) := by
      change Field Scalar
      infer_instance
    exact (source, target + coefficient * source)

abbrev NegateState (width : ℕ) :=
  StandardFiniteTable.State width 1 width

abbrev State (width : ℕ) :=
  Sum (StandardMatrixEntry.State width)
    (Sum Bool (Sum (NegateState width) (StandardMatrixRows.State width)))

instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardFiniteTable.State width 1 width) := inferInstance
  letI : Fintype (StandardMatrixRows.State width) := inferInstance
  dsimp only [State, NegateState]
  infer_instance

noncomputable def lookup (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixEntry.State
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire lookupWiring
    (StandardMatrixEntry.machine
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))

noncomputable def prepareFlag : Machine Alphabet Bool :=
  StandardTapeCommands.setBoolean (dataTape 16) false

noncomputable def negate (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (NegateState
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  MultiTape.wire tableWiring
    (StandardFiniteTable.algorithm scalar (EncodedDomain.booleans (Parameter := Empty)) scalar
      (fun (_ : Empty → ℕ) (value : Scalar) (_ : Bool) => -value))

noncomputable def rowClear (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixRows.State
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  MultiTape.wire rowWiring
    (StandardMatrixRows.machine false scalar (additionOperation enumeration))

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (State
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  MultiTape.sequence (lookup enumeration)
    (MultiTape.sequence prepareFlag
      (MultiTape.sequence (negate enumeration) (rowClear enumeration)
        (StandardMatrixRows.entry (scalar.width Empty.elim)))
      (.inl StandardFiniteTable.entry))
    (.inl false)

def entry (width : ℕ) : State width := .inl (StandardMatrixEntry.entry width)

def exit (width : ℕ) : State width :=
  .inr (.inr (.inr (StandardMatrixRows.exit width)))

omit [Field Scalar] in
@[simp] theorem lookup_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    lookup enumeration (StandardMatrixEntry.exit
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [lookup, MultiTape.wire, StandardMatrixEntry.halt]

@[simp] theorem prepareFlag_halt (symbols : Symbols Alphabet) :
    prepareFlag true symbols = none := by
  simp [prepareFlag, StandardTapeCommands.setBoolean, MultiTape.wire,
    StandardTapeCommands.booleanMachine]

@[simp] theorem negate_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    negate enumeration StandardFiniteTable.exit symbols = none := by
  simp [negate, MultiTape.wire, StandardFiniteTable.algorithm,
    StandardFiniteTable.machine, StandardFiniteTable.exit]
  rfl

@[simp] theorem rowClear_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    rowClear enumeration (StandardMatrixRows.exit
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp only [rowClear, MultiTape.wire]
  rw [StandardMatrixRows.halt]
  rfl

omit [Field Scalar] in
/-- Read the target pivot-column entry into the coefficient input tape. -/
theorem lookup_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (targetRow column : Fin (2 ^ sizes 0))
      (matrix : ((Polytime2.FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes)
      (within : targetRow.val * sizes 2 + column.val <
        MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → targetRow.val < sizes 1 → column.val < sizes 2 →
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial inputTape = encoded (domains enumeration inputTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (lookup enumeration) ticks
          (StandardMatrixEntry.entry
            ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardMatrixEntry.exit
            ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final (dataTape 3) = encoded (Polytime2.FieldRow.scalarDomain enumeration)
          Empty.elim (matrix ⟨targetRow.val * sizes 2 + column.val, within⟩) ∧
        (∀ name, name ∉ Set.range lookupWiring → final name = initial name) ∧
        (∀ name, StandardMatrixEntry.readOnly name = true →
          final (lookupWiring name) = initial (lookupWiring name)) := by
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  obtain ⟨bound, execute⟩ := (StandardMatrixEntry.contract scalar.constant
    (scalar.width Empty.elim) (fun _ => rfl)).wired_runs lookupWiring
  refine ⟨bound, ?_⟩
  intro sizes initial targetRow column matrix within columnsFit targetValid columnValid
    capacity targetEq columnEq matrixEq headers regions
  let input := StandardMatrixEntry.inputValues scalar.constant sizes targetRow column matrix
  have sameDomain : ∀ name, domains enumeration (lookupWiring name) =
      StandardMatrixEntry.domains scalar.constant name := by
    intro name
    fin_cases name <;> rfl
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; rw [sameDomain name])
      (by intro name; fin_cases name <;> decide)
      ⟨columnsFit, targetValid, columnValid, capacity⟩
      (by
        intro name readonly
        cases name with
        | inl name =>
          cases name with
          | inl parameter =>
            change initial (sizeTape parameter) =
              encoded (EncodedDomain.unary parameter) sizes PUnit.unit
            rw [encoded_unary]
            exact headers parameter
          | inr slot =>
            fin_cases slot <;> first | exact targetEq | exact columnEq |
              norm_num [StandardMatrixEntry.readOnly, StandardMatrixAddress.readOnly] at readonly
        | inr output =>
          cases output with
          | false => exact matrixEq
          | true => contradiction)
      (by intro name writable; exact regions (lookupWiring name)) headers
  obtain ⟨otherWithin, valueEq⟩ := correct
  change output ⟨.inr true, rfl⟩ =
    matrix ⟨targetRow.val * sizes 2 + column.val, otherWithin⟩ at valueEq
  have result := canonical (.inr true) rfl
  rw [valueEq] at result
  refine ⟨ticks, final, cost, trace, ?_, outside, immutable⟩
  exact result

/-- Fixed-table negation uses separate immutable arguments and overwrites the
coefficient output, including for zero-bit scalar presentations. -/
theorem negate_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ cost : ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet) (value : Scalar),
      initial (dataTape 3) = encoded (Polytime2.FieldRow.scalarDomain enumeration)
        Empty.elim value →
      initial (dataTape 16) = encoded EncodedDomain.booleans Empty.elim false →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ cost ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (negate enumeration) ticks StandardFiniteTable.entry (fun _ => 0) initial
          StandardFiniteTable.exit (fun _ => 0) final ∧
        final (dataTape 7) = encoded (Polytime2.FieldRow.scalarDomain enumeration)
          Empty.elim (-value) ∧
        (∀ name, name ∉ Set.range tableWiring → final name = initial name) ∧
        (∀ name, StandardFiniteTable.readOnly name = true →
          final (tableWiring name) = initial (tableWiring name)) := by
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  let boolean : EncodedDomain.{0, 0} Empty := EncodedDomain.booleans
  obtain ⟨bound, execute⟩ := (StandardFiniteTable.contract scalar boolean scalar
    (fun (_ : Empty → ℕ) (value : Scalar) (_ : Bool) => -value)).wired_runs tableWiring
  refine ⟨MvPolynomial.eval Empty.elim bound, ?_⟩
  intro sizes initial value valueEq flagEq regions
  let input : Inputs (StandardFiniteTable.domains scalar boolean scalar)
      StandardFiniteTable.readOnly Empty.elim := fun name => by
    rcases name with ⟨name, readonly⟩
    by_cases isFirst : name = 0
    · subst name
      exact value
    · by_cases isSecond : name = 1
      · subst name
        exact false
      · have small : name.val < 2 := of_decide_eq_true readonly
        have notZero : name.val ≠ 0 := fun equal => isFirst (Fin.ext equal)
        have notOne : name.val ≠ 1 := fun equal => isSecond (Fin.ext equal)
        exact False.elim (by omega)
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute Empty.elim input (fun name => (domains enumeration name).width sizes)
      readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name; fin_cases name <;> decide)
      trivial
      (by
        intro name readonly
        fin_cases name
        · exact valueEq
        · exact flagEq
        · contradiction)
      (by intro name writable; exact regions (tableWiring name))
      (by intro parameter; cases parameter)
  change output ⟨2, rfl⟩ = -value at correct
  have result := canonical 2 rfl
  rw [correct] at result
  exact ⟨ticks, final, cost, trace, result, outside, immutable⟩

/-- The row phase accepts arbitrary writable regions, preserves its arguments,
and returns the row transform with every private tape valid. -/
theorem rowClear_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (sourceRow targetRow : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (coefficient : Scalar)
      (matrix : ((Polytime2.FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (dataTape 7) = encoded (Polytime2.FieldRow.scalarDomain enumeration)
        Empty.elim coefficient →
      initial inputTape = encoded (domains enumeration inputTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (rowClear enumeration) ticks
          (StandardMatrixRows.entry
            ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardMatrixRows.exit
            ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final (dataTape 5) = encoded (domains enumeration (dataTape 5)) sizes
          (StandardMatrixRows.processed false
            (Polytime2.FieldRow.scalarDomain enumeration) (additionOperation enumeration)
            sizes sourceRow targetRow sourceValid targetValid coefficient matrix (sizes 2)) ∧
        (∀ name, StandardMatrixRows.readOnly name = false →
          ∃ value : (domains enumeration (rowWiring name)).Carrier sizes,
            final (rowWiring name) = encoded
              (domains enumeration (rowWiring name)) sizes value) ∧
        (∀ name, name ∉ Set.range rowWiring → final name = initial name) ∧
        (∀ name, StandardMatrixRows.readOnly name = true →
          final (rowWiring name) = initial (rowWiring name)) := by
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  obtain ⟨bound, execute⟩ := StandardMatrixRows.runs false scalar
    (additionOperation enumeration)
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow targetRow sourceValid targetValid coefficient matrix
    columnsFit capacity sourceEq targetEq coefficientEq matrixEq headers regions
  have sameDomain : ∀ name, domains enumeration (rowWiring name) =
      StandardMatrixRows.domains scalar name := by
    intro name
    fin_cases name <;> rfl
  have readOnlyMatches : ∀ name, readOnly (rowWiring name) = true →
      StandardMatrixRows.readOnly name = true := by
    intro name
    fin_cases name <;> decide
  let localInitial : Tapes StandardMatrixRows.Alphabet := fun name => initial (rowWiring name)
  obtain ⟨ticks, localFinal, cost, localTrace, result, canonical⟩ :=
    execute sizes localInitial sourceRow targetRow sourceValid targetValid coefficient matrix
      columnsFit capacity sourceEq targetEq coefficientEq matrixEq headers
      (by intro name; simpa only [localInitial, ← sameDomain name] using regions (rowWiring name))
  have trace := localTrace.wire rowWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (by intro name; rw [sameDomain name]) readOnlyMatches initial (fun _ => 0)
  have initialEq : install rowWiring localInitial initial = initial := install_self rowWiring initial
  have positions : install rowWiring (fun _ : BaseTape => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self rowWiring _
  rw [initialEq, positions] at trace
  refine ⟨ticks, install rowWiring localFinal initial, cost, trace, ?_, ?_, ?_, ?_⟩
  · have resultAt := install_at rowWiring localFinal initial (StandardMatrixRows.dataTape 5)
    change (install rowWiring localFinal initial) (dataTape 5) = _ at resultAt
    exact resultAt.trans result
  · intro name writable
    obtain ⟨value, encodedValue⟩ := canonical name writable
    rw [sameDomain name]
    exact ⟨value, (install_at rowWiring localFinal initial name).trans encodedValue⟩
  · intro name outside
    exact install_outside rowWiring localFinal initial name outside
  · intro name immutable
    rw [install_at]
    exact localTrace.readOnly_tape name immutable

/-- Lookup, coefficient negation, and row traversal share one workspace and
accept arbitrary initial writable contents. All scratch is valid on return. -/
theorem runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ)
      (initial : Tapes Alphabet) (sourceRow targetRow column : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (matrix : ((Polytime2.FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      sizes 2 < 2 ^ sizes 0 → column.val < sizes 2 →
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial inputTape = encoded (domains enumeration inputTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (algorithm enumeration) ticks
          (entry ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (exit ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        (∃ within : targetRow.val * sizes 2 + column.val <
            MvPolynomial.eval sizes StandardMatrixEntry.length,
          final (dataTape 5) = encoded (domains enumeration (dataTape 5)) sizes
            (StandardMatrixRows.processed false
              (Polytime2.FieldRow.scalarDomain enumeration) (additionOperation enumeration)
              sizes sourceRow targetRow sourceValid targetValid
              (Neg.neg (α := Scalar) (matrix ⟨targetRow.val * sizes 2 + column.val, within⟩))
              matrix (sizes 2))) ∧
        (∀ name, readOnly name = false →
          ∃ value : (domains enumeration name).Carrier sizes,
            final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨lookupBound, executeLookup⟩ := lookup_runs enumeration
  obtain ⟨negateCost, executeNegate⟩ := negate_runs enumeration
  obtain ⟨rowBound, executeRow⟩ := rowClear_runs enumeration
  refine ⟨lookupBound + MvPolynomial.C negateCost + rowBound + 4, ?_⟩
  intro sizes initial sourceRow targetRow column sourceValid targetValid matrix
    columnsFit columnValid capacity sourceEq targetEq columnEq matrixEq headers regions
  have within := StandardMatrixEntry.index_lt sizes targetRow.val column.val targetValid columnValid
  let value : Scalar := matrix ⟨targetRow.val * sizes 2 + column.val, within⟩
  obtain ⟨lookupTicks, loaded, lookupCost, lookupTrace, valueEq, lookupOutside, lookupImmutable⟩ :=
    executeLookup sizes initial targetRow column matrix within columnsFit targetValid
      columnValid capacity targetEq columnEq matrixEq headers regions
  have loadedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (loaded name) :=
    fun name => lookupTrace.region name (regions name)
  obtain ⟨old, oldLength, oldEq⟩ := (loadedRegions (dataTape 16)).exists_buffer
  change old.length = 1 at oldLength
  obtain ⟨oldBit, rfl⟩ := List.length_eq_one_iff.mp oldLength
  let prepared := Function.update loaded (dataTape 16) (buffer [Binary.data false])
  have flagTrace := StandardTapeCommands.setBoolean_runs (dataTape 16) false
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl loaded oldBit oldEq
  have preparedValue : prepared (dataTape 3) =
      encoded (Polytime2.FieldRow.scalarDomain enumeration) Empty.elim value := by
    exact (Function.update_of_ne (by decide) _ _).trans valueEq
  have preparedFlag : prepared (dataTape 16) =
      encoded EncodedDomain.booleans Empty.elim false := by
    change Function.update loaded (dataTape 16) (buffer [Binary.data false])
      (dataTape 16) = _
    rw [Function.update_self]
    rfl
  have preparedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (prepared name) :=
    fun name => flagTrace.region name (loadedRegions name)
  obtain ⟨negateTicks, negated, negationCost, negateTrace, coefficientEq, negateOutside, negateImmutable⟩ :=
    executeNegate sizes prepared value preparedValue preparedFlag preparedRegions
  have negateRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (negated name) :=
    fun name => negateTrace.region name (preparedRegions name)
  have firstStages := lookupTrace.sequence prepareFlag false (lookup_halt enumeration) flagTrace
  have preserveInput : ∀ name, readOnly name = true → negated name = initial name := by
    intro name readonly
    exact (negateTrace.readOnly_tape name readonly).trans (firstStages.readOnly_tape name readonly)
  obtain ⟨rowTicks, final, rowCost, rowTrace, result, canonical, rowOutside, rowImmutable⟩ :=
    executeRow sizes negated sourceRow targetRow sourceValid targetValid
      (Neg.neg (α := Scalar) value) matrix
      columnsFit capacity
      ((preserveInput (dataTape 0) rfl).trans sourceEq)
      ((preserveInput (dataTape 1) rfl).trans targetEq) coefficientEq
      ((preserveInput inputTape rfl).trans matrixEq)
      (fun parameter => (preserveInput (sizeTape parameter) rfl).trans (headers parameter))
      negateRegions
  have tail := negateTrace.sequence (rowClear enumeration)
    (StandardMatrixRows.entry ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
    (negate_halt enumeration) rowTrace
  have middle := flagTrace.sequence _ (Sum.inl StandardFiniteTable.entry) prepareFlag_halt tail
  have complete := lookupTrace.sequence _ (Sum.inl false) (lookup_halt enumeration) middle
  refine ⟨lookupTicks + (1 + (negateTicks + rowTicks + 1) + 1) + 1, final, ?_, ?_,
    ⟨within, result⟩, ?_⟩
  · simp only [map_add, MvPolynomial.eval_C, map_ofNat]
    omega
  · simpa only [algorithm, entry, exit, prepareFlag] using complete
  · intro name writable
    cases name with
    | inr extra => contradiction
    | inl name =>
      by_cases isCoefficient : name = StandardMatrixRows.dataTape 7
      · subst name
        exact ⟨-value, (rowImmutable (StandardMatrixRows.dataTape 3) rfl).trans coefficientEq⟩
      · have localWritable : StandardMatrixRows.readOnly (rowSwap name) = false := by
          fin_cases name <;> first | rfl | exact False.elim (isCoefficient rfl) | contradiction
        have valid := canonical (rowSwap name) localWritable
        rw [rowWiring_swap] at valid
        exact valid

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    algorithm enumeration
      (exit ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [algorithm, exit, MultiTape.sequence]

/-- The complete target-row update exposes only immutable mathematical inputs,
with arbitrary initial outputs and valid scratch on return. -/
theorem contract (enumeration : Scalar ≃ Fin cardinality) :
    CallingConvention.Realizes (domains enumeration) readOnly sizeTapes
      (algorithm enumeration)
      (entry ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
      (exit ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))
      (fun sizes input =>
        (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧
        (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 2 ∧
        sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (within : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
          (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val <
            MvPolynomial.eval sizes StandardMatrixEntry.length),
        output ⟨dataTape 5, rfl⟩ = StandardMatrixRows.processed false
          (Polytime2.FieldRow.scalarDomain enumeration) (additionOperation enumeration)
          sizes (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩)
          sourceValid targetValid
          (Neg.neg (α := Scalar) ((input ⟨inputTape, rfl⟩)
            ⟨(input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
              (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val, within⟩ : Scalar))
          (input ⟨inputTape, rfl⟩) (sizes 2)) := by
  classical
  obtain ⟨bound, execute⟩ := runs enumeration
  refine ⟨(by intro parameter; rfl), halt enumeration, bound, ?_⟩
  intro sizes input initial valid represented headers
  obtain ⟨ticks, final, cost, trace, ⟨within, resultEq⟩, canonical⟩ :=
    execute sizes initial (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩)
      (input ⟨columnTape, rfl⟩) valid.1 valid.2.1 (input ⟨inputTape, rfl⟩)
      valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2
      (represented.1 (dataTape 0) rfl) (represented.1 (dataTape 1) rfl)
      (represented.1 columnTape rfl) (represented.1 inputTape rfl) headers represented.region
  let resultArray := StandardMatrixRows.processed false
    (Polytime2.FieldRow.scalarDomain enumeration) (additionOperation enumeration)
    sizes (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩) valid.1 valid.2.1
    (Neg.neg (α := Scalar) ((input ⟨inputTape, rfl⟩)
      ⟨(input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val * sizes 2 +
        (input ⟨columnTape, rfl⟩ : Fin (2 ^ sizes 0)).val, within⟩ : Scalar))
    (input ⟨inputTape, rfl⟩) (sizes 2)
  let output : Outputs (domains enumeration) readOnly sizes := fun name => by
    rcases name with ⟨name, writable⟩
    by_cases isResult : name = dataTape 5
    · subst name
      exact resultArray
    · exact Classical.choose (canonical name writable)
  refine ⟨ticks, output, final, cost, trace, ⟨valid.1, valid.2.1, within, rfl⟩, ?_⟩
  intro name writable
  by_cases isResult : name = dataTape 5
  · subst name
    exact resultEq
  · simpa only [output, isResult, ↓reduceDIte] using Classical.choose_spec (canonical name writable)

end Polytime2.StandardGaussJordanClearTarget
