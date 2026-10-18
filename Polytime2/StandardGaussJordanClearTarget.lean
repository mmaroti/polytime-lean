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
import Polytime2.FiniteTable
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

def tableTarget : Fin 1 ⊕ Fin 1 → TapeName
  | .inl _ => dataTape 3
  | .inr _ => dataTape 7

def tableWiring : (Fin 1 ⊕ Fin 1) ↪ TapeName where
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
  FiniteTable.State (fun _ : Fin 1 => width) (fun _ : Fin 1 => width)

noncomputable abbrev State (width : ℕ) :=
  Sum (StandardMatrixEntry.State width) (Sum (NegateState width) (StandardMatrixRows.State width))

noncomputable instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardMatrixRows.State width) := inferInstance
  dsimp only [State, NegateState]
  infer_instance

noncomputable def lookup (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardMatrixEntry.State
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire lookupWiring
    (StandardMatrixEntry.machine
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim))

noncomputable def negate (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (NegateState
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  MultiTape.wire tableWiring
    (FiniteTable.algorithm (fun _ : Fin 1 => scalar) (fun _ : Fin 1 => scalar)
      (fun (_ : Empty → ℕ) (values : Fin 1 → Scalar) (_ : Fin 1) => -(values 0)))

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
    (MultiTape.sequence (negate enumeration) (rowClear enumeration)
      (StandardMatrixRows.entry (scalar.width Empty.elim)))
    (.inl (FiniteTable.entry _ _))

def entry (width : ℕ) : State width := .inl (StandardMatrixEntry.entry width)

def exit (width : ℕ) : State width :=
  .inr (.inr (StandardMatrixRows.exit width))

omit [Field Scalar] in
@[simp] theorem lookup_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    lookup enumeration (StandardMatrixEntry.exit
      ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [lookup, MultiTape.wire, StandardMatrixEntry.halt]

@[simp] theorem negate_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    negate enumeration none symbols = none := by
  simp [negate, MultiTape.wire, FiniteTable.algorithm]

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
    (scalar.width Empty.elim) (fun _ => by simp [EncodedDomain.constant, EncodedDomain.ofCodec])).wired_runs lookupWiring
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
  change output () =
    matrix ⟨targetRow.val * sizes 2 + column.val, otherWithin⟩ at valueEq
  have result := canonical ()
  rw [valueEq] at result
  refine ⟨ticks, final, cost, trace, ?_, outside, immutable⟩
  exact result.trans (encoded_constant scalar sizes _)

/-- Fixed-table negation uses separate immutable arguments and overwrites the
coefficient output, including for zero-bit scalar presentations. -/
theorem negate_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ cost : ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet) (value : Scalar),
      initial (dataTape 3) = encoded (Polytime2.FieldRow.scalarDomain enumeration) Empty.elim value →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ cost ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (negate enumeration) ticks (FiniteTable.entry _ _) (fun _ => 0) initial none (fun _ => 0) final ∧
        final (dataTape 7) = encoded (Polytime2.FieldRow.scalarDomain enumeration) Empty.elim (-value) ∧
        (∀ name, name ∉ Set.range tableWiring → final name = initial name) ∧
        (∀ name, FiniteTable.readOnly name = true → final (tableWiring name) = initial (tableWiring name)) := by
  let scalar := Polytime2.FieldRow.scalarDomain enumeration
  obtain ⟨bound, execute⟩ := (FiniteTable.contract (fun _ : Fin 1 => scalar) (fun _ : Fin 1 => scalar)
    (fun (_ : Empty → ℕ) (values : Fin 1 → Scalar) (_ : Fin 1) => -(values 0))).wired_runs tableWiring
  refine ⟨MvPolynomial.eval Empty.elim bound, ?_⟩
  intro sizes initial value valueEq regions
  let input : Inputs (FiniteTable.domains (fun _ : Fin 1 => scalar) (fun _ : Fin 1 => scalar))
      FiniteTable.readOnly Empty.elim := fun name => match name with
    | ⟨.inl _, _⟩ => value
    | ⟨.inr _, impossible⟩ => nomatch impossible
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute Empty.elim input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by
        intro name
        change (domains enumeration (tableTarget name)).width sizes = _
        fin_cases name <;> simp [domains, tableTarget, dataTape, scalar,
        StandardMatrixRows.domains, StandardMatrixRows.dataTape, StandardMatrixRowStep.domains,
        StandardMatrixRowEntry.domains, FiniteTable.domains, EncodedDomain.constant])
      (by intro name; fin_cases name <;> decide) trivial
      (by intro name readonly; fin_cases name; exact valueEq; contradiction)
      (by intro name writable; exact regions (tableWiring name))
      (by intro parameter; cases parameter)
  have selected := congrFun correct 0
  change output 0 = -value at selected
  have result := canonical 0
  rw [selected] at result
  exact ⟨ticks, final, cost, trace, result, outside, immutable⟩

/-- The row phase accepts arbitrary writable regions, preserves its arguments,
and returns the encoded row transform without scratch validity obligations. -/
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
  obtain ⟨ticks, localFinal, cost, localTrace, result⟩ :=
    execute sizes localInitial sourceRow targetRow sourceValid targetValid coefficient matrix
      columnsFit capacity sourceEq targetEq coefficientEq matrixEq headers
      (by intro name; simpa only [localInitial, ← sameDomain name] using regions (rowWiring name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring rowWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (by intro name; rw [sameDomain name]) readOnlyMatches initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace, ?_, ?_, ?_⟩
  · have resultAt := located (StandardMatrixRows.dataTape 5)
    change final (dataTape 5) = _ at resultAt
    exact resultAt.trans result
  · intro name absent
    exact outside name absent
  · intro name fixed
    exact immutable name fixed

/-- Lookup, coefficient negation, and row traversal share one workspace and
accept arbitrary initial writable contents and restore all heads. -/
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
              matrix (sizes 2))) := by
  obtain ⟨lookupBound, executeLookup⟩ := lookup_runs enumeration
  obtain ⟨negateCost, executeNegate⟩ := negate_runs enumeration
  obtain ⟨rowBound, executeRow⟩ := rowClear_runs enumeration
  refine ⟨lookupBound + MvPolynomial.C negateCost + rowBound + 2, ?_⟩
  intro sizes initial sourceRow targetRow column sourceValid targetValid matrix
    columnsFit columnValid capacity sourceEq targetEq columnEq matrixEq headers regions
  have within := StandardMatrixEntry.index_lt sizes targetRow.val column.val targetValid columnValid
  let value : Scalar := matrix ⟨targetRow.val * sizes 2 + column.val, within⟩
  obtain ⟨lookupTicks, loaded, lookupCost, lookupTrace, valueEq, lookupOutside, lookupImmutable⟩ :=
    executeLookup sizes initial targetRow column matrix within columnsFit targetValid
      columnValid capacity targetEq columnEq matrixEq headers regions
  have loadedRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (loaded name) :=
    fun name => lookupTrace.region name (regions name)
  obtain ⟨negateTicks, negated, negationCost, negateTrace, coefficientEq, negateOutside, negateImmutable⟩ :=
    executeNegate sizes loaded value valueEq loadedRegions
  have negateRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (negated name) :=
    fun name => negateTrace.region name (loadedRegions name)
  have preserveInput : ∀ name, readOnly name = true → negated name = initial name := by
    intro name readonly
    exact (negateTrace.readOnly_tape name readonly).trans (lookupTrace.readOnly_tape name readonly)
  obtain ⟨rowTicks, final, rowCost, rowTrace, result, rowOutside, rowImmutable⟩ :=
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
  have complete := lookupTrace.sequence _ (Sum.inl (FiniteTable.entry _ _)) (lookup_halt enumeration) tail
  refine ⟨lookupTicks + (negateTicks + rowTicks + 1) + 1, final, ?_, ?_, ⟨within, result⟩⟩
  · simp only [map_add, MvPolynomial.eval_C, map_ofNat]
    omega
  · simpa only [algorithm, entry, exit] using complete
@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    algorithm enumeration
      (exit ((Polytime2.FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [algorithm, exit, MultiTape.sequence]

end Polytime2.StandardGaussJordanClearTarget
