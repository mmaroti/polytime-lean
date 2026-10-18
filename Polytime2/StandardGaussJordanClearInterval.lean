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

import Polytime2.StandardGaussJordanClearStep

/-! # Guarded row intervals for clearing a pivot column

Two intervals, ending at the pivot and starting immediately after it, skip the
pivot row without an equality test inside the loop. The enclosing caller owns
the working matrix and target counter. The interval limit is immutable here.
-/

namespace Polytime2.StandardGaussJordanClearInterval

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev TapeName := Sum StandardGaussJordanClearStep.TapeName (Fin 3)
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev GuardState := Sum StandardBinaryArithmetic.State Unit
abbrev State (width : ℕ) := Sum (Sum GuardState (StandardGaussJordanClearStep.State width)) Unit

noncomputable instance statesFinite (width : ℕ) : Fintype (State width) := by
  letI : Fintype (StandardGaussJordanClearStep.State width) := inferInstance
  dsimp only [State, GuardState]
  infer_instance

def dataTape (slot : Fin 18) : TapeName := .inl (StandardGaussJordanClearStep.dataTape slot)
def workingTape : TapeName := .inl StandardGaussJordanClearStep.workingTape
def columnTape : TapeName := .inl StandardGaussJordanClearStep.columnTape
def sizeTape (parameter : Fin 3) : TapeName := .inl (StandardGaussJordanClearStep.sizeTape parameter)
def limitTape : TapeName := .inr 0
def differenceTape : TapeName := .inr 1
def guardTape : TapeName := .inr 2

noncomputable def domains (enumeration : Scalar ≃ Fin cardinality) :
    TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardGaussJordanClearStep.domains enumeration name
  | .inr name => if name = 2 then EncodedDomain.booleans else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl name => StandardGaussJordanClearStep.readOnly name
  | .inr name => decide (name = 0)

def bodyWiring : StandardGaussJordanClearStep.TapeName ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

@[simp] theorem bodyWiring_apply (name : StandardGaussJordanClearStep.TapeName) :
    bodyWiring name = .inl name := rfl

def guardWiring : Sum Unit (Fin 4) ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => dataTape 1 | 1 => limitTape | 2 => differenceTape | _ => guardTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;>
      simp_all [dataTape, sizeTape, limitTape, differenceTape, guardTape,
        StandardGaussJordanClearStep.dataTape, StandardGaussJordanClearStep.sizeTape,
        StandardGaussJordanClearTarget.dataTape, StandardGaussJordanClearTarget.sizeTape,
        StandardMatrixRows.dataTape, StandardMatrixRows.sizeTape]⟩

@[simp] theorem guardWiring_apply (name : Sum Unit (Fin 4)) : guardWiring name =
    (match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => dataTape 1 | 1 => limitTape | 2 => differenceTape | _ => guardTape) := rfl

noncomputable def guard : Machine Alphabet GuardState :=
  MultiTape.wire guardWiring BinarySubtraction.algorithm

noncomputable def body (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanClearStep.State
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.wire bodyWiring (StandardGaussJordanClearStep.machine enumeration)

def result (symbols : Symbols Alphabet) : Bool := decide (symbols guardTape = Binary.data true)

noncomputable def machine (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (State ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.withExit (MultiTape.whileMachine guard (body enumeration)
    BinarySubtraction.entry
    (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)) result)

def entry (width : ℕ) : State width := .inl (.inl BinarySubtraction.entry)
def exit (width : ℕ) : State width := .inr ()

@[simp] theorem guard_halt (symbols : Symbols Alphabet) :
    guard BinarySubtraction.exit symbols = none := by
  simp [guard, MultiTape.wire, BinarySubtraction.algorithm, BinarySubtraction.exit,
    StandardBinaryArithmetic.algorithm, StandardBinaryArithmetic.exit, MultiTape.withExit]

@[simp] theorem body_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    body enumeration
      (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      symbols = none := by
  simp [body, MultiTape.wire, StandardGaussJordanClearStep.halt]

@[simp] theorem halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    machine enumeration (exit ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := rfl

omit [Field Scalar] in
/-- The restoring guard tests the target against the interval limit. Its two
outputs may initially contain blanks or arbitrary bits; all other tapes stay
unchanged, including both operands and the working matrix. -/
theorem guard_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (targetRow limit : Fin (2 ^ sizes 0)),
      initial (sizeTape 0) = unary (sizes 0) →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial guardTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly guard ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final guardTape = encoded EncodedDomain.booleans sizes (decide (targetRow.val < limit.val)) ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := BinarySubtraction.comparison_contract.wired_runs guardWiring
  refine ⟨MvPolynomial.rename (fun _ : Unit => (0 : Fin 3)) bound, ?_⟩
  intro sizes initial targetRow limit header targetEq limitEq differenceRegion guardRegion
  let localSizes : Unit → ℕ := fun _ => sizes 0
  let input : Inputs BinarySubtraction.domains BinarySubtraction.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr name =>
      by_cases first : name = 0
      · subst name; exact targetRow
      · by_cases second : name = 1
        · subst name; exact limit
        · have writable : BinarySubtraction.argumentReadOnly (.inr name) = false := by
            fin_cases name <;> first | rfl | contradiction
          rw [writable] at readonly
          contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute localSizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;>
        simp [domains, StandardGaussJordanClearStep.domains, StandardGaussJordanClearTarget.domains,
          StandardMatrixRows.domains, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains,
          BinarySubtraction.domains, StandardBinaryArithmetic.domains, EncodedDomain.unary,
          EncodedDomain.binaryNaturals, EncodedDomain.booleans, EncodedDomain.fixed,
          EncodedDomain.ofCodec, sizeTape, dataTape, StandardGaussJordanClearStep.sizeTape,
          StandardGaussJordanClearStep.dataTape, StandardGaussJordanClearTarget.sizeTape,
          StandardGaussJordanClearTarget.dataTape, StandardMatrixRows.sizeTape,
          StandardMatrixRows.dataTape, limitTape, differenceTape, guardTape, localSizes])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      trivial
      (by
        intro name readonly
        fin_cases name
        · change initial (sizeTape 0) = encoded (EncodedDomain.unary ()) localSizes PUnit.unit
          rw [encoded_unary]
          exact header
        · change initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals ()) localSizes targetRow
          simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits_cast, localSizes] using targetEq
        · change initial (limitTape) = encoded (EncodedDomain.binaryNaturals ()) localSizes limit
          simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
            EncodedDomain.ArrayEncoding.bits_cast, localSizes] using limitEq
        · contradiction
        · contradiction)
      (by
        intro name writable
        fin_cases name
        · contradiction
        · contradiction
        · contradiction
        · convert differenceRegion using 1 <;>
            norm_num [domains, differenceTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] <;> rfl
        · convert guardRegion using 1 <;>
            norm_num [domains, guardTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec] <;> rfl)
      (by intro parameter; cases parameter; exact header)
  refine ⟨ticks, final, ?_, trace, ?_, ?_, ?_⟩
  · simpa only [MvPolynomial.eval_rename, localSizes, Function.comp_def] using cost
  · have flag := canonical true
    change final guardTape = encoded EncodedDomain.booleans localSizes (output true) at flag
    change output true = decide (targetRow.val < limit.val) at correct
    rw [correct] at flag
    simpa only [encoded, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast] using flag
  · have result := canonical false
    change final differenceTape = encoded (EncodedDomain.binaryNaturals ()) localSizes (output false) at result
    refine ⟨output false, ?_⟩
    simpa only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
      EncodedDomain.ArrayEncoding.bits_cast, localSizes] using result
  · intro name notDifference notGuard
    apply preserved_of_wiring guardWiring BinarySubtraction.argumentReadOnly initial final outside immutable
    intro localName equal
    fin_cases localName
    · rfl
    · rfl
    · rfl
    · exact False.elim (notDifference equal.symm)
    · exact False.elim (notGuard equal.symm)

/-- The row body shares the interval workspace without touching its limit or
comparison outputs. Its matrix result and next target counter are canonical. -/
theorem body_runs (enumeration : Scalar ≃ Fin cardinality) :
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
          (body enumeration) ticks
          (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
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
        (∀ slot : Fin 3, final (.inr slot) = initial (.inr slot)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanClearStep.runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow targetRow column sourceValid targetValid matrix
    columnsFit columnValid capacity sourceEq targetEq columnEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, ⟨within, resultEq⟩, counterEq⟩ :=
    execute sizes (fun name => initial (.inl name)) sourceRow targetRow column
      sourceValid targetValid matrix columnsFit columnValid capacity sourceEq targetEq columnEq
      matrixEq headers (fun name => regions (.inl name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring bodyWiring
    (fun name => (domains enumeration name).width sizes) readOnly
    (fun _ => rfl) (fun _ premise => premise) initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace,
    ⟨within, (located _).trans resultEq⟩,
    (located _).trans counterEq, ?_⟩
  · intro slot
    exact outside (.inr slot) (by
      rintro ⟨name, equal⟩
      cases equal)

/-- An exhausted interval evaluates its guard and exits without invoking the
row-clear body. This also covers an empty interval on the first call. -/
theorem stopped_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (targetRow limit : Fin (2 ^ sizes 0)), limit.val ≤ targetRow.val →
      initial (sizeTape 0) = unary (sizes 0) →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial guardTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (machine enumeration) ticks
          (entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final guardTape = encoded EncodedDomain.booleans sizes false ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := guard_runs enumeration
  refine ⟨bound + 1, ?_⟩
  intro sizes initial targetRow limit exhausted header targetEq limitEq differenceRegion guardRegion
  obtain ⟨ticks, final, cost, trace, flagEq, differenceEq, outside⟩ :=
    execute sizes initial targetRow limit header targetEq limitEq differenceRegion guardRegion
  have notBefore : ¬ targetRow.val < limit.val := by omega
  simp only [notBefore, decide_false] at flagEq
  let controller := MultiTape.whileMachine guard (body enumeration) BinarySubtraction.entry
    (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim)) result
  have lifted := trace.rename Sum.inl (target := controller)
    (by intro state symbols next actions instruction; simp [controller, MultiTape.whileMachine, instruction])
  have stopped : result (MultiTape.read final) = false := by
    unfold result MultiTape.read
    rw [flagEq, encoded_booleans]
    rfl
  have noNext : controller (.inl BinarySubtraction.exit) (MultiTape.read final) = none := by
    simp [controller, MultiTape.whileMachine, guard_halt, stopped]
  refine ⟨ticks + 1, final, ?_, ?_, flagEq, differenceEq, outside⟩
  · simpa only [map_add, map_one] using Nat.add_le_add_right cost 1
  · exact lifted.withExit_at noNext

end Polytime2.StandardGaussJordanClearInterval
