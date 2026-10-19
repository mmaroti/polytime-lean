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

import Polytime2.GaussJordan.ClearInterval
import Polytime2.Arithmetic.TraversalLoop

/-! # Polynomial execution of a complete row-clear interval -/

namespace Polytime2.StandardGaussJordanClearInterval

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- A mathematical sequence of row updates is realized by the guarded
interval traversal. The limit fits the fixed counter capacity, so the target
advances without wrapping. An empty interval only evaluates the guard. -/
theorem loop_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow column start limit : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (columnValid : column.val < sizes 2)
      (limitWithin : limit.val ≤ sizes 1) (_startWithin : start.val ≤ limit.val)
      (current : ℕ → ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      (∀ count (before : count < limit.val), start.val ≤ count →
        StandardMatrixRows.processed false (FieldRow.scalarDomain enumeration)
          (StandardGaussJordanClearTarget.additionOperation enumeration)
          sizes sourceRow ⟨count, lt_trans before limit.isLt⟩ sourceValid
          (lt_of_lt_of_le before limitWithin)
          (Neg.neg (α := Scalar) (current count
            ⟨count * sizes 2 + column.val, StandardMatrixEntry.index_lt sizes count
              column.val (lt_of_lt_of_le before limitWithin) columnValid⟩))
          (current count) (sizes 2) = current (count + 1)) →
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial workingTape = encoded (domains enumeration workingTape) sizes (current start.val) →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (machine enumeration) ticks (entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial (exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes (current limit.val) ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes limit := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs enumeration
  obtain ⟨bodyBound, executeBody⟩ := body_runs enumeration
  refine ⟨(MvPolynomial.X 1 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial sourceRow column start limit sourceValid columnValid limitWithin startWithin
    current updateLaw columnsFit capacity sourceEq counterEq columnEq matrixEq limitEq headers regions
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  let invariant (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow ∧
    tapes (columnTape) = encoded (EncodedDomain.binaryNaturals 0) sizes column ∧
    tapes (workingTape) = encoded (domains enumeration workingTape) sizes (current count)
  obtain ⟨ticks, final, cost, trace, finalValues, finalCounter⟩ :=
    BinaryTraversal.range_runs 0 sizes width readOnly guardWiring guardBound bodyBound
      (MvPolynomial.X 1) (executeGuard sizes)
      (by change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = sizes 0; simp)
      (by change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = 1
          norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
      sizeTape rfl (by intro parameter; rfl) (body enumeration)
      (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (body_halt enumeration) invariant (by
        intro count tapes final preserved represented
        obtain ⟨sourceEq, columnEq, matrixEq⟩ := represented
        exact ⟨(preserved (dataTape 0) (by decide) (by decide)).trans sourceEq,
          (preserved (columnTape) (by decide) (by decide)).trans columnEq,
          (preserved (workingTape) (by decide) (by decide)).trans matrixEq⟩)
      start limit startWithin (by simpa only [MvPolynomial.eval_X] using limitWithin)
      (by
        intro count counterFits lower before nextFits nextValue tapes represented counterEq limitEq headers regions
        obtain ⟨sourceEq, columnEq, matrixEq⟩ := represented
        have targetValid : count < sizes 1 := lt_of_lt_of_le before limitWithin
        obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, ⟨within, nextMatrixEq⟩,
            nextCounterEq, bodyOutside⟩ :=
          executeBody sizes tapes sourceRow ⟨count, counterFits⟩ column sourceValid targetValid
            (current count) columnsFit columnValid capacity
            sourceEq counterEq columnEq matrixEq headers regions
        rw [nextValue] at nextCounterEq
        have nextMatrix : advanced workingTape = encoded (domains enumeration workingTape) sizes
            (current (count + 1)) :=
          nextMatrixEq.trans (congrArg (encoded (domains enumeration workingTape) sizes)
            (updateLaw count before lower))
        refine ⟨bodyTicks, advanced, bodyCost, bodyTrace, ?_, nextCounterEq, bodyOutside 0⟩
        exact ⟨(bodyTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq,
          (bodyTrace.readOnly_tape columnTape rfl).trans columnEq, nextMatrix⟩)
      initial ⟨sourceEq, columnEq, matrixEq⟩ counterEq limitEq headers regions
  exact ⟨ticks, final, cost, trace, finalValues.2.2, finalCounter⟩

end Polytime2.StandardGaussJordanClearInterval
