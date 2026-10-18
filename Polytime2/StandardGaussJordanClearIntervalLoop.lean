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

import Polytime2.StandardGaussJordanClearInterval
import Polytime2.CallingConventionWhile

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
  let representation (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    ∃ counterFits : count < 2 ^ sizes 0,
      tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow ∧
      tapes (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ ∧
      tapes columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column ∧
      tapes workingTape = encoded (domains enumeration workingTape) sizes (current count) ∧
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) ∧
      (∀ name, Region (width name) 0 (tapes name))
  have executeGuarded : ∀ count, start.val ≤ count → count ≤ limit.val → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly guard ticks BinarySubtraction.entry (fun _ => 0) tapes
          BinarySubtraction.exit (fun _ => 0) final ∧
        (representation count final ∧ result (MultiTape.read final) = decide (count < limit.val)) := by
    intro count lower upper tapes represented
    obtain ⟨counterFits, sourceEq, counterEq, columnEq, matrixEq, limitEq, headers,
      regions⟩ := represented
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, flagEq, difference, guardOutside⟩ :=
      executeGuard sizes tapes ⟨count, counterFits⟩ limit (headers 0) counterEq limitEq
        (by simpa [width, domains, differenceTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using regions differenceTape)
        (by simpa [width, domains, guardTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
          show Nat.clog 2 2 = 1 from by decide] using regions guardTape)
    have guardedRegions : ∀ name, Region (width name) 0 (guarded name) :=
      fun name => guardTrace.region name (regions name)
    have tested : result (MultiTape.read guarded) = decide (count < limit.val) := by
      unfold result MultiTape.read
      rw [flagEq, encoded_booleans]
      cases decide (count < limit.val) <;> rfl
    exact ⟨guardTicks, guarded, guardCost, guardTrace,
      ⟨counterFits, (guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq,
        (guardOutside (dataTape 1) (by decide) (by decide)).trans counterEq,
        (guardTrace.readOnly_tape columnTape rfl).trans columnEq,
        (guardOutside workingTape (by decide) (by decide)).trans matrixEq,
        (guardTrace.readOnly_tape limitTape rfl).trans limitEq,
        (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
        guardedRegions⟩, tested⟩
  have executeAdvanced : ∀ count, start.val ≤ count → count < limit.val → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly (body enumeration) ticks
          (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) tapes
          (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧ representation (count + 1) final := by
    intro count lower before tapes represented
    obtain ⟨counterFits, sourceEq, counterEq, columnEq, matrixEq, limitEq, headers,
      regions⟩ := represented
    have targetValid : count < sizes 1 := lt_of_lt_of_le before limitWithin
    obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, ⟨within, nextMatrixEq⟩,
        nextCounterEq, bodyOutside⟩ :=
      executeBody sizes tapes sourceRow ⟨count, counterFits⟩ column sourceValid targetValid
        (current count) columnsFit columnValid capacity
        sourceEq
        counterEq
        columnEq
        matrixEq
        headers
        regions
    have nextFits : count + 1 < 2 ^ sizes 0 := by have fits := limit.isLt; omega
    have nextValue : StandardBinaryIncrement.next 0 sizes ⟨count, counterFits⟩ =
        (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt nextFits
    rw [nextValue] at nextCounterEq
    have nextMatrix : advanced workingTape = encoded (domains enumeration workingTape) sizes
        (current (count + 1)) :=
      nextMatrixEq.trans (congrArg (encoded (domains enumeration workingTape) sizes)
        (updateLaw count before lower))
    exact ⟨bodyTicks, advanced, bodyCost, bodyTrace,
      ⟨nextFits, (bodyTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq, nextCounterEq,
        (bodyTrace.readOnly_tape columnTape rfl).trans columnEq, nextMatrix,
        (bodyOutside 0).trans limitEq,
        (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
        (fun name => bodyTrace.region name (regions name))⟩⟩
  obtain ⟨ticks, final, cost, trace, represented, stopped⟩ :=
    Runs.whileRange width readOnly guard (body enumeration)
      BinarySubtraction.entry BinarySubtraction.exit
      (StandardGaussJordanClearStep.entry ((FieldRow.scalarDomain enumeration).width Empty.elim))
      (StandardGaussJordanClearStep.exit ((FieldRow.scalarDomain enumeration).width Empty.elim))
      result representation
      (fun count tapes => representation count tapes ∧
        result (MultiTape.read tapes) = decide (count < limit.val))
      start.val limit.val (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes bodyBound)
      startWithin guard_halt (body_halt enumeration) executeGuarded
      (fun count lower before tapes valid => executeAdvanced count lower before tapes valid.1)
      (fun _ _ _ _ valid => valid.2) initial
      ⟨start.isLt, sourceEq, counterEq, columnEq, matrixEq, limitEq, headers, regions⟩
  obtain ⟨counterFits, _, finalCounter, _, finalMatrix, _, _, _⟩ := represented
  refine ⟨ticks, final, ?_, trace, finalMatrix, finalCounter⟩
  have remainingBound : limit.val - start.val + 1 ≤ sizes 1 + 1 := by omega
  have boundedCost := cost.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2)
      remainingBound) 1)
  simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using boundedCost

end Polytime2.StandardGaussJordanClearInterval
