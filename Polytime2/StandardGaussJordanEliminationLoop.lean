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

import Polytime2.StandardGaussJordanEliminationBody
import Polytime2.CallingConventionWhile

/-! # Polynomial execution of the outer elimination loop -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

/-- The outer loop realizes any mathematical sequence of column steps. The
column counter stops at the dimension, including an empty column interval. -/
theorem loop_runs [DecidableEq Scalar] (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (start : Fin (2 ^ sizes 0)) (_startWithin : start.val ≤ sizes 2)
      (_rowsFit : sizes 1 < 2 ^ sizes 0) (columnsFit : sizes 2 < 2 ^ sizes 0)
      (matrices : ℕ → Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (pivots : ℕ → Fin (2 ^ sizes 0)),
      (∀ count, (pivots count).val ≤ sizes 1) →
      (∀ count (before : count < sizes 2),
        GaussJordan.columnStep (matrices count) (pivots count).val ⟨count, before⟩ =
          (matrices (count + 1), (pivots (count + 1)).val)) →
      sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots start.val) →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes start →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
        (matrices start.val) →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes
        (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (loop enumeration) ticks
          (loopEntry
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) initial
          (loopExit
            ((FieldRow.scalarDomain enumeration).width Empty.elim)) (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (matrices (sizes 2)) ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (sizes 2)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs enumeration
  obtain ⟨bodyBound, executeBody⟩ := body_runs enumeration
  refine ⟨(MvPolynomial.X 2 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial start startWithin rowsFit columnsFit matrices pivots pivotBounds updateLaw
    capacity pivotEq counterEq matrixEq limitEq headers regions
  let width : TapeName → ℕ := fun name => (domains enumeration name).width sizes
  let bodyStart := bodyEntry
    ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let bodyStop := bodyExit
    ((FieldRow.scalarDomain enumeration).width Empty.elim)
  let limit : Fin (2 ^ sizes 0) := ⟨sizes 2, columnsFit⟩
  have sizeReadOnly (parameter : Fin 3) : readOnly (sizeTape parameter) = true := by
    fin_cases parameter <;> decide
  let representation (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    ∃ counterFits : count < 2 ^ sizes 0,
      tapes pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes (pivots count) ∧
      tapes columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ ∧
      tapes workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices count) ∧
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit ∧
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) ∧
      (∀ name, Region (width name) 0 (tapes name))
  have executeGuarded : ∀ count, start.val ≤ count → count ≤ sizes 2 → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly guard ticks BinarySubtraction.entry (fun _ => 0) tapes
          BinarySubtraction.exit (fun _ => 0) final ∧
        (representation count final ∧ continues (MultiTape.read final) = decide (count < sizes 2)) := by
    intro count lower upper tapes represented
    obtain ⟨counterFits, pivotEq, counterEq, matrixEq, limitEq, headers, regions⟩ := represented
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, flagEq, difference, guardOutside⟩ :=
      executeGuard sizes tapes ⟨count, counterFits⟩ limit (headers 0) counterEq limitEq
        (by simpa [width, domains, differenceTape] using regions differenceTape)
        (by simpa [width, domains, guardTape, EncodedDomain.booleans, EncodedDomain.fixed,
          EncodedDomain.ofCodec, show Nat.clog 2 2 = 1 from by decide] using regions guardTape)
    have guardedRegions : ∀ name, Region (width name) 0 (guarded name) :=
      fun name => guardTrace.region name (regions name)
    have tested : continues (MultiTape.read guarded) = decide (count < sizes 2) := by
      unfold continues MultiTape.read
      rw [flagEq, encoded_booleans]
      cases decide (count < sizes 2) <;> rfl
    exact ⟨guardTicks, guarded, guardCost, guardTrace,
      ⟨counterFits, (guardOutside pivotTape (by decide) (by decide)).trans pivotEq,
        (guardOutside columnTape (by decide) (by decide)).trans counterEq,
        (guardOutside workingTape (by decide) (by decide)).trans matrixEq,
        (guardOutside limitTape (by decide) (by decide)).trans limitEq,
        (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
          (headers parameter)), guardedRegions⟩, tested⟩
  have executeAdvanced : ∀ count, start.val ≤ count → count < sizes 2 → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly (body enumeration) ticks bodyStart (fun _ => 0) tapes
          bodyStop (fun _ => 0) final ∧ representation (count + 1) final := by
    intro count lower before tapes represented
    obtain ⟨counterFits, pivotEq, counterEq, matrixEq, limitEq, headers, regions⟩ := represented
    obtain ⟨bodyTicks, advanced, nextRow, nextColumn, bodyCost, bodyTrace, nextMatrixEq,
        nextRowEq, nextRowValue, nextRowBound, nextCounterEq, nextCounterValue,
        bodyOutside⟩ :=
      executeBody sizes tapes (pivots count) ⟨count, counterFits⟩ (matrices count)
        (pivotBounds count) before rowsFit columnsFit capacity
        pivotEq
        counterEq
        matrixEq
        headers regions
    have nextFits : count + 1 < 2 ^ sizes 0 :=
      lt_of_le_of_lt (Nat.succ_le_of_lt before) columnsFit
    have sameCounter : nextColumn = (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) :=
      Fin.ext nextCounterValue
    have sameRow : nextRow = pivots (count + 1) :=
      Fin.ext (nextRowValue.trans (congrArg Prod.snd (updateLaw count before)))
    have nextMatrix : advanced workingTape =
        encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes (matrices (count + 1)) :=
      nextMatrixEq.trans (congrArg (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes)
        (congrArg Prod.fst (updateLaw count before)))
    have nextPivot : advanced pivotTape =
        encoded (EncodedDomain.binaryNaturals 0) sizes (pivots (count + 1)) :=
      nextRowEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameRow)
    have nextCounter : advanced columnTape =
        encoded (EncodedDomain.binaryNaturals 0) sizes (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) :=
      nextCounterEq.trans (congrArg (encoded (EncodedDomain.binaryNaturals 0) sizes) sameCounter)
    exact ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextFits, nextPivot, nextCounter, nextMatrix,
      (bodyOutside 1 (by decide)).trans limitEq,
      (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
        (headers parameter)), (fun name => bodyTrace.region name (regions name))⟩
  obtain ⟨ticks, final, cost, trace, represented, stopped⟩ :=
    Runs.whileRange width readOnly guard (body enumeration)
      BinarySubtraction.entry BinarySubtraction.exit bodyStart bodyStop continues representation
      (fun count tapes => representation count tapes ∧
        continues (MultiTape.read tapes) = decide (count < sizes 2))
      start.val (sizes 2) (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes bodyBound)
      startWithin guard_halt (body_halt enumeration) executeGuarded
      (fun count lower before tapes valid => executeAdvanced count lower before tapes valid.1)
      (fun _ _ _ _ valid => valid.2) initial
      ⟨start.isLt, pivotEq, counterEq, matrixEq, limitEq, headers, regions⟩
  obtain ⟨counterFits, finalPivot, finalCounter, finalMatrix, _, _, _⟩ := represented
  refine ⟨ticks, final, ?_, trace, finalMatrix, finalPivot, finalCounter⟩
  have remainingBound : sizes 2 - start.val + 1 ≤ sizes 2 + 1 := by omega
  have boundedCost := cost.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes bodyBound + 2)
      remainingBound) 1)
  simpa only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using boundedCost

end Polytime2.StandardGaussJordanElimination
