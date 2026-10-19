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

import Polytime2.Matrices.RowsCalls
import Polytime2.Machine.CallingConventionWhile

/-! # Guarded traversal of all columns of two matrix rows -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention
open StandardMatrixEntry (index_lt)

abbrev LoopState (width : ℕ) := Sum
  (Sum (Sum StandardBinaryArithmetic.State Unit) (StandardMatrixRowStep.State width)) Unit

instance loopFinite (width : ℕ) : Fintype (LoopState width) := by
  letI : Fintype (StandardMatrixRowStep.State width) := inferInstance
  dsimp only [LoopState]
  infer_instance

noncomputable def loop (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    Machine Alphabet (LoopState (scalar.width Empty.elim)) :=
  MultiTape.withExit (MultiTape.whileMachine guard (body writeSource scalar operation)
    BinarySubtraction.entry (StandardMatrixRowStep.entry (scalar.width Empty.elim)) result)

def loopEntry (width : ℕ) : LoopState width := .inl (.inl BinarySubtraction.entry)
def loopExit (width : ℕ) : LoopState width := .inr ()

@[simp] theorem loop_halt (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (symbols : Symbols Alphabet) : loop writeSource scalar operation (loopExit (scalar.width Empty.elim)) symbols = none := rfl

/-- The mathematical array after the first `count` columns. Indices and scalar
operations act on mathematical values; no tape representation occurs here. -/
noncomputable def processed (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment)
    (sizes : Fin 3 → ℕ) (sourceRow targetRow : Fin (2 ^ sizes 0))
    (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
    (coefficient : scalar.Carrier Empty.elim)
    (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes) :
    ℕ → (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes
  | 0 => array
  | count + 1 =>
    let current := processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array count
    if valid : count < sizes 2 then
      let sourceIndex := ⟨sourceRow.val * sizes 2 + count, index_lt sizes sourceRow.val count sourceValid valid⟩
      let targetIndex := ⟨targetRow.val * sizes 2 + count, index_lt sizes targetRow.val count targetValid valid⟩
      let values := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
        coefficient (current sourceIndex) (current targetIndex)
      Function.update (Function.update current sourceIndex values.1) targetIndex values.2
    else current

private theorem result_of_encoded {sizes : Fin 3 → ℕ} (tapes : Tapes Alphabet) (bit : Bool)
    (encodedFlag : tapes guardTape = encoded EncodedDomain.booleans sizes bit) :
    result (MultiTape.read tapes) = bit := by
  unfold result MultiTape.read
  rw [encodedFlag, encoded_booleans]
  cases bit <;> rfl

/-- The bounded binary column counter reaches the declared limit. Both the
working and result matrices contain the same completed row operation, including
for zero columns; private scratch needs only bounded regions. -/
theorem loop_runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow : Fin (2 ^ sizes 0))
      (sourceValid : sourceRow.val < sizes 1) (targetValid : targetRow.val < sizes 1)
      (coefficient : scalar.Carrier Empty.elim)
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (fits : sizes 2 < 2 ^ sizes 0), sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) →
      initial (dataTape 3) = encoded scalar Empty.elim coefficient →
      initial (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (loop writeSource scalar operation) ticks
          (loopEntry (scalar.width Empty.elim)) (fun _ => 0) initial (loopExit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes
          (processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array (sizes 2)) ∧
        final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ := by
  obtain ⟨guardBound, executeGuard⟩ := guard_runs scalar
  obtain ⟨bodyBound, executeBody⟩ := body_runs writeSource scalar operation
  refine ⟨(MvPolynomial.X 2 + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro sizes initial sourceRow targetRow sourceValid targetValid coefficient array fits capacity
    sourceEq targetEq columnEq coefficientEq workEq matrixEq limitEq headers regions
  let width : TapeName → ℕ := fun name => (domains scalar name).width sizes
  let current := processed writeSource scalar operation sizes sourceRow targetRow sourceValid targetValid coefficient array
  let representation (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    ∃ counterFits : count < 2 ^ sizes 0,
      tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow ∧
      tapes (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow ∧
      tapes (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨count, counterFits⟩ ∧
      tapes (dataTape 3) = encoded scalar Empty.elim coefficient ∧
      tapes (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count) ∧
      tapes (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count) ∧
      tapes limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
      (∀ parameter, tapes (sizeTape parameter) = unary (sizes parameter)) ∧
      (∀ name, Region (width name) 0 (tapes name))
  have executeGuarded : ∀ count, 0 ≤ count → count ≤ sizes 2 → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes guardBound ∧
        Runs width readOnly guard ticks BinarySubtraction.entry (fun _ => 0) tapes
          BinarySubtraction.exit (fun _ => 0) final ∧
        (representation count final ∧ result (MultiTape.read final) = decide (count < sizes 2)) := by
    intro count lower upper tapes represented
    obtain ⟨counterFits, sourceEq, targetEq, columnEq, coefficientEq, workEq, matrixEq,
      limitEq, headers, regions⟩ := represented
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, flagEq, difference, guardOutside⟩ :=
      executeGuard sizes tapes ⟨count, counterFits⟩ ⟨sizes 2, fits⟩ (headers 0) columnEq limitEq
        (by simpa [width, domains, differenceTape, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec] using regions differenceTape)
        (by simpa [width, domains, guardTape, EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec,
          show Nat.clog 2 2 = 1 from by decide] using regions guardTape)
    have guardedRegions : ∀ name, Region (width name) 0 (guarded name) := fun name => guardTrace.region name (regions name)
    have tested : result (MultiTape.read guarded) = decide (count < sizes 2) := result_of_encoded guarded _ flagEq
    refine ⟨guardTicks, guarded, guardCost, guardTrace, ?_, tested⟩
    exact ⟨counterFits,
      (guardTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq,
      (guardTrace.readOnly_tape (dataTape 1) rfl).trans targetEq,
      (guardOutside (dataTape 2) (by decide) (by decide)).trans columnEq,
      (guardTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq,
      (guardOutside (dataTape 4) (by decide) (by decide)).trans workEq,
      (guardOutside (dataTape 5) (by decide) (by decide)).trans matrixEq,
      (guardOutside limitTape (by decide) (by decide)).trans limitEq,
      (fun parameter => (guardTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
      guardedRegions⟩
  have executeAdvanced : ∀ count, 0 ≤ count → count < sizes 2 → ∀ tapes,
      representation count tapes → ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bodyBound ∧
        Runs width readOnly (body writeSource scalar operation) ticks
          (StandardMatrixRowStep.entry (scalar.width Empty.elim)) (fun _ => 0) tapes
          (StandardMatrixRowStep.exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        representation (count + 1) final := by
    intro count lower valid tapes represented
    obtain ⟨counterFits, sourceEq, targetEq, columnEq, coefficientEq, workEq, matrixEq,
      limitEq, headers, regions⟩ := represented
    obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextWorkEq, nextResultEq, nextColumnEq, bodyOutside⟩ :=
      executeBody sizes tapes sourceRow targetRow ⟨count, counterFits⟩ (current count) coefficient
        (index_lt sizes sourceRow.val count sourceValid valid) (index_lt sizes targetRow.val count targetValid valid)
        fits sourceValid targetValid valid capacity
        sourceEq
        targetEq
        columnEq
        coefficientEq
        workEq
        headers regions
    have nextFits : count + 1 < 2 ^ sizes 0 := by omega
    have nextValue : StandardBinaryIncrement.next 0 sizes ⟨count, counterFits⟩ = (⟨count + 1, nextFits⟩ : Fin (2 ^ sizes 0)) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt nextFits
    rw [nextValue] at nextColumnEq
    let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
      ⟨sourceRow.val * sizes 2 + count, index_lt sizes sourceRow.val count sourceValid valid⟩
    let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
      ⟨targetRow.val * sizes 2 + count, index_lt sizes targetRow.val count targetValid valid⟩
    let values := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
      coefficient (current count sourceIndex) (current count targetIndex)
    have nextArray : current (count + 1) =
        Function.update (Function.update (current count) sourceIndex values.1) targetIndex values.2 := by
      dsimp only [current]
      rw [processed]
      exact dite_eq_left valid
    have nextWorkEq' : advanced (dataTape 4) =
        encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current (count + 1)) := by
      exact nextWorkEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm)
    have nextResultEq' : advanced (dataTape 5) =
        encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current (count + 1)) := by
      exact nextResultEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm)
    refine ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextFits,
      (bodyTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq,
      (bodyTrace.readOnly_tape (dataTape 1) rfl).trans targetEq, nextColumnEq,
      (bodyTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq,
      nextWorkEq', nextResultEq', (bodyOutside 0).trans limitEq,
      (fun parameter => (bodyTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter)),
      (fun name => bodyTrace.region name (regions name))⟩
  obtain ⟨ticks, final, cost, trace, represented, stopped⟩ :=
    Runs.whileRange width readOnly guard (body writeSource scalar operation)
      BinarySubtraction.entry BinarySubtraction.exit
      (StandardMatrixRowStep.entry (scalar.width Empty.elim))
      (StandardMatrixRowStep.exit (scalar.width Empty.elim)) result representation
      (fun count tapes => representation count tapes ∧
        result (MultiTape.read tapes) = decide (count < sizes 2))
      0 (sizes 2) (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes bodyBound)
      (by omega) guard_halt
      (by intro symbols; simp [body, MultiTape.wire, StandardMatrixRowStep.halt])
      executeGuarded (fun count lower before tapes valid => executeAdvanced count lower before tapes valid.1)
      (fun _ _ _ _ valid => valid.2) initial
      ⟨by positivity, sourceEq, targetEq, columnEq, coefficientEq, workEq, matrixEq,
        limitEq, headers, regions⟩
  obtain ⟨counterFits, _, _, finalColumn, _, _, finalMatrix, _, _, _⟩ := represented
  refine ⟨ticks, final, ?_, trace, finalMatrix, finalColumn⟩
  simpa only [Nat.sub_zero, map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval_X] using cost

end Polytime2.StandardMatrixRows
