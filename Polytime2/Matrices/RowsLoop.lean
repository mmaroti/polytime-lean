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
import Polytime2.Arithmetic.TraversalLoop

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
  let invariant (count : ℕ) (tapes : Tapes Alphabet) : Prop :=
    tapes (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow ∧
    tapes (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow ∧
    tapes (dataTape 3) = encoded scalar Empty.elim coefficient ∧
    tapes (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count) ∧
    tapes (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes (current count)
  obtain ⟨ticks, final, cost, trace, finalValues, finalCounter⟩ :=
    BinaryTraversal.range_runs 0 sizes width readOnly guardWiring guardBound bodyBound
      (MvPolynomial.X 2) (executeGuard sizes)
      (by change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = sizes 0; simp)
      (by change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = 1
          norm_num [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
      sizeTape rfl (by intro parameter; rfl) (body writeSource scalar operation)
      (StandardMatrixRowStep.entry (scalar.width Empty.elim))
      (StandardMatrixRowStep.exit (scalar.width Empty.elim))
      (by intro symbols; simp [body, MultiTape.wire, StandardMatrixRowStep.halt])
      invariant (by
        intro count tapes final preserved represented
        obtain ⟨sourceEq, targetEq, coefficientEq, workEq, matrixEq⟩ := represented
        exact ⟨(preserved (dataTape 0) (by decide) (by decide)).trans sourceEq,
          (preserved (dataTape 1) (by decide) (by decide)).trans targetEq,
          (preserved (dataTape 3) (by decide) (by decide)).trans coefficientEq,
          (preserved (dataTape 4) (by decide) (by decide)).trans workEq,
          (preserved (dataTape 5) (by decide) (by decide)).trans matrixEq⟩)
      ⟨0, by positivity⟩ ⟨sizes 2, fits⟩ (by simp) (by simp)
      (by
        intro count counterFits lower valid nextFits nextValue tapes represented columnEq limitEq headers regions
        obtain ⟨sourceEq, targetEq, coefficientEq, workEq, matrixEq⟩ := represented
        obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, nextWorkEq, nextResultEq, nextColumnEq, bodyOutside⟩ :=
          executeBody sizes tapes sourceRow targetRow ⟨count, counterFits⟩ (current count) coefficient
            (index_lt sizes sourceRow.val count sourceValid valid)
            (index_lt sizes targetRow.val count targetValid valid)
            fits sourceValid targetValid valid capacity
            sourceEq targetEq columnEq coefficientEq workEq headers regions
        rw [nextValue] at nextColumnEq
        let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
          ⟨sourceRow.val * sizes 2 + count, index_lt sizes sourceRow.val count sourceValid valid⟩
        let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
          ⟨targetRow.val * sizes 2 + count, index_lt sizes targetRow.val count targetValid valid⟩
        let output := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
          coefficient (current count sourceIndex) (current count targetIndex)
        have nextArray : current (count + 1) =
            Function.update (Function.update (current count) sourceIndex output.1) targetIndex output.2 := by
          dsimp only [current]
          rw [processed]
          exact dite_eq_left valid
        refine ⟨bodyTicks, advanced, bodyCost, bodyTrace, ?_, nextColumnEq, bodyOutside 0⟩
        exact ⟨(bodyTrace.readOnly_tape (dataTape 0) rfl).trans sourceEq,
          (bodyTrace.readOnly_tape (dataTape 1) rfl).trans targetEq,
          (bodyTrace.readOnly_tape (dataTape 3) rfl).trans coefficientEq,
          nextWorkEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm),
          nextResultEq.trans (congrArg (encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes) nextArray.symm)⟩)
      initial ⟨sourceEq, targetEq, coefficientEq, workEq, matrixEq⟩ columnEq limitEq headers regions
  exact ⟨ticks, final, cost, trace, finalValues.2.2.2.2, finalCounter⟩

end Polytime2.StandardMatrixRows
