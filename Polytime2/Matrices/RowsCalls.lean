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

import Polytime2.Matrices.RowsInit
import Polytime2.Primitives.Initialization

/-! # Size reading and column calls in a complete row workspace -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

def limitWiring : Sum Bool Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl false => sizeTape 2 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => dataTape 12), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [sizeTape, dataTape, limitTape]⟩

@[simp] theorem limitWiring_apply (name : Sum Bool Bool) : limitWiring name =
    (match name with
    | .inl false => sizeTape 2 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => dataTape 12) := rfl

noncomputable def readLimit : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire limitWiring StandardSizeRead.algorithm

@[simp] theorem readLimit_halt (symbols : Symbols Alphabet) : readLimit StandardSizeRead.exit symbols = none := by
  simp [readLimit, MultiTape.wire, StandardSizeRead.algorithm]

theorem readLimit_runs (scalar : EncodedDomain.{0, 0} Empty) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (fits : sizes 2 < 2 ^ sizes 0),
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial limitTape) → Region (sizes 0) 0 (initial (dataTape 12)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly readLimit ticks
          StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final (dataTape 12) = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ limitTape → name ≠ dataTape 12 → final name = initial name) := by
  refine ⟨4 * MvPolynomial.X 0 + MvPolynomial.X 2 * (4 * MvPolynomial.X 0 + 8) + 11, ?_⟩
  intro sizes initial fits headers limitRegion scratchRegion
  let localSizes : Bool → ℕ := fun name => if name then sizes 0 else sizes 2
  obtain ⟨final, trace, resultEq, scratchEq, outside⟩ :=
    Initialization.readSize_runs limitWiring 2 0 sizes
      (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;>
        simp [domains, StandardMatrixRowStep.domains, StandardMatrixRowEntry.domains,
          StandardSizeRead.domains,
          EncodedDomain.unary, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
          sizeTape, dataTape, limitTape, localSizes])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      (by intro name; cases name <;> exact headers _) fits limitRegion scratchRegion
  refine ⟨_, final, ?_, trace, resultEq, scratchEq, outside⟩
  simp [localSizes]

/-- Column calls leave the comparison workspace and original matrix unchanged.
Only private matrix and counter tapes are mutable in the body. -/
theorem body_runs (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (sourceRow targetRow column : Fin (2 ^ sizes 0))
      (array : (scalar.constant.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
      (coefficient : scalar.Carrier Empty.elim)
      (sourceWithin : sourceRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length)
      (targetWithin : targetRow.val * sizes 2 + column.val < MvPolynomial.eval sizes StandardMatrixEntry.length),
      sizes 2 < 2 ^ sizes 0 → sourceRow.val < sizes 1 → targetRow.val < sizes 1 →
      column.val < sizes 2 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes sourceRow →
      initial (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes targetRow →
      initial (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial (dataTape 3) = encoded scalar Empty.elim coefficient →
      initial (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes array →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains scalar name).width sizes) 0 (initial name)) →
      let sourceIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨sourceRow.val * sizes 2 + column.val, sourceWithin⟩
      let targetIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) := ⟨targetRow.val * sizes 2 + column.val, targetWithin⟩
      let values := StandardMatrixRowEntry.effectiveOperation writeSource scalar operation Empty.elim
        coefficient (array sourceIndex) (array targetIndex)
      let resultArray := Function.update (Function.update array sourceIndex values.1) targetIndex values.2
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains scalar name).width sizes) readOnly (body writeSource scalar operation) ticks
          (StandardMatrixRowStep.entry (scalar.width Empty.elim)) (fun _ => 0) initial
          (StandardMatrixRowStep.exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
        final (dataTape 4) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray ∧
        final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) sizes resultArray ∧
        final (dataTape 2) = encoded (EncodedDomain.binaryNaturals 0) sizes (StandardBinaryIncrement.next 0 sizes column) ∧
        (∀ name : Fin 4, final (.inr name) = initial (.inr name)) := by
  obtain ⟨bound, execute⟩ := StandardMatrixRowStep.runs writeSource scalar operation
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin columnsFit
    sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers regions
    sourceIndex targetIndex values resultArray
  obtain ⟨ticks, localFinal, cost, localTrace, workEq, resultEq, nextEq⟩ :=
    execute sizes (fun name => initial (.inl name)) sourceRow targetRow column array coefficient sourceWithin targetWithin
      columnsFit sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers
      (fun name => regions (.inl name))
  obtain ⟨final, trace, located, outside, immutable⟩ :=
    localTrace.wire_restoring stepWiring (fun name => (domains scalar name).width sizes) readOnly
    (fun _ => rfl) (fun _ premise => premise) initial (fun _ => rfl)
  refine ⟨ticks, final, cost, trace, ?_, ?_, ?_, ?_⟩
  · exact (located (.inl (.inr 4))).trans workEq
  · exact (located (.inl (.inr 5))).trans resultEq
  · exact (located (.inl (.inr 2))).trans nextEq
  · intro name
    apply outside
    rintro ⟨localName, equal⟩
    cases equal

end Polytime2.StandardMatrixRows
