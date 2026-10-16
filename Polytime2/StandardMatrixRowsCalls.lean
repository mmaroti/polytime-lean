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

import Polytime2.StandardMatrixRowsInit

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
  obtain ⟨scratch, scratchLength, final, trace, resultEq, scratchEq, outside, immutable⟩ :=
    StandardSizeRead.Internal.runs_wired limitWiring localSizes
      (fun name => (domains scalar name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      (by intro name; cases name <;> exact headers _) limitRegion scratchRegion
  let resultBits := StandardSizeRead.advanceBits (sizes 2) (List.replicate (sizes 0) false)
  have resultLength : resultBits.length = sizes 0 := by simp [resultBits]
  have resultValue : Binary.value resultBits = sizes 2 := by
    simp [resultBits, StandardSizeRead.advanceBits_value, Nat.mod_eq_of_lt fits]
  have resultEncoding := encoded_binaryNaturals (0 : Fin 3) sizes resultBits resultLength
  have naturalEq : (⟨Binary.value resultBits, by
      simpa only [resultLength] using Binary.value_lt_pow_length resultBits⟩ : Fin (2 ^ sizes 0)) =
      ⟨sizes 2, fits⟩ := Fin.ext resultValue
  rw [naturalEq] at resultEncoding
  let scratchValue : Fin (2 ^ sizes 0) := ⟨Binary.value scratch, by
    simpa only [show scratch.length = sizes 0 from scratchLength] using Binary.value_lt_pow_length scratch⟩
  refine ⟨_, final, ?_, trace, resultEq.trans resultEncoding.symm,
    ⟨scratchValue, scratchEq.trans (encoded_binaryNaturals 0 sizes scratch scratchLength).symm⟩, ?_⟩
  · simp [localSizes]
  · intro name notLimit notScratch
    apply preserved_of_wiring limitWiring StandardSizeRead.argumentReadOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr name => cases name with
      | false => exact False.elim (notLimit equal.symm)
      | true => exact False.elim (notScratch equal.symm)

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
        (∀ name, StandardMatrixRowStep.readOnly name = false → ∃ value : (domains scalar (.inl name)).Carrier sizes,
          final (.inl name) = encoded (domains scalar (.inl name)) sizes value) ∧
        (∀ name : Fin 4, final (.inr name) = initial (.inr name)) := by
  obtain ⟨bound, execute⟩ := StandardMatrixRowStep.runs writeSource scalar operation
  refine ⟨bound, ?_⟩
  intro sizes initial sourceRow targetRow column array coefficient sourceWithin targetWithin columnsFit
    sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers regions
    sourceIndex targetIndex values resultArray
  obtain ⟨ticks, localFinal, cost, localTrace, workEq, resultEq, nextEq, canonical⟩ :=
    execute sizes (fun name => initial (.inl name)) sourceRow targetRow column array coefficient sourceWithin targetWithin
      columnsFit sourceValid targetValid columnValid capacity sourceEq targetEq columnEq coefficientEq arrayEq headers
      (fun name => regions (.inl name))
  have trace := localTrace.wire stepWiring (fun name => (domains scalar name).width sizes) readOnly
    (fun _ => rfl) (fun _ premise => premise) initial (fun _ => 0)
  have start : install stepWiring (fun name => initial (.inl name)) initial = initial := install_self stepWiring initial
  have positions : install stepWiring (fun _ : StandardMatrixRowStep.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self stepWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install stepWiring localFinal initial, cost, trace, ?_, ?_, ?_, ?_, ?_⟩
  · exact (install_at stepWiring localFinal initial (.inl (.inr 4))).trans workEq
  · exact (install_at stepWiring localFinal initial (.inl (.inr 5))).trans resultEq
  · exact (install_at stepWiring localFinal initial (.inl (.inr 2))).trans nextEq
  · intro name writable
    obtain ⟨value, canonical⟩ := canonical name writable
    exact ⟨value, (install_at stepWiring localFinal initial name).trans canonical⟩
  · intro name
    apply install_outside
    rintro ⟨localName, equal⟩
    cases equal

end Polytime2.StandardMatrixRows
