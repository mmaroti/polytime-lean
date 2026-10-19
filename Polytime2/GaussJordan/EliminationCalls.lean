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

import Polytime2.Arithmetic.BoundedTraversal
import Polytime2.GaussJordan.Elimination

/-! # Safe calls in the outer elimination controller -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

omit [Field Scalar] in
theorem commitMatrix_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (initial : Tapes Alphabet)
    (resultEq : initial resultTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)
    (region : Region ((matrixDomain (FieldRow.scalarDomain enumeration)).width sizes)
      0 (initial workingTape)) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly commitMatrix
      (2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2)
      0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial workingTape
        (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix)) := by
  simpa only [commitMatrix] using
    StandardTapeCommands.copy_encoded_runs (matrixDomain (FieldRow.scalarDomain enumeration))
      sizes matrix resultTape workingTape (by decide)
      (fun name => (domains enumeration name).width sizes) readOnly (by decide) rfl rfl
      initial resultEq region

omit [Field Scalar] in
theorem commitRow_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (row : Fin (2 ^ sizes 0)) (initial : Tapes Alphabet)
    (resultEq : initial nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes row)
    (region : Region (sizes 0) 0 (initial pivotTape)) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly commitRow
      (2 * sizes 0 + 2) 0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial pivotTape (encoded (EncodedDomain.binaryNaturals 0) sizes row)) := by
  simpa only [commitRow, EncodedDomain.binaryNaturals_width] using
    StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
      sizes row nextRowTape pivotTape (by decide)
      (fun name => (domains enumeration name).width sizes) readOnly (by decide) rfl rfl
      initial resultEq (by
        simpa only [show (domains enumeration pivotTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using region)

omit [Field Scalar] in
theorem commitColumn_runs (enumeration : Scalar ≃ Fin cardinality) (sizes : Fin 3 → ℕ)
    (columnIndex : Fin (2 ^ sizes 0)) (initial : Tapes Alphabet)
    (resultEq : initial nextColumnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex)
    (region : Region (sizes 0) 0 (initial columnTape)) :
    Runs (fun name => (domains enumeration name).width sizes) readOnly commitColumn
      (2 * sizes 0 + 2) 0 (fun _ => 0) initial 2 (fun _ => 0)
      (Function.update initial columnTape (encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex)) := by
  simpa only [commitColumn, EncodedDomain.binaryNaturals_width] using
    StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
      sizes columnIndex nextColumnTape columnTape (by decide)
      (fun name => (domains enumeration name).width sizes) readOnly (by decide) rfl rfl
      initial resultEq (by
        simpa only [show (domains enumeration columnTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using region)

omit [Field Scalar] in
theorem increment_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (columnIndex : Fin (2 ^ sizes 0)),
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial nextColumnTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly increment ticks
          (.inl (.inl true)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
        final nextColumnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (StandardBinaryIncrement.next 0 sizes columnIndex) ∧
        (∀ name, name ≠ nextColumnTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := (StandardBinaryIncrement.contract (0 : Fin 3)).wired_runs incrementWiring
  refine ⟨bound, ?_⟩
  intro sizes initial columnIndex columnEq headers region
  let input : Inputs (StandardBinaryScan.domains (EncodedDomain.binaryNaturals (0 : Fin 3))
      (EncodedDomain.binaryNaturals 0)) StandardTerminatedCopy.readOnly sizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl parameter => exact PUnit.unit
    | inr output => cases output with
      | false => exact columnIndex
      | true => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name; fin_cases name <;> decide) trivial
      (by
        intro name readonly
        cases name with
        | inl parameter =>
          change initial (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit
          rw [encoded_unary]
          exact headers parameter
        | inr output => cases output with
          | false => exact columnEq
          | true => contradiction)
      (by
        intro name writable
        fin_cases name <;> first
          | contradiction
          | change Region ((EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes) 0 (initial nextColumnTape)
            simpa only [EncodedDomain.binaryNaturals_width] using region) headers
  refine ⟨ticks, final, cost, trace, ?_, ?_⟩
  · have result := canonical ()
    change output () = StandardBinaryIncrement.next 0 sizes columnIndex at correct
    rw [correct] at result
    exact result
  · intro name notNext
    apply preserved_of_wiring incrementWiring StandardTerminatedCopy.readOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr output => cases output with
      | false => rfl
      | true => exact False.elim (notNext equal.symm)

omit [Field Scalar] in
theorem guard_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (columnIndex limit : Fin (2 ^ sizes 0)),
      initial (sizeTape 0) = unary (sizes 0) →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial guardTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly guard ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final guardTape = encoded EncodedDomain.booleans sizes (decide (columnIndex.val < limit.val)) ∧
        (∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) := by
  exact BinaryTraversal.comparison_runs 0 (fun sizes name => (domains enumeration name).width sizes)
    readOnly guardWiring
    (by
      intro sizes name
      fin_cases name
      · change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = (EncodedDomain.unary.{0, 0} ()).width _
        simp [EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = (EncodedDomain.booleans (Parameter := Unit)).width _
        simp [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)

end Polytime2.StandardGaussJordanElimination
