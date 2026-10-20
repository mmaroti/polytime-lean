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

import Polytime2.Matrices.RowsMath
import Polytime2.Computation.InternalSize

/-! # Matrix-valued input and output contracts for row operations -/

namespace Polytime2.StandardMatrixRows

open MultiTape CallingConvention

/-- The mathematical carrier exposes an ordinary rectangular matrix. Its
canonical encoding is the controller's existing row-major array encoding. -/
noncomputable def matrixDomain (scalar : EncodedDomain.{0, 0} Empty) : EncodedDomain (Fin 3) :=
  (scalar.constant.arrayOfLength StandardMatrixEntry.length).reindex
    (fun sizes => Matrix (Fin (sizes 1)) (Fin (sizes 2)) (scalar.Carrier Empty.elim))
    (fun sizes => matrixEquiv sizes)

/-- Public matrix arguments are mathematical matrices. Private workspace
values retain their existing domains and their exact same physical encodings. -/
noncomputable def mathematicalDomains (scalar : EncodedDomain.{0, 0} Empty) (name : TapeName) : EncodedDomain (Fin 3) :=
  if name = inputTape ∨ name = dataTape 5 then matrixDomain scalar else domains scalar name

noncomputable def mathematicalEquivalence (scalar : EncodedDomain.{0, 0} Empty) (name : TapeName) (sizes : Fin 3 → ℕ) :
    (mathematicalDomains scalar name).Carrier sizes ≃ (domains scalar name).Carrier sizes := by
  by_cases isInput : name = inputTape
  · subst name
    exact matrixEquiv sizes
  · by_cases isOutput : name = dataTape 5
    · subst name
      exact matrixEquiv sizes
    · simp only [mathematicalDomains, show ¬ (name = inputTape ∨ name = dataTape 5) by tauto, ↓reduceIte]
      exact Equiv.refl _

private theorem mathematical_widths (scalar : EncodedDomain.{0, 0} Empty) (name : TapeName) (sizes : Fin 3 → ℕ) :
    (mathematicalDomains scalar name).width sizes = (domains scalar name).width sizes := by
  fin_cases name <;> rfl

private theorem mathematical_encoding (scalar : EncodedDomain.{0, 0} Empty) (name : TapeName) (sizes : Fin 3 → ℕ)
    (value : (mathematicalDomains scalar name).Carrier sizes) :
    encoded (mathematicalDomains scalar name) sizes value =
      encoded (domains scalar name) sizes (mathematicalEquivalence scalar name sizes value) := by
  fin_cases name <;> rfl

/-- The same finite machine computes the ordinary pointwise row transform on
mathematical matrices. Reindexing does not add transitions or change the tape
convention or the shape hypotheses; private scratch has no validity obligation. -/
theorem mathematical_contract (writeSource : Bool) (scalar : EncodedDomain.{0, 0} Empty)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    CallingConvention.Realizes (mathematicalDomains scalar) readOnly sizeTapes outputTapes (machine writeSource scalar operation)
      (entry (scalar.width Empty.elim)) (exit (scalar.width Empty.elim))
      (fun sizes input => (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1 ∧
        sizes 2 < 2 ^ sizes 0 ∧ sizes 1 * sizes 2 ≤ 2 ^ sizes 0)
      (fun sizes input output => ∃
        (sourceValid : (input ⟨dataTape 0, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1)
        (targetValid : (input ⟨dataTape 1, rfl⟩ : Fin (2 ^ sizes 0)).val < sizes 1),
        output () = MatrixRows.transform writeSource (operation Empty.elim)
          (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩)
          ⟨(input ⟨dataTape 0, rfl⟩).val, sourceValid⟩ ⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩) := by
  refine CallingConvention.realizes_reindex (mathematicalEquivalence scalar)
    (mathematical_widths scalar) (mathematical_encoding scalar) readOnly sizeTapes outputTapes
    (machine writeSource scalar operation) (entry (scalar.width Empty.elim)) (exit (scalar.width Empty.elim))
    _ _ _ _ ?_ ?_ (contract writeSource scalar operation)
  · intro sizes input valid
    exact valid
  · intro sizes input output correct
    obtain ⟨sourceValid, targetValid, correct⟩ := correct
    refine ⟨sourceValid, targetValid, ?_⟩
    have computed := processed_eq_matrix writeSource scalar operation sizes
      (input ⟨dataTape 0, rfl⟩) (input ⟨dataTape 1, rfl⟩) sourceValid targetValid
      (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩) (sizes 2) (le_refl _)
    have complete := MatrixRows.processedColumns_complete writeSource (operation Empty.elim)
      (input ⟨dataTape 3, rfl⟩) (input ⟨inputTape, rfl⟩)
      (⟨(input ⟨dataTape 0, rfl⟩).val, sourceValid⟩ : Fin (sizes 1))
      (⟨(input ⟨dataTape 1, rfl⟩).val, targetValid⟩ : Fin (sizes 1))
    have flatResult := correct.trans (computed.trans (congrArg (matrixEquiv sizes) complete))
    change (matrixEquiv (Carrier := scalar.Carrier Empty.elim) sizes).symm (output ()) = _
    simpa only [Equiv.symm_apply_apply] using
      congrArg (matrixEquiv (Carrier := scalar.Carrier Empty.elim) sizes).symm flatResult

/-- Public coordinates have the dimension as their bound. Their codec uses the
private controller width, so no runtime conversion of the binary digits is needed. -/
noncomputable def coordinateDomain (dimension : Fin 2) : EncodedDomain (Fin 2) :=
  EncodedDomain.boundedIndexOfWidth (fun sizes => sizes dimension)
    (Computation.Realizable.Internal.internalBound (MvPolynomial.X 0)) (by
      intro sizes
      rw [Computation.Realizable.Internal.internalBound_eval]
      simp only [MvPolynomial.eval_X, Computation.Realizable.Internal.internalSizes,
        Matrix.cons_val_zero]
      have fits := Computation.Realizable.Internal.internalCapacity_fits sizes
      fin_cases dimension
      · exact fits.1.le
      · exact fits.2.1.le)

/-- The same digits are also a valid internal binary counter. -/
noncomputable def coordinateValue (dimension : Fin 2) (sizes : Fin 2 → ℕ)
    (index : (coordinateDomain dimension).Carrier sizes) :
    ((EncodedDomain.binaryNaturals (0 : Fin 3)).withInternalSize).Carrier sizes :=
  ⟨index.val, by
    have fits := Computation.Realizable.Internal.internalCapacity_fits sizes
    apply index.isLt.trans_le
    fin_cases dimension
    · exact fits.1.le
    · exact fits.2.1.le⟩

theorem coordinate_bits (dimension : Fin 2) (sizes : Fin 2 → ℕ)
    (index : (coordinateDomain dimension).Carrier sizes) :
    EncodedDomain.ArrayEncoding.bits ((coordinateDomain dimension).encode sizes index) =
      EncodedDomain.ArrayEncoding.bits
        (((EncodedDomain.binaryNaturals (0 : Fin 3)).withInternalSize).encode sizes
          (coordinateValue dimension sizes index)) := by
  simp only [coordinateDomain, EncodedDomain.boundedIndexOfWidth,
    EncodedDomain.withInternalSize, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
    EncodedDomain.ArrayEncoding.bits_cast, BitVec.ofNatLT_eq_ofNat]
  rw [Computation.Realizable.Internal.internalBound_eval]
  simp only [coordinateValue, BitVec.ofFin_eq_ofNat]
  rw [MvPolynomial.eval_X]

end Polytime2.StandardMatrixRows
