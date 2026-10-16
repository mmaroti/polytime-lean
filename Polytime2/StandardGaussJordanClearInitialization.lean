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

import Polytime2.StandardGaussJordanClearInit

/-! # Complete arbitrary-content initialization for column clearing -/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

abbrev InitializationState (width : ℕ) := Sum (Sum (Copy.State width) (Fin 3))
  (Sum (Pipeline.State StandardMatrixRows.InitStageState) (Pipeline.State FinishStageState))

instance initializationStateFinite (width : ℕ) : Fintype (InitializationState width) := by
  letI : Fintype (Pipeline.State StandardMatrixRows.InitStageState) := inferInstance
  letI : Fintype (Pipeline.State FinishStageState) := inferInstance
  dsimp only [InitializationState]
  infer_instance

noncomputable def initialization (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (InitializationState (zeroBits enumeration).length) :=
  MultiTape.sequence (seed enumeration)
    (MultiTape.sequence rowWorkspace finishInitialization (Pipeline.position finishEntry 0))
    (.inl (Pipeline.position StandardMatrixRows.initEntry 0))

def initializationEntry (width : ℕ) : InitializationState width := .inl (seedEntry width)
def initializationExit (width : ℕ) : InitializationState width := .inr (.inr none)

@[simp] theorem initialization_halt (enumeration : Scalar ≃ Fin cardinality)
    (symbols : Symbols Alphabet) :
    initialization enumeration (initializationExit (zeroBits enumeration).length) symbols = none := rfl

/-- Every writable tape becomes a valid encoded value before either interval
is called. No externally prepared output or scratch is required. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot : Fin (2 ^ sizes 0))
      (matrix : ((FieldRow.scalarDomain enumeration).constant.arrayOfLength
        StandardMatrixEntry.length).Carrier sizes),
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial originalTape = encoded (domains enumeration originalTape) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (initialization enumeration) ticks (initializationEntry (zeroBits enumeration).length)
          (fun _ => 0) initial (initializationExit (zeroBits enumeration).length) (fun _ => 0) final ∧
        final workingTape = encoded (domains enumeration workingTape) sizes matrix ∧
        final (dataTape 1) = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨seedBound, executeSeed⟩ := seed_runs enumeration
  let matrixBound := ((FieldRow.scalarDomain enumeration).constant.arrayOfLength StandardMatrixEntry.length).widthPolynomial
  refine ⟨seedBound + 19 * (2 * matrixBound +
    MvPolynomial.C (2 * (FieldRow.scalarDomain enumeration).width Empty.elim) + 2 * MvPolynomial.X 0 + 3) +
    5 * (2 * MvPolynomial.X 0 + 3) + 2, ?_⟩
  intro sizes initial pivot matrix pivotEq matrixEq headers regions
  obtain ⟨seedTicks, seeded, seedCost, seedTrace, workEq, zeroEq, seedOutside⟩ :=
    executeSeed sizes initial matrix matrixEq regions
  have seededRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (seeded name) :=
    fun name => seedTrace.region name (regions name)
  obtain ⟨rowTicks, prepared, rowCost, rowTrace, preparedMatrix, preparedZero, rowCanonical, rowOutside⟩ :=
    rowWorkspace_runs enumeration sizes matrix seeded workEq zeroEq
      ((seedTrace.readOnly_tape (sizeTape 0) rfl).trans (headers 0)) seededRegions
  obtain ⟨finishTicks, final, finishCost, finishTrace, finishValues, finishPreserved⟩ :=
    finishInitialization_runs enumeration sizes pivot prepared
      ((rowTrace.readOnly_tape (dataTape 0) rfl).trans
        ((seedTrace.readOnly_tape (dataTape 0) rfl).trans pivotEq))
      ((rowTrace.readOnly_tape (sizeTape 0) rfl).trans
        ((seedTrace.readOnly_tape (sizeTape 0) rfl).trans (headers 0)))
      (fun name => rowTrace.region name (seededRegions name))
  have finalMatrix : final workingTape = encoded (domains enumeration workingTape) sizes matrix :=
    (finishPreserved workingTape (by decide)).trans preparedMatrix
  have finalZero : final (dataTape 3) = encoded (FieldRow.scalarDomain enumeration) Empty.elim (0 : Scalar) :=
    (finishPreserved (dataTape 3) (by decide)).trans preparedZero
  have tail := rowTrace.sequence finishInitialization (Pipeline.position finishEntry 0)
    rowWorkspace_halt finishTrace
  have complete := seedTrace.sequence _ (Sum.inl (Pipeline.position StandardMatrixRows.initEntry 0))
    (seed_halt enumeration) tail
  refine ⟨seedTicks + (rowTicks + finishTicks + 1) + 1, final, ?_, ?_, finalMatrix,
    finishValues 0, finishValues 4, ?_⟩
  · simp only [EncodedDomain.width] at rowCost
    simp only [matrixBound, EncodedDomain.width, map_add, map_mul, map_ofNat, MvPolynomial.eval_C, MvPolynomial.eval_X]
    omega
  · simpa only [initialization, initializationEntry, initializationExit] using complete
  · intro name writable
    by_cases isTarget : name = dataTape 1
    · subst name
      exact ⟨⟨0, by positivity⟩, finishValues 0⟩
    · by_cases isNext : name = nextTape
      · subst name
        exact ⟨⟨0, by positivity⟩, finishValues 1⟩
      · by_cases isDifference : name = differenceTape
        · subst name
          exact ⟨⟨0, by positivity⟩, finishValues 2⟩
        · by_cases isGuard : name = guardTape
          · subst name
            exact ⟨false, finishValues 3⟩
          · by_cases isLimit : name = limitTape
            · subst name
              exact ⟨pivot, finishValues 4⟩
            · by_cases isMatrix : name = workingTape
              · subst name
                exact ⟨matrix, finalMatrix⟩
              · by_cases isScalar : name = dataTape 3
                · subst name
                  exact ⟨(0 : Scalar), finalZero.trans
                    (encoded_constant (FieldRow.scalarDomain enumeration) sizes _).symm⟩
                · have preserved : final name = prepared name := finishPreserved name (by
                    simp only [finishReadOnly, isTarget, isNext, isDifference, isGuard, isLimit,
                      or_self, ↓reduceIte])
                  cases name with
                  | inr extra => contradiction
                  | inl name => cases name with
                    | inr slot =>
                      fin_cases slot <;> first
                        | exact False.elim (isLimit rfl)
                        | exact False.elim (isDifference rfl)
                        | exact False.elim (isGuard rfl)
                    | inl name => cases name with
                      | inr extra => exact False.elim (isNext rfl)
                      | inl name => cases name with
                        | inr extra => contradiction
                        | inl name =>
                          have localWritable : StandardMatrixRows.readOnly name = false := by
                            fin_cases name <;> first
                              | rfl
                              | contradiction
                          obtain ⟨value, encodedValue⟩ := rowCanonical name localWritable
                          exact ⟨value, preserved.trans encodedValue⟩

end Polytime2.StandardGaussJordanClear

