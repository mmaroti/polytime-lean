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

import Polytime2.StandardGaussJordanClearInitialization

/-! # Complete standard-convention pivot-column clearing -/

namespace Polytime2.StandardGaussJordanClear

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

instance tapeNamesFinite : Fintype TapeName := by
  letI : Fintype StandardMatrixRows.TapeName := inferInstance
  letI : Fintype StandardGaussJordanClearTarget.TapeName := inferInstance
  letI : Fintype StandardGaussJordanClearStep.TapeName := inferInstance
  letI : Fintype StandardGaussJordanClearInterval.TapeName := inferInstance
  infer_instance

abbrev AlgorithmState (initWidth scalarWidth : ℕ) :=
  Sum (InitializationState initWidth) (TraversalState scalarWidth)

instance algorithmStateFinite (initWidth scalarWidth : ℕ) : Fintype (AlgorithmState initWidth scalarWidth) := by
  letI : Fintype (InitializationState initWidth) := inferInstance
  letI : Fintype (TraversalState scalarWidth) := inferInstance
  dsimp only [AlgorithmState]
  infer_instance

def sizeTapes : Fin 3 ↪ TapeName := StandardMatrixRows.sizeTapes.trans rowsWiring

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (AlgorithmState (zeroBits enumeration).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) :=
  MultiTape.sequence (initialization enumeration) (traversal enumeration)
    (traversalEntry ((FieldRow.scalarDomain enumeration).width Empty.elim))

def algorithmEntry (initWidth scalarWidth : ℕ) : AlgorithmState initWidth scalarWidth :=
  .inl (initializationEntry initWidth)

def algorithmExit (initWidth scalarWidth : ℕ) : AlgorithmState initWidth scalarWidth :=
  .inr (traversalExit scalarWidth)

@[simp] theorem algorithm_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    algorithm enumeration (algorithmExit (zeroBits enumeration).length
      ((FieldRow.scalarDomain enumeration).width Empty.elim)) symbols = none := by
  simp [algorithm, algorithmExit, MultiTape.sequence, traversal_halt]

/-- Initialization and both guarded intervals form one routine. Writable
regions can contain arbitrary symbols, and all return valid encoded values. -/
theorem runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot column : Fin (2 ^ sizes 0))
      (pivotValid : pivot.val < sizes 1) (columnValid : column.val < sizes 2)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar)
      (_rowsFit : sizes 1 < 2 ^ sizes 0),
      sizes 2 < 2 ^ sizes 0 → sizes 1 * sizes 2 ≤ 2 ^ sizes 0 →
      initial (dataTape 0) = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes column →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          (algorithm enumeration) ticks
          (algorithmEntry (zeroBits enumeration).length ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) initial
          (algorithmExit (zeroBits enumeration).length ((FieldRow.scalarDomain enumeration).width Empty.elim))
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes
          (MatrixOperations.clearColumn (Scalar := Scalar) matrix
            ⟨pivot.val, pivotValid⟩ ⟨column.val, columnValid⟩) ∧
        (∀ name, readOnly name = false → ∃ value : (domains enumeration name).Carrier sizes,
          final name = encoded (domains enumeration name) sizes value) := by
  obtain ⟨initBound, executeInit⟩ := initialization_runs enumeration
  obtain ⟨traversalBound, executeTraversal⟩ := traversal_runs enumeration
  refine ⟨initBound + traversalBound + 1, ?_⟩
  intro sizes initial pivot column pivotValid columnValid matrix rowsFit columnsFit capacity
    pivotEq columnEq matrixEq headers regions
  change initial originalTape = encoded (domains enumeration originalTape) sizes
    (matrixEquiv (Carrier := Scalar) sizes matrix) at matrixEq
  obtain ⟨initTicks, initialized, initCost, initTrace, workEq, targetEq, limitEq, canonical⟩ :=
    executeInit sizes initial pivot (matrixEquiv sizes matrix) pivotEq matrixEq headers regions
  change initialized workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix at workEq
  obtain ⟨traversalTicks, final, traversalCost, traversalTrace, resultEq, finalCounter, finalCanonical⟩ :=
    executeTraversal sizes initialized pivot column pivotValid columnValid matrix rowsFit columnsFit capacity
      ((initTrace.readOnly_tape (dataTape 0) rfl).trans pivotEq) targetEq
      ((initTrace.readOnly_tape columnTape rfl).trans columnEq) workEq limitEq
      (fun parameter => (initTrace.readOnly_tape (sizeTape parameter) rfl).trans (headers parameter))
      (fun name => initTrace.region name (regions name)) canonical
  have complete := initTrace.sequence (traversal enumeration)
    (traversalEntry ((FieldRow.scalarDomain enumeration).width Empty.elim))
    (initialization_halt enumeration) traversalTrace
  refine ⟨initTicks + traversalTicks + 1, final, ?_, ?_, resultEq, finalCanonical⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [algorithm, algorithmEntry, algorithmExit] using complete

end Polytime2.StandardGaussJordanClear
