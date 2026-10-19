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

import Polytime2.GaussJordan.ColumnFound

/-! # Preparing both outcomes of a Gauss–Jordan column

The result initially represents the original matrix, and the separate next-row
output initially represents the unchanged pivot. The no-pivot branch returns these values without preparing unused scratch.
-/

namespace Polytime2.StandardGaussJordanColumn

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

noncomputable def prepareNextRow : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy pivotTape nextRowTape (by decide)

noncomputable def prepareMatrix : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy originalTape resultTape (by decide)

abbrev InitializationState := Sum (Fin 3) (Fin 3)

noncomputable def initialization : Machine Alphabet InitializationState :=
  MultiTape.sequence prepareNextRow prepareMatrix 0

def initializationEntry : InitializationState := .inl 0
def initializationExit : InitializationState := .inr 2

@[simp] theorem initialization_halt (symbols : Symbols Alphabet) :
    initialization initializationExit symbols = none := rfl

/-- Initialize the result matrix and next-row output from arbitrary old contents.
The selected branch initializes its own workspace when it is called. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivotRow : Fin (2 ^ sizes 0))
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow →
      initial originalTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly
          initialization ticks
          (initializationEntry) (fun _ => 0) initial
          (initializationExit) (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow := by
  let matrixBound := (matrixDomain (FieldRow.scalarDomain enumeration)).widthPolynomial
  refine ⟨2 * matrixBound + 2 * MvPolynomial.X 0 + 5, ?_⟩
  intro sizes initial pivotRow matrix pivotEq matrixEq headers regions
  have nextTrace := StandardTapeCommands.copy_encoded_runs (EncodedDomain.binaryNaturals 0)
    sizes pivotRow pivotTape nextRowTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl
    initial pivotEq (regions nextRowTape)
  simp only [EncodedDomain.binaryNaturals_width] at nextTrace
  let afterNext := Function.update initial nextRowTape (encoded (EncodedDomain.binaryNaturals 0) sizes pivotRow)
  have afterNextRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (afterNext name) :=
    fun name => nextTrace.region name (regions name)
  have originalEq : afterNext originalTape =
      encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    (Function.update_of_ne (by decide) _ _).trans matrixEq
  have matrixTrace := StandardTapeCommands.copy_encoded_runs (matrixDomain (FieldRow.scalarDomain enumeration))
    sizes matrix originalTape resultTape (by decide)
    (fun name => (domains enumeration name).width sizes) readOnly rfl rfl rfl
    afterNext originalEq (afterNextRegions resultTape)
  have complete := nextTrace.sequence prepareMatrix 0 (by intro symbols; rfl) matrixTrace
  refine ⟨(2 * sizes 0 + 2) + (2 * (matrixDomain (FieldRow.scalarDomain enumeration)).width sizes + 2) + 1,
    Function.update afterNext resultTape (encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix),
    ?_, ?_, Function.update_self _ _ _, ?_⟩
  · simp only [matrixBound, EncodedDomain.width, map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
    omega
  · exact complete
  · exact (Function.update_of_ne (by decide) _ _).trans (Function.update_self _ _ _)

abbrev AlgorithmState (scalarWidth : ℕ) :=
  Sum (InitializationState)
    (Sum (StandardPivotSearch.AlgorithmState scalarWidth) (SelectState scalarWidth))

noncomputable instance algorithmStateFinite (scalarWidth : ℕ) :
    Fintype (AlgorithmState scalarWidth) := by
  letI : Fintype (StandardPivotSearch.AlgorithmState scalarWidth) := inferInstance
  letI : Fintype (SelectState scalarWidth) := inferInstance
  dsimp only [AlgorithmState]
  infer_instance

noncomputable def algorithm (enumeration : Scalar ≃ Fin cardinality) :
    let scalar := FieldRow.scalarDomain enumeration
    Machine Alphabet (AlgorithmState (scalar.width Empty.elim)) :=
  let scalar := FieldRow.scalarDomain enumeration
  MultiTape.sequence initialization
    (MultiTape.sequence (search enumeration) (select enumeration)
      (selectEntry (scalar.width Empty.elim)))
    (.inl (StandardPivotSearch.algorithmEntry
      (scalar.width Empty.elim)))

def algorithmEntry (scalarWidth : ℕ) : AlgorithmState scalarWidth :=
  .inl (initializationEntry)

def algorithmExit (scalarWidth : ℕ) : AlgorithmState scalarWidth :=
  .inr (.inr (selectExit scalarWidth))

@[simp] theorem algorithm_halt (enumeration : Scalar ≃ Fin cardinality) (symbols : Symbols Alphabet) :
    let scalar := FieldRow.scalarDomain enumeration
    algorithm enumeration (algorithmExit (scalar.width Empty.elim)) symbols = none := by
  simp [algorithm, algorithmExit, MultiTape.sequence, select_halt]

/-- Each private search tape has exactly one physical place in the column
workspace; proof fields in the subtype do not change that place. -/
theorem searchWiring_scratch (name : SearchScratch) :
    searchWiring name.val = .inr (.inl name) := by
  rcases name with ⟨name, writable, notCandidate⟩
  fin_cases name <;> solve | rfl | cases writable | exact False.elim (notCandidate rfl)

/-- Search only writes its private tapes and the candidate field. Every other
pivot-workspace tape retains its initialized value, including the matrix result. -/
theorem search_preserves_pivot (initial final : Tapes Alphabet)
    (outside : ∀ name, name ∉ Set.range searchWiring → final name = initial name)
    (immutable : ∀ name, StandardPivotSearch.readOnly name = true →
      final (searchWiring name) = initial (searchWiring name))
    (name : StandardGaussJordanPivot.TapeName)
    (notCandidate : name ≠ StandardGaussJordanPivot.candidateTape) :
    final (.inl name) = initial (.inl name) := by
  apply preserved_of_wiring searchWiring StandardPivotSearch.readOnly initial final outside immutable
  intro localName equal
  fin_cases localName <;> solve
    | rfl
    | cases equal
    | exact False.elim (notCandidate (Sum.inl.inj equal).symm)

end Polytime2.StandardGaussJordanColumn

