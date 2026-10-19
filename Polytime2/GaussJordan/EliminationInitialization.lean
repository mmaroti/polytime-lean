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

import Polytime2.GaussJordan.EliminationInitCalls

/-! # Complete initialization from arbitrary writable contents -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} {cardinality : ℕ}

abbrev InitializationState := Sum (Pipeline.State SeedStageState) StandardSizeRead.State

noncomputable def initialization :
    Machine Alphabet InitializationState :=
  MultiTape.sequence seed readColumns StandardSizeRead.entry

def initializationEntry : InitializationState := .inl (Pipeline.position seedEntry 0)
def initializationExit : InitializationState := .inr StandardSizeRead.exit

@[simp] theorem initialization_halt (symbols : Symbols Alphabet) :
    initialization initializationExit symbols = none := rfl

/-- Startup initializes only the live matrix and counters and reads the column
limit. Private scratch may contain arbitrary symbols, including blanks. -/
theorem initialization_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar) (columnsFit : sizes 2 < 2 ^ sizes 0),
      initial inputTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly initialization ticks
          initializationEntry
          (fun _ => 0) initial
          initializationExit
          (fun _ => 0) final ∧
        final workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨0, by positivity⟩ : Fin (2 ^ sizes 0)) ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes
          (⟨sizes 2, columnsFit⟩ : Fin (2 ^ sizes 0)) := by
  obtain ⟨seedBound, executeSeed⟩ := seed_runs enumeration
  obtain ⟨readBound, executeRead⟩ := readColumns_runs enumeration
  refine ⟨seedBound + readBound + 1, ?_⟩
  intro sizes initial matrix columnsFit matrixEq headers regions
  let zero : Fin (2 ^ sizes 0) := ⟨0, by positivity⟩
  have sizeReadOnly (parameter : Fin 3) : readOnly (sizeTape parameter) = true := by
    fin_cases parameter <;> decide
  obtain ⟨seedTicks, seeded, seedCost, seedTrace, seedOutputs⟩ :=
    executeSeed sizes initial matrix matrixEq (headers 0) regions
  have seedMatrix : seeded workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix :=
    seedOutputs 0
  have seedPivot : seeded pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero := seedOutputs 1
  have seedColumn : seeded columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes zero := seedOutputs 2
  have seededRegions : ∀ name, Region ((domains enumeration name).width sizes) 0 (seeded name) :=
    fun name => seedTrace.region name (regions name)
  obtain ⟨readTicks, final, readCost, readTrace, limitEq, difference, readOutside⟩ :=
    executeRead sizes seeded columnsFit
      (fun parameter => (seedTrace.readOnly_tape (sizeTape parameter) (sizeReadOnly parameter)).trans
        (headers parameter))
      (by simpa only [show (domains enumeration limitTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using seededRegions limitTape) (by simpa only [show (domains enumeration differenceTape).width sizes = sizes 0 from EncodedDomain.binaryNaturals_width 0 sizes] using seededRegions differenceTape)
  have complete := seedTrace.sequence readColumns StandardSizeRead.entry (by intro symbols; rfl) readTrace
  refine ⟨seedTicks + readTicks + 1, final, ?_, ?_,
    (readOutside workingTape (by decide) (by decide)).trans seedMatrix,
    (readOutside pivotTape (by decide) (by decide)).trans seedPivot,
    (readOutside columnTape (by decide) (by decide)).trans seedColumn, limitEq⟩
  · simp only [map_add, map_one]
    omega
  · simpa only [initialization, initializationEntry, initializationExit] using complete

end Polytime2.StandardGaussJordanElimination
