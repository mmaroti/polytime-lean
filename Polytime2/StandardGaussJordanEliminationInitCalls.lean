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

import Polytime2.StandardGaussJordanEliminationSeed

/-! # Workspace preparation and unary column-limit reading -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

noncomputable def prepareWorkspace (enumeration : Scalar ≃ Fin cardinality) :
    Machine Alphabet (StandardGaussJordanColumn.WorkspaceState
      (StandardGaussJordanClear.zeroBits enumeration).length
      (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length) :=
  MultiTape.wire columnWiring (StandardGaussJordanColumn.workspace enumeration)

theorem prepareWorkspace_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (pivot : Fin (2 ^ sizes 0)) (matrix : Matrix (Fin (sizes 1)) (Fin (sizes 2)) Scalar),
      initial pivotTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot →
      initial workingTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix →
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      (∀ name, Region ((domains enumeration name).width sizes) 0 (initial name)) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly (prepareWorkspace enumeration) ticks
          (StandardGaussJordanColumn.workspaceEntry (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) initial
          (StandardGaussJordanColumn.workspaceExit (StandardGaussJordanClear.zeroBits enumeration).length
            (StandardPivotSearch.defaultBits (FieldRow.scalarDomain enumeration) (0 : Scalar)).length)
          (fun _ => 0) final ∧
        final resultTape = encoded (matrixDomain (FieldRow.scalarDomain enumeration)) sizes matrix ∧
        final nextRowTape = encoded (EncodedDomain.binaryNaturals 0) sizes pivot ∧
        (∀ name, StandardGaussJordanColumn.readOnly name = false →
          ∃ value : (domains enumeration (.inl name)).Carrier sizes,
            final (.inl name) = encoded (domains enumeration (.inl name)) sizes value) ∧
        (∀ name, name ∉ Set.range columnWiring → final name = initial name) ∧
        (∀ name, StandardGaussJordanColumn.readOnly name = true →
          final (columnWiring name) = initial (columnWiring name)) := by
  obtain ⟨bound, execute⟩ := StandardGaussJordanColumn.workspace_runs enumeration
  refine ⟨bound, ?_⟩
  intro sizes initial pivot matrix pivotEq matrixEq headers regions
  obtain ⟨ticks, localFinal, cost, localTrace, resultEq, nextEq, canonical⟩ :=
    execute sizes (fun name => initial (.inl name)) pivot matrix pivotEq matrixEq headers
      (fun name => regions (.inl name))
  have trace := localTrace.wire columnWiring
    (fun name => (domains enumeration name).width sizes) readOnly (fun _ => rfl)
    (by
      intro name premise
      change (if name = StandardGaussJordanColumn.pivotTape ∨
        name = StandardGaussJordanColumn.columnTape ∨
        name = StandardGaussJordanColumn.originalTape then false
        else StandardGaussJordanColumn.readOnly name) = true at premise
      split_ifs at premise
      exact premise)
    initial (fun _ => 0)
  have start : install columnWiring (fun name => initial (.inl name)) initial = initial :=
    install_self columnWiring initial
  have positions : install columnWiring (fun _ : StandardGaussJordanColumn.TapeName => (0 : ℤ))
      (fun _ : TapeName => (0 : ℤ)) = fun _ => 0 := install_self columnWiring _
  rw [start, positions] at trace
  refine ⟨ticks, install columnWiring localFinal initial, cost, trace,
    (install_at columnWiring localFinal initial _).trans resultEq,
    (install_at columnWiring localFinal initial _).trans nextEq, ?_, ?_, ?_⟩
  · intro name writable
    obtain ⟨value, valueEq⟩ := canonical name writable
    exact ⟨value, (install_at columnWiring localFinal initial name).trans valueEq⟩
  · intro name outside
    exact install_outside columnWiring localFinal initial name outside
  · intro name immutable
    exact (install_at columnWiring localFinal initial name).trans (localTrace.readOnly_tape name immutable)

def columnLimitWiring : Sum Bool Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl false => sizeTape 2 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => differenceTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

noncomputable def readColumns : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire columnLimitWiring StandardSizeRead.algorithm

@[simp] theorem readColumns_halt (symbols : Symbols Alphabet) :
    readColumns StandardSizeRead.exit symbols = none := rfl

omit [Field Scalar] in
theorem readColumns_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (fits : sizes 2 < 2 ^ sizes 0),
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial limitTape) → Region (sizes 0) 0 (initial differenceTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly readColumns ticks
          StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ limitTape → name ≠ differenceTape → final name = initial name) := by
  obtain ⟨bound, execute⟩ := StandardSizeRead.contract.wired_runs columnLimitWiring
  let parameter : Bool → Fin 3 := fun name => if name then 0 else 2
  refine ⟨MvPolynomial.rename parameter bound, ?_⟩
  intro sizes initial fits headers limitRegion scratchRegion
  let localSizes : Bool → ℕ := fun name => sizes (parameter name)
  let input : Inputs StandardSizeRead.domains StandardSizeRead.argumentReadOnly localSizes := fun name => by
    rcases name with ⟨name, readonly⟩
    cases name with
    | inl name => exact PUnit.unit
    | inr name => contradiction
  obtain ⟨ticks, output, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute localSizes input (fun name => (domains enumeration name).width sizes) readOnly initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      fits
      (by
        intro name readonly
        cases name with
        | inl name =>
          change initial (columnLimitWiring (.inl name)) = encoded (EncodedDomain.unary name) localSizes PUnit.unit
          rw [encoded_unary]
          cases name <;> exact headers _
        | inr name => contradiction)
      (by intro name writable; fin_cases name <;> first | contradiction | exact limitRegion | exact scratchRegion)
      (by intro name; cases name <;> exact headers _)
  refine ⟨ticks, final, ?_, trace, ?_, ?_, ?_⟩
  · simpa only [MvPolynomial.eval_rename, Function.comp_def, localSizes] using cost
  · have valueEq : output ⟨.inr false, rfl⟩ = (⟨sizes 2, fits⟩ : Fin (2 ^ sizes 0)) := Fin.ext correct
    have result := canonical (.inr false) rfl
    rw [valueEq] at result
    exact result
  · exact ⟨output ⟨.inr true, rfl⟩, canonical (.inr true) rfl⟩
  · intro name notLimit notDifference
    apply preserved_of_wiring columnLimitWiring StandardSizeRead.argumentReadOnly initial final outside immutable
    intro localName equal
    cases localName with
    | inl parameter => rfl
    | inr name => cases name with
      | false => exact False.elim (notLimit equal.symm)
      | true => exact False.elim (notDifference equal.symm)

end Polytime2.StandardGaussJordanElimination
