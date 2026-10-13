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

import Polytime2.StandardMatrixRowStep
import Polytime2.Pipeline

/-! # Consecutive row steps reuse their working matrix and counter -/

namespace Polytime2.Examples.MatrixRowSteps

open MultiTape CallingConvention StandardMatrixRowStep

private abbrev scalar := EncodedDomain.booleans (Parameter := Empty)
private abbrev sizes : Fin 3 → ℕ := ![2, 1, 2]
private noncomputable abbrev arrayDomain := scalar.constant.arrayOfLength StandardMatrixEntry.length
private abbrev operation (_assignment : Empty → ℕ) (_coefficient source target : Bool) := (source, !target)

private theorem array_length : MvPolynomial.eval sizes StandardMatrixEntry.length = 2 := by
  norm_num [StandardMatrixEntry.length, sizes]

private noncomputable def zeroIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
  ⟨0, by rw [array_length]; decide⟩

private noncomputable def oneIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
  ⟨1, by rw [array_length]; decide⟩

private noncomputable def initial : Tapes Alphabet
  | .inl (.inl parameter) => unary (sizes parameter)
  | .inl (.inr name) =>
    if name = 0 ∨ name = 1 ∨ name = 2 then
      encoded (EncodedDomain.binaryNaturals (0 : Fin 3)) sizes (0 : Fin 4)
    else if name = 3 then encoded scalar Empty.elim false
    else if name = 4 then encoded arrayDomain sizes (fun _ => false)
    else buffer (List.replicate ((domains scalar (.inl (.inr name))).width sizes) 2)
  | .inr () => buffer (List.replicate (sizes 0) 2)

private theorem initial_regions (name : TapeName) :
    Region ((domains scalar name).width sizes) 0 (initial name) := by
  cases name with
  | inl name =>
    cases name with
    | inl parameter =>
      rw [show initial (.inl (.inl parameter)) =
        encoded (EncodedDomain.unary parameter) sizes PUnit.unit by simp only [initial, encoded_unary]]
      exact encoded_region _ _ _
    | inr name =>
      fin_cases name <;> norm_num [initial, Fin.ext_iff]
      all_goals first
        | exact encoded_region _ _ _
        | simpa only [List.length_replicate] using buffer_region
            (List.replicate ((domains scalar _).width sizes) 2)
  | inr name =>
    cases name
    change Region (sizes 0) 0 (buffer (List.replicate (sizes 0) 2))
    simpa only [initial, List.length_replicate] using buffer_region (List.replicate (sizes 0) 2)

/-- The second call consumes the matrix and counter produced by the first;
no host-side tape preparation occurs between calls. Invalid scratch symbols
are overwritten, and all heads return to zero after both calls. -/
theorem two_columns :
    ∃ firstTicks secondTicks middle final,
      Runs (fun name => (domains scalar name).width sizes) readOnly
        (machine false scalar operation) firstTicks (entry 1) (fun _ => 0) initial (exit 1) (fun _ => 0) middle ∧
      Runs (fun name => (domains scalar name).width sizes) readOnly
        (machine false scalar operation) secondTicks (entry 1) (fun _ => 0) middle (exit 1) (fun _ => 0) final ∧
      final (.inl (.inr 4)) = encoded arrayDomain sizes (fun _ => true) ∧
      final (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes (2 : Fin 4) := by
  obtain ⟨bound, execute⟩ := runs false scalar operation
  obtain ⟨firstTicks, middle, firstCost, firstTrace, firstMatrix, firstResult, firstColumn, firstCanonical⟩ :=
    execute sizes initial 0 0 0 (fun _ => false) false
      (by norm_num [array_length]) (by norm_num [array_length])
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by intro parameter; rfl) initial_regions
  let firstArray : arrayDomain.Carrier sizes := Function.update (fun _ => false) zeroIndex true
  have firstMatrixEq : middle (.inl (.inr 4)) = encoded arrayDomain sizes firstArray := by
    change middle (.inl (.inr 4)) = encoded arrayDomain sizes
      (Function.update (Function.update (fun _ => false) zeroIndex false) zeroIndex true) at firstMatrix
    exact firstMatrix.trans (congrArg (encoded arrayDomain sizes) (Function.update_idem _ _ _))
  have firstColumnEq : middle (.inl (.inr 2)) = encoded (EncodedDomain.binaryNaturals 0) sizes (1 : Fin 4) := firstColumn
  obtain ⟨secondTicks, final, secondCost, secondTrace, finalMatrix, finalResult, finalColumn, finalCanonical⟩ :=
    execute sizes middle 0 0 1 firstArray false
      (by norm_num [array_length]) (by norm_num [array_length])
      (by decide) (by decide) (by decide) (by decide) (by decide)
      ((firstTrace.readOnly_tape (.inl (.inr 0)) rfl).trans (by rfl))
      ((firstTrace.readOnly_tape (.inl (.inr 1)) rfl).trans (by rfl)) firstColumnEq
      ((firstTrace.readOnly_tape (.inl (.inr 3)) rfl).trans (by rfl)) firstMatrixEq
      (fun parameter => (firstTrace.readOnly_tape (.inl (.inl parameter)) rfl).trans (by rfl))
      (fun name => firstTrace.region name (initial_regions name))
  refine ⟨firstTicks, secondTicks, middle, final, firstTrace, secondTrace, ?_, finalColumn⟩
  have allTrue : Function.update firstArray oneIndex true = fun _ => true := by
    funext index
    have bound : index.val < 2 := by simpa only [array_length] using index.isLt
    have cases : index = zeroIndex ∨ index = oneIndex := by
      rcases (show index.val = 0 ∨ index.val = 1 by omega) with zero | one
      · exact Or.inl (Fin.ext zero)
      · exact Or.inr (Fin.ext one)
    rcases cases with rfl | rfl
    · have different : zeroIndex ≠ oneIndex := by
        intro equal
        have impossible : (0 : ℕ) = 1 := congrArg Fin.val equal
        contradiction
      exact (Function.update_of_ne different true firstArray).trans (Function.update_self _ _ _)
    · exact Function.update_self _ _ _
  have firstAtOne : firstArray oneIndex = false := by
    apply Function.update_of_ne
    intro equal
    have impossible : (1 : ℕ) = 0 := congrArg Fin.val equal
    contradiction
  change final (.inl (.inr 4)) = encoded arrayDomain sizes
    (Function.update (Function.update firstArray oneIndex (firstArray oneIndex)) oneIndex (!(firstArray oneIndex))) at finalMatrix
  have updated : Function.update (Function.update firstArray oneIndex (firstArray oneIndex))
      oneIndex (!(firstArray oneIndex)) = fun _ => true := by
    rw [Function.update_eq_self, firstAtOne]
    exact allTrue
  exact finalMatrix.trans (congrArg (encoded arrayDomain sizes) updated)

/-- The same two calls form one finite controller whose handovers also obey
the standard tape contract. The generic pipeline hides the state injections. -/
theorem pipeline_two_columns :
    ∃ ticks final,
      Runs (fun name => (domains scalar name).width sizes) readOnly
        (Pipeline.machine (fun _ : Fin 2 => machine false scalar operation) (fun _ => entry 1)) ticks
        (Pipeline.position (fun _ : Fin 2 => entry 1) 0) (fun _ => 0) initial none (fun _ => 0) final ∧
      final (.inl (.inr 4)) = encoded arrayDomain sizes (fun _ => true) := by
  obtain ⟨firstTicks, secondTicks, middle, final, firstTrace, secondTrace, matrixEq, columnEq⟩ := two_columns
  let representation : Fin 3 → Tapes Alphabet → Prop := fun stage tapes =>
    match stage.val with | 0 => tapes = initial | 1 => tapes = middle | _ => tapes = final
  obtain ⟨ticks, result, cost, trace, resultEq⟩ := Pipeline.runs
    (fun name => (domains scalar name).width sizes) readOnly
    (fun _ : Fin 2 => machine false scalar operation) (fun _ => entry 1) (fun _ => exit 1)
    representation (firstTicks + secondTicks)
    (by intro stage symbols; exact halt false scalar operation symbols)
    (by
      intro stage tapes valid
      fin_cases stage
      · change tapes = initial at valid
        subst tapes
        exact ⟨firstTicks, middle, by omega, firstTrace, rfl⟩
      · change tapes = middle at valid
        subst tapes
        exact ⟨secondTicks, final, by omega, secondTrace, rfl⟩)
    initial rfl
  change result = final at resultEq
  subst result
  exact ⟨ticks, final, trace, matrixEq⟩

end Polytime2.Examples.MatrixRowSteps
