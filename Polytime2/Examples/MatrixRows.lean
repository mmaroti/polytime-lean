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

import Polytime2.StandardMatrixRowsContract

/-! # Complete row traversal with arbitrary initial writable contents -/

namespace Polytime2.Examples.MatrixRows

open MultiTape CallingConvention StandardMatrixRows

private def input (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (value : scalar.Carrier Empty.elim) : Inputs (domains scalar) readOnly sizes := fun name => by
  rcases name with ⟨name, readonly⟩
  cases name with
  | inl name => cases name with
    | inl name => cases name with
      | inl parameter => exact PUnit.unit
      | inr name =>
        by_cases source : name = 0
        · subst name; exact ⟨0, by positivity⟩
        · by_cases target : name = 1
          · subst name; exact ⟨0, by positivity⟩
          · have accepted : name = 0 ∨ name = 1 ∨ name = 3 := of_decide_eq_true readonly
            have coefficient : name = 3 := accepted.resolve_left source |>.resolve_left target
            subst name
            exact value
    | inr name => contradiction
  | inr name =>
    have original : name = 3 := of_decide_eq_true readonly
    subst name
    exact fun _ => value

private noncomputable def initial (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (value : scalar.Carrier Empty.elim) : Tapes Alphabet := fun name =>
  if readonly : readOnly name = true then encoded (domains scalar name) sizes (input scalar sizes value ⟨name, readonly⟩)
  else buffer (List.replicate ((domains scalar name).width sizes) 2)

private theorem initial_entry (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (value : scalar.Carrier Empty.elim) :
    Entry (domains scalar) readOnly sizes (input scalar sizes value) (initial scalar sizes value) := by
  refine ⟨?_, ?_⟩
  · intro name readonly
    simp only [initial, dite_eq_left readonly]
  · intro name writable
    have notReadonly : ¬ readOnly name = true := by rw [writable]; decide
    exact ⟨List.replicate ((domains scalar name).width sizes) 2, List.length_replicate,
      by simp only [initial, dite_eq_right notReadonly]⟩

private theorem initial_header (scalar : EncodedDomain.{0, 0} Empty) (sizes : Fin 3 → ℕ)
    (value : scalar.Carrier Empty.elim) (parameter : Fin 3) :
    initial scalar sizes value (sizeTape parameter) = unary (sizes parameter) := by
  have represented := (initial_entry scalar sizes value).1 (sizeTape parameter) rfl
  change initial scalar sizes value (sizeTape parameter) = encoded (EncodedDomain.unary parameter) sizes PUnit.unit at represented
  exact represented.trans (encoded_unary parameter sizes)

/-- A zero-column matrix still initializes every scalar and Boolean scratch
word. Binary words and matrices have zero width, and all heads are restored. -/
theorem empty_columns (scalar : EncodedDomain.{0, 0} Empty) (value : scalar.Carrier Empty.elim)
    (operation : ∀ assignment, scalar.Carrier assignment → scalar.Carrier assignment →
      scalar.Carrier assignment → scalar.Carrier assignment × scalar.Carrier assignment) :
    ∃ ticks final,
      Runs (fun name => (domains scalar name).width ![0, 1, 0]) readOnly (machine true scalar operation) ticks
        (entry (scalar.width Empty.elim)) (fun _ => 0) (initial scalar ![0, 1, 0] value)
        (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
      final (dataTape 5) = encoded (scalar.constant.arrayOfLength StandardMatrixEntry.length) ![0, 1, 0] (fun _ => value) ∧
      (∀ name, readOnly name = false → ∃ result : (domains scalar name).Carrier ![0, 1, 0],
        final name = encoded (domains scalar name) ![0, 1, 0] result) := by
  obtain ⟨bound, execute⟩ := runs true scalar operation
  have represented := initial_entry scalar ![0, 1, 0] value
  obtain ⟨ticks, final, cost, trace, matrixEq, canonical⟩ :=
    execute ![0, 1, 0] (initial scalar ![0, 1, 0] value) 0 0 (by decide) (by decide) value (fun _ => value)
      (by decide) (by decide)
      (represented.1 (dataTape 0) rfl) (represented.1 (dataTape 1) rfl)
      ((represented.1 (dataTape 3) rfl).trans (encoded_constant scalar ![0, 1, 0] _)) (represented.1 inputTape rfl)
      (initial_header scalar ![0, 1, 0] value) represented.region
  exact ⟨ticks, final, trace, matrixEq, canonical⟩

private noncomputable abbrev scalar := EncodedDomain.booleans (Parameter := Empty)
private abbrev sizes : Fin 3 → ℕ := ![2, 1, 2]
private noncomputable abbrev arrayDomain := scalar.constant.arrayOfLength StandardMatrixEntry.length
private abbrev operation (_assignment : Empty → ℕ) (_coefficient source target : Bool) := (source, !target)

private theorem array_length : MvPolynomial.eval sizes StandardMatrixEntry.length = 2 := by
  norm_num [StandardMatrixEntry.length, sizes]

private noncomputable def zeroIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
  ⟨0, by rw [array_length]; decide⟩

private noncomputable def oneIndex : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length) :=
  ⟨1, by rw [array_length]; decide⟩

private theorem processed_two (sourceValid targetValid : (0 : Fin 4).val < sizes 1) :
    processed false scalar operation sizes 0 0 sourceValid targetValid false (fun _ => false) 2 = fun _ => true := by
  let firstArray : arrayDomain.Carrier sizes := Function.update (fun _ => false) zeroIndex true
  have first : processed false scalar operation sizes 0 0 sourceValid targetValid false (fun _ => false) 1 = firstArray := by
    erw [processed.eq_def]
    change (if _ : (0 : ℕ) < 2 then
      Function.update (Function.update (fun _ => false) zeroIndex false) zeroIndex true else _) = firstArray
    erw [dite_eq_left (by decide)]
    exact Function.update_idem _ _ _
  have second : processed false scalar operation sizes 0 0 sourceValid targetValid false (fun _ => false) 2 =
      Function.update firstArray oneIndex (!(firstArray oneIndex)) := by
    erw [processed.eq_def]
    let prior : arrayDomain.Carrier sizes :=
      processed false scalar operation sizes 0 0 sourceValid targetValid false (fun _ => false) 1
    have priorEq : prior = firstArray := first
    change (if _ : (1 : ℕ) < 2 then
      Function.update (Function.update prior oneIndex (prior oneIndex)) oneIndex (!(prior oneIndex)) else prior) = _
    erw [dite_eq_left (by decide), priorEq, Function.update_eq_self]
  have different : oneIndex ≠ zeroIndex := by
    intro equal
    have impossible : (1 : ℕ) = 0 := congrArg Fin.val equal
    contradiction
  have firstAtOne : firstArray oneIndex = false := Function.update_of_ne different _ _
  erw [second, firstAtOne]
  funext index
  have bound : index.val < 2 := by simpa only [array_length] using index.isLt
  have alternatives : index = zeroIndex ∨ index = oneIndex := by
    rcases (show index.val = 0 ∨ index.val = 1 by omega) with zero | one
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext one)
  rcases alternatives with rfl | rfl
  · exact (Function.update_of_ne (Ne.symm different) _ _).trans (Function.update_self _ _ _)
  · exact Function.update_self _ _ _

/-- The complete controller visits both columns, changes each original false
entry to true, and stops with the column counter equal to two. All writable
tapes begin with arbitrary contents; initialization is part of the machine. -/
theorem two_columns :
    ∃ ticks final,
      Runs (fun name => (domains scalar name).width sizes) readOnly (machine false scalar operation) ticks
        (entry (scalar.width Empty.elim)) (fun _ => 0) (initial scalar sizes false) (exit (scalar.width Empty.elim)) (fun _ => 0) final ∧
      final (dataTape 5) = encoded arrayDomain sizes (fun _ => true) := by
  obtain ⟨bound, execute⟩ := runs false scalar operation
  have represented := initial_entry scalar sizes false
  obtain ⟨ticks, final, cost, trace, matrixEq, canonical⟩ :=
    execute sizes (initial scalar sizes false) 0 0 (by decide) (by decide) false (fun _ => false)
      (by decide) (by decide)
      (represented.1 (dataTape 0) rfl) (represented.1 (dataTape 1) rfl)
      ((represented.1 (dataTape 3) rfl).trans (encoded_constant scalar sizes _)) (represented.1 inputTape rfl)
      (initial_header scalar sizes false) represented.region
  refine ⟨ticks, final, trace, ?_⟩
  exact matrixEq.trans (congrArg (encoded arrayDomain sizes) (processed_two _ _))

/-- Nonempty traversal also works when each scalar and the whole matrix have
zero bits. Unary dimensions and binary counters still control both iterations. -/
theorem zero_width_columns :
    let domain := EncodedDomain.fixed (Parameter := Empty) (Equiv.refl (Fin 1))
    let combine := fun (_assignment : Empty → ℕ) (_coefficient source target : Fin 1) => (source, target)
    ∃ ticks final,
      Runs (fun name => (domains domain name).width sizes) readOnly (machine true domain combine) ticks
        (entry (domain.width Empty.elim)) (fun _ => 0) (initial domain sizes (0 : Fin 1)) (exit (domain.width Empty.elim)) (fun _ => 0) final ∧
      final (dataTape 5) = encoded (domain.constant.arrayOfLength StandardMatrixEntry.length) sizes (fun _ => (0 : Fin 1)) := by
  intro domain combine
  obtain ⟨bound, execute⟩ := runs true domain combine
  have represented := initial_entry domain sizes (0 : Fin 1)
  obtain ⟨ticks, final, cost, trace, matrixEq, canonical⟩ :=
    execute sizes (initial domain sizes (0 : Fin 1)) 0 0 (by decide) (by decide) (0 : Fin 1) (fun _ => (0 : Fin 1))
      (by decide) (by decide)
      (represented.1 (dataTape 0) rfl) (represented.1 (dataTape 1) rfl)
      ((represented.1 (dataTape 3) rfl).trans (encoded_constant domain sizes _)) (represented.1 inputTape rfl)
      (initial_header domain sizes (0 : Fin 1)) represented.region
  have unchanged : processed true domain combine sizes 0 0 (by decide) (by decide) (0 : Fin 1)
      (fun _ => (0 : Fin 1)) (sizes 2) = fun _ => (0 : Fin 1) := by
    funext index
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  exact ⟨ticks, final, trace,
    matrixEq.trans (congrArg (encoded (domain.constant.arrayOfLength StandardMatrixEntry.length) sizes) unchanged)⟩

end Polytime2.Examples.MatrixRows
