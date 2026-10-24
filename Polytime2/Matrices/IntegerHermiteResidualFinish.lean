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

import Polytime2.Matrices.IntegerHermiteExtendPivot
import Polytime2.Matrices.IntegerResidualPivot
import Polytime2.Arrays.SearchCoordinates

/-! # Completing insertion after incoming-row clearing

Given a residual row and distinct old rows excluding it, return an optional new
pivot and both actual matrices. A zero residual retains the matrices; otherwise
extend at the returned nonzero column. Both branches share a derived width.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width length : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter
  | 0 => boundedIndex rows
  | 1 => integerMatrices rows columns width
  | 2 => integerMatrices rows rows width
  | 3 => (boundedIndex rows).arrayOfLength length

private def allowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :=
  (List.ofFn (arguments 3)).Nodup ∧ arguments 0 ∉ List.ofFn (arguments 3)

private noncomputable def residual (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :
    Option (Fin (MvPolynomial.eval sizes columns)) :=
  (integerResidualPivot rows columns width).compute sizes
    ⟨(fun choice => match choice with | false => arguments 0 | true => arguments 1), trivial⟩

private theorem residual_realizable (rows columns width length : MvPolynomial Parameter ℕ)
    (admissible : ∀ sizes, (∀ name, (inputs rows columns width length name).Carrier sizes) → Prop) :
    (Computation.mk (inputs rows columns width length) (arraySearchResult columns) admissible
      (fun sizes arguments => residual rows columns width length sizes arguments.val)).Realizable := by
  exact (integerResidualPivot_realizable rows columns width).onArguments (inputs rows columns width length) admissible
    (fun choice => match choice with | false => 0 | true => 1) (by intro choice; cases choice <;> rfl) (by intros; trivial)

private def extensionArguments (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes)
    (column : Fin (MvPolynomial.eval sizes columns)) : (integerHermiteExtendPivot rows columns width length).Arguments sizes
  | 0 => arguments 0 | 1 => column | 2 => arguments 1 | 3 => arguments 2 | 4 => arguments 3

private theorem extension_valid (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes)
    (valid : allowed rows columns width length sizes arguments) (column : Fin (MvPolynomial.eval sizes columns))
    (found : residual rows columns width length sizes arguments = some column) :
    (integerHermiteExtendPivot rows columns width length).precondition sizes
      (extensionArguments rows columns width length sizes arguments column) := by
  refine ⟨valid.1, valid.2, ?_⟩
  exact integerResidualPivot_nonzero rows columns width sizes
    ⟨(fun choice => match choice with | false => arguments 0 | true => arguments 1), trivial⟩ column found

private noncomputable def widened (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width length name).Carrier sizes) :
    (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes :=
  ((integerMatrixWiden rows columns width (width + 1) (2 * width + 1) (by ring)).compute sizes
      ⟨(fun _ => arguments 1), trivial⟩,
    (integerMatrixWiden rows rows width (width + 1) (2 * width + 1) (by ring)).compute sizes
      ⟨(fun _ => arguments 2), trivial⟩)

/-- Complete a residual-row insertion, keeping the optional mathematical pivot. -/
noncomputable def integerHermiteResidualFinish (rows columns width length : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) where
  inputDomains := inputs rows columns width length
  outputDomain := (hermiteColumnState rows columns (2 * width + 1)).prod (arraySearchResult columns)
  precondition := allowed rows columns width length
  compute sizes arguments :=
    match found : residual rows columns width length sizes arguments.val with
    | none => (widened rows columns width length sizes arguments.val, none)
    | some column => ((integerHermiteExtendPivot rows columns width length).compute sizes
        ⟨extensionArguments rows columns width length sizes arguments.val column,
          extension_valid rows columns width length sizes arguments.val arguments.property column found⟩, some column)

/-- The runtime branch retains matrices for a zero residual and extends only at a found nonzero pivot. -/
theorem integerHermiteResidualFinish_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (integerHermiteResidualFinish rows columns width length).Realizable := by
  let computation := integerHermiteResidualFinish rows columns width length
  let condition sizes (arguments : computation.Arguments sizes) :=
    (residual rows columns width length sizes arguments).isNone
  have guard := (residual_realizable rows columns width length computation.precondition).followedBy
    (arraySearchIsNone_realizable columns) rfl (by intros; trivial)
  apply Realizable.ofCases condition guard
  · let admissible sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have first := ((integerMatrixWiden_realizable rows columns width (width + 1) (2 * width + 1) (by ring)).withArguments
      computation.inputDomains (MultiTape.oneTape 1) (by intros; rfl)).withPrecondition admissible (by intros; trivial)
    have second := ((integerMatrixWiden_realizable rows rows width (width + 1) (2 * width + 1) (by ring)).withArguments
      computation.inputDomains (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition admissible (by intros; trivial)
    have matrices := first.prodMk second
    have complete := matrices.prodMk (residual_realizable rows columns width length admissible)
    apply complete.withSpecification admissible _ (by intros; assumption)
    intro sizes arguments valid
    change (widened rows columns width length sizes arguments,
      residual rows columns width length sizes arguments) = _
    dsimp only [computation, integerHermiteResidualFinish]
    split
    · rename_i found
      rw [found]
    · rename_i column found
      have impossible := valid.2
      change (residual rows columns width length sizes arguments).isNone = true at impossible
      simp only [found, Option.isNone_some, Bool.false_eq_true] at impossible
  · let admissible sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have present sizes (arguments : {arguments : computation.Arguments sizes // admissible sizes arguments}) :
        (residual rows columns width length sizes arguments.val).isSome := by
      cases found : residual rows columns width length sizes arguments.val with
      | none => have impossible := arguments.property.2; simp only [condition, found, Option.isNone_none, Bool.true_eq_false] at impossible
      | some column => rfl
    have extracted := (residual_realizable rows columns width length admissible).followedBy
      (arraySearchFound_realizable columns) rfl (by intro sizes arguments valid; exact present sizes ⟨arguments, valid⟩)
    let selected sizes (arguments : {arguments : computation.Arguments sizes // admissible sizes arguments}) :=
      (residual rows columns width length sizes arguments.val).get (present sizes arguments)
    have extended := (integerHermiteExtendPivot_realizable rows columns width length).onResults
      computation.inputDomains admissible
      (fun name sizes arguments => extensionArguments rows columns width length sizes arguments.val (selected sizes arguments) name)
      (by
        intro sizes arguments
        exact extension_valid rows columns width length sizes arguments.val arguments.property.1 (selected sizes arguments)
          (Option.some_get (present sizes arguments)).symm) (by
        intro name
        fin_cases name
        · exact Realizable.argument computation.inputDomains 0 admissible
        · exact extracted
        · exact Realizable.argument computation.inputDomains 1 admissible
        · exact Realizable.argument computation.inputDomains 2 admissible
        · exact Realizable.argument computation.inputDomains 3 admissible)
    have complete := extended.prodMk (residual_realizable rows columns width length admissible)
    apply complete.withSpecification admissible _ (by intros; assumption)
    intro sizes arguments valid
    dsimp only [computation, integerHermiteResidualFinish]
    split
    · rename_i found
      have impossible := valid.2
      change (residual rows columns width length sizes arguments).isNone = false at impossible
      simp only [found, Option.isNone_none, Bool.true_eq_false] at impossible
    · rename_i column found
      have selectedEquation : selected sizes ⟨arguments, valid⟩ = column := by
        dsimp only [selected]
        exact Option.some.inj ((Option.some_get (present sizes ⟨arguments, valid⟩)).trans found)
      apply Prod.ext
      · apply congrArg ((integerHermiteExtendPivot rows columns width length).compute sizes)
        apply Subtype.ext
        funext name
        exact congrArg (fun index => extensionArguments rows columns width length sizes arguments index name) selectedEquation
      · exact found

/-- The returned pivot is exactly the mathematical residual search result. -/
theorem integerHermiteResidualFinish_pivot (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteResidualFinish rows columns width length).Arguments sizes //
      (integerHermiteResidualFinish rows columns width length).precondition sizes arguments}) :
    ((integerHermiteResidualFinish rows columns width length).compute sizes arguments).2 =
      IntegerMatrix.hermiteResidualPivot (arguments.val 0) (arguments.val 1).val := by
  have search := integerResidualPivot_correct rows columns width sizes
    ⟨(fun choice => match choice with | false => arguments.val 0 | true => arguments.val 1), trivial⟩
  dsimp only [integerHermiteResidualFinish]
  split
  · rename_i found
    exact found.symm.trans search
  · rename_i column found
    exact found.symm.trans search

/-- With embedded old rows, the result is exactly copy-or-extend at the mathematical residual pivot. -/
theorem integerHermiteResidualFinish_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteResidualFinish rows columns width length).Arguments sizes //
      (integerHermiteResidualFinish rows columns width length).precondition sizes arguments})
    (activeRows : Fin (MvPolynomial.eval sizes length) ↪ Fin (MvPolynomial.eval sizes rows))
    (selected : arguments.val 3 = (fun index => activeRows index)) :
    let result := (integerHermiteResidualFinish rows columns width length).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) =
      match IntegerMatrix.hermiteResidualPivot (arguments.val 0) (arguments.val 1).val with
      | none => (((arguments.val 1).val, (arguments.val 2).val), none)
      | some column => (IntegerMatrix.hermiteExtendPivot activeRows (arguments.val 0) column
          (arguments.val 1).val (arguments.val 2).val, some column) := by
  let value (choice : Option (Fin (MvPolynomial.eval sizes columns))) := match choice with
    | none => (((arguments.val 1).val, (arguments.val 2).val), none)
    | some column => (IntegerMatrix.hermiteExtendPivot activeRows (arguments.val 0) column
        (arguments.val 1).val (arguments.val 2).val, some column)
  have search := integerResidualPivot_correct rows columns width sizes
    ⟨(fun choice => match choice with | false => arguments.val 0 | true => arguments.val 1), trivial⟩
  apply Eq.trans (b := value (residual rows columns width length sizes arguments.val))
  · dsimp only [integerHermiteResidualFinish]
    split
    · rename_i found
      exact (congrArg value found).symm
    · rename_i column found
      apply Eq.trans (b := value (some column))
      · exact Prod.ext (integerHermiteExtendPivot_embedding rows columns width length sizes
          ⟨extensionArguments rows columns width length sizes arguments.val column,
            extension_valid rows columns width length sizes arguments.val arguments.property column found⟩ activeRows selected) rfl
      · exact (congrArg value found).symm
  · exact congrArg value search

/-- Both residual outcomes preserve the actual presentation and unimodular left basis. -/
theorem integerHermiteResidualFinish_preserves (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteResidualFinish rows columns width length).Arguments sizes //
      (integerHermiteResidualFinish rows columns width length).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 2).val * original * right = (arguments.val 1).val)
    (unit : IsUnit (arguments.val 2).val.det) :
    let result := (integerHermiteResidualFinish rows columns width length).compute sizes arguments
    result.1.2.val * original * right = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  let activeRows : Fin (MvPolynomial.eval sizes length) ↪ Fin (MvPolynomial.eval sizes rows) :=
    ⟨arguments.val 3, List.nodup_ofFn.mp arguments.property.1⟩
  have excluded : arguments.val 0 ∉ Set.range activeRows := by
    rintro ⟨index, same⟩
    exact arguments.property.2 (List.mem_ofFn.mpr ⟨index, same⟩)
  have actual := integerHermiteResidualFinish_correct rows columns width length sizes arguments activeRows rfl
  have transfer := congrArg (fun state => state.1.2 * original * right = state.1.1 ∧ IsUnit state.1.2.det) actual
  apply transfer.mpr
  split
  · exact ⟨equation, unit⟩
  · exact IntegerMatrix.hermiteExtendPivot_preserves activeRows (arguments.val 0) _ excluded
      (arguments.val 1).val original (arguments.val 2).val right equation unit

end Polytime2.Computation
