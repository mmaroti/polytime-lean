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

import Polytime2.Matrices.HermiteWorkspace
import Polytime2.Arrays.FoldContract
import Polytime2.Computation.Equality

/-! # Certified guarded updates for a Hermite column fold

The immutable context is a source row and selected column. The accumulator is
the current matrix and its left basis. A token equal to the source leaves the
state unchanged; every other token invokes the fixed-workspace Hermite step.
Its logical width precondition is supplied by the enclosing fold invariant.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def hermiteColumnContext (rows columns : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => boundedIndex rows
  | true => boundedIndex columns

noncomputable def hermiteColumnState (rows columns workspace : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (integerMatrices rows columns workspace).prod (integerMatrices rows rows workspace)

private def updateArguments (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :
    (integerHermiteRowStep rows columns workspace).Arguments sizes
  | 0 => context false | 1 => token | 2 => context true | 3 => state.1 | 4 => state.2

/-- Only a genuine update needs the logical narrowing precondition. -/
def hermiteColumnUpdateAllowed (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :=
  token ≠ context false → (integerHermiteRowStepWithin rows columns columnWidth workspace).precondition sizes
    (updateArguments rows columns workspace sizes context state token)

/-- A total mathematical update, certified under its logical fold precondition. -/
noncomputable def hermiteColumnUpdate (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes) :
    (hermiteColumnState rows columns workspace).Carrier sizes := by
  classical
  exact if token = context false then state
    else if valid : (integerHermiteRowStepWithin rows columns columnWidth workspace).precondition sizes
        (updateArguments rows columns workspace sizes context state token) then
      (integerHermiteRowStepWithin rows columns columnWidth workspace).compute sizes
        ⟨updateArguments rows columns workspace sizes context state token, valid⟩ else state

theorem hermiteColumnUpdate_realizable (rows columns columnWidth workspace : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (hermiteColumnContext rows columns) (boundedIndex rows) (hermiteColumnState rows columns workspace)
      (hermiteColumnUpdateAllowed rows columns columnWidth workspace)
      (hermiteColumnUpdate rows columns columnWidth workspace)).Realizable := by
  classical
  let computation := arrayFoldStep (hermiteColumnContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns workspace) (hermiteColumnUpdateAllowed rows columns columnWidth workspace)
    (hermiteColumnUpdate rows columns columnWidth workspace)
  let condition (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) :=
    decide (arguments (.inr true) = arguments (.inl false))
  have guard := (elementsEqual_realizable (boundedIndex rows)).onResults computation.inputDomains computation.precondition
    (fun choice _ arguments => if choice then arguments.val (.inl false) else arguments.val (.inr true))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains (.inr true) computation.precondition
      · exact Realizable.argument computation.inputDomains (.inl false) computation.precondition)
  apply Realizable.ofCases condition guard
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have copied := Realizable.argument computation.inputDomains (.inr false) allowed
    apply copied.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have same : arguments (.inr true) = arguments (.inl false) := of_decide_eq_true valid.2
    simp only [computation, arrayFoldStep, hermiteColumnUpdate, ite_eq_left same]
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have updated := (integerHermiteRowStepWithin_realizable rows columns columnWidth workspace).onResults
      computation.inputDomains allowed (fun name sizes arguments => updateArguments rows columns workspace sizes
        (fun original => arguments.val (.inl original)) (arguments.val (.inr false)) (arguments.val (.inr true)) name)
      (by intro sizes arguments; exact arguments.property.1 (of_decide_eq_false arguments.property.2)) (by
        intro name
        fin_cases name
        · exact Realizable.argument computation.inputDomains (.inl false) allowed
        · exact Realizable.argument computation.inputDomains (.inr true) allowed
        · exact Realizable.argument computation.inputDomains (.inl true) allowed
        · exact ((pairProjection_realizable (integerMatrices rows columns workspace) (integerMatrices rows rows workspace) false).withArguments
            computation.inputDomains (MultiTape.oneTape (.inr false)) (by intros; rfl)).withPrecondition allowed (by intros; trivial)
        · exact ((pairProjection_realizable (integerMatrices rows columns workspace) (integerMatrices rows rows workspace) true).withArguments
            computation.inputDomains (MultiTape.oneTape (.inr false)) (by intros; rfl)).withPrecondition allowed (by intros; trivial))
    apply updated.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have different : arguments (.inr true) ≠ arguments (.inl false) := of_decide_eq_false valid.2
    have permitted := valid.1 different
    simp only [computation, arrayFoldStep, Computation.onResults,
      hermiteColumnUpdate, ite_eq_right different, dite_eq_left permitted]

/-- Every permitted nonsource update is exactly the mathematical Hermite step. -/
theorem hermiteColumnUpdate_correct (rows columns columnWidth workspace : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (boundedIndex rows).Carrier sizes)
    (different : token ≠ context false) (valid : hermiteColumnUpdateAllowed rows columns columnWidth workspace sizes context state token) :
    let result := hermiteColumnUpdate rows columns columnWidth workspace sizes context state token
    (result.1.val, result.2.val) = IntegerMatrix.hermiteRowStep
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (context false) token (context true) state.1.val state.2.val := by
  simp only [hermiteColumnUpdate, ite_eq_right different, dite_eq_left (valid different)]
  exact integerHermiteRowStepWithin_correct rows columns columnWidth workspace sizes
    ⟨updateArguments rows columns workspace sizes context state token, valid different⟩

end Polytime2.Computation.Realizable.Internal
