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

import Polytime2.Matrices.HermiteAlternatingAdvance
import Polytime2.Arrays.FoldContract
import Polytime2.Arrays.Indices

/-! # Bounded fixed-workspace alternating Hermite controller

Fold the certified forward update for the prescribed mathematical pair budget.
The immutable original matrix determines the exact prefix invariant; entries
and accumulated bases retain fixed polynomial widths throughout the fold.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def context (dimension width : MvPolynomial Parameter ℕ) : Unit → EncodedDomain Parameter :=
  fun _ => integerMatrices dimension dimension width

private def values (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (hermiteAlternatingState dimension width budget).Carrier sizes) :=
  (state.1.val, state.2.1.val, state.2.2.val)

private noncomputable def update (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (_original : ∀ name, (context dimension width name).Carrier sizes)
    (state : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (_token : (arrayPosition budget).Carrier sizes) := by
  classical
  exact if valid : (integerHermiteAlternatingAdvance dimension width budget).precondition sizes (fun _ => state) then
    (integerHermiteAlternatingAdvance dimension width budget).compute sizes ⟨fun _ => state, valid⟩ else state

private def allowed (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (_original : ∀ name, (context dimension width name).Carrier sizes)
    (state : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (_token : (arrayPosition budget).Carrier sizes) : Prop :=
  (integerHermiteAlternatingAdvance dimension width budget).precondition sizes (fun _ => state)

private theorem update_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (context dimension width) (arrayPosition budget) (hermiteAlternatingState dimension width budget)
      (allowed dimension width budget) (update dimension width budget)).Realizable := by
  classical
  let step := arrayFoldStep (context dimension width) (arrayPosition budget) (hermiteAlternatingState dimension width budget)
    (allowed dimension width budget) (update dimension width budget)
  have ready := (integerHermiteAlternatingAdvance_realizable dimension width budget).onResults
    step.inputDomains step.precondition (fun _ _ arguments => arguments.val (.inr false))
    (by intro sizes arguments; exact arguments.property)
    (fun _ => Realizable.argument step.inputDomains (.inr false) step.precondition)
  apply ready.withSpecification step.precondition step.compute (by intros; assumption)
  intro sizes arguments valid
  have permitted : (integerHermiteAlternatingAdvance dimension width budget).precondition sizes
      (fun _ => arguments (.inr false)) := valid
  change _ = update dimension width budget sizes (fun name => arguments (.inl name))
    (arguments (.inr false)) (arguments (.inr true))
  rw [show update dimension width budget sizes (fun name => arguments (.inl name))
      (arguments (.inr false)) (arguments (.inr true)) =
      (integerHermiteAlternatingAdvance dimension width budget).compute sizes
        ⟨fun _ => arguments (.inr false), permitted⟩ from dite_eq_left permitted]
  rfl

private def admissible (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ name, (context dimension width name).Carrier sizes)
    (_tokens : ((arrayPosition budget).arrayOfLength budget).Carrier sizes)
    (initial : (hermiteAlternatingState dimension width budget).Carrier sizes) : Prop :=
  (original ()).val.IsLowerTriangular ∧ (∀ index, 0 < (original ()).val index index) ∧
    (original ()).val.det.natAbs < 2 ^ MvPolynomial.eval sizes width ∧
    values dimension width budget sizes initial = ((original ()).val, 1, 1)

private def invariant (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ name, (context dimension width name).Carrier sizes)
    (count : ℕ) (state : (hermiteAlternatingState dimension width budget).Carrier sizes) : Prop :=
  values dimension width budget sizes state = IntegerMatrix.hermiteAlternatingRun count (original ()).val

private theorem permits (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ name, (context dimension width name).Carrier sizes)
    (tokens : ((arrayPosition budget).arrayOfLength budget).Carrier sizes)
    (initial : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (valid : admissible dimension width budget sizes original tokens initial)
    (index : Fin (MvPolynomial.eval sizes budget)) (state : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (before : invariant dimension width budget sizes original index.val state) :
    allowed dimension width budget sizes original state (tokens index) :=
  integerHermiteAlternatingAdvance_permitted dimension width budget sizes (fun _ => state)
    (original ()) valid.1 valid.2.1 valid.2.2.1 index.val index.isLt before

private theorem preserves (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ name, (context dimension width name).Carrier sizes)
    (tokens : ((arrayPosition budget).arrayOfLength budget).Carrier sizes)
    (initial : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (valid : admissible dimension width budget sizes original tokens initial)
    (index : Fin (MvPolynomial.eval sizes budget)) (state : (hermiteAlternatingState dimension width budget).Carrier sizes)
    (before : invariant dimension width budget sizes original index.val state) :
    invariant dimension width budget sizes original (index.val + 1)
      (update dimension width budget sizes original state (tokens index)) := by
  classical
  have permitted : (integerHermiteAlternatingAdvance dimension width budget).precondition sizes (fun _ => state) :=
    permits dimension width budget sizes original tokens initial valid index state before
  dsimp only [invariant, update]
  rw [dite_eq_left permitted]
  have same := integerHermiteAlternatingAdvance_correct dimension width budget sizes ⟨fun _ => state, permitted⟩
  change values dimension width budget sizes _ = _ at same
  rw [same]
  change IntegerMatrix.hermiteAlternatingAdvance (values dimension width budget sizes state) = _
  change values dimension width budget sizes state = _ at before
  rw [before, IntegerMatrix.hermiteAlternatingRun_eq_iterate,
    IntegerMatrix.hermiteAlternatingRun_eq_iterate]
  exact (Function.iterate_succ_apply' _ _ _).symm

/-- Internal controller at a common entry/determinant width and fixed total-budget basis width. -/
noncomputable def hermiteAlternatingController (dimension width budget : MvPolynomial Parameter ℕ) :=
  arrayFold (context dimension width) (arrayPosition budget) (hermiteAlternatingState dimension width budget) budget
    (admissible dimension width budget) (update dimension width budget)

/-- The whole bounded fold reuses the certified forward step and its canonical prefix invariant. -/
theorem hermiteAlternatingController_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (hermiteAlternatingController dimension width budget).Realizable := by
  apply arrayFold_realizable (context dimension width) (arrayPosition budget) (hermiteAlternatingState dimension width budget) budget
    (admissible dimension width budget) (update dimension width budget) (allowed dimension width budget)
    (update_realizable dimension width budget)
    (fun sizes original _tokens _initial count state => invariant dimension width budget sizes original count state)
  · intro sizes original tokens initial valid
    exact valid.2.2.2
  · exact permits dimension width budget
  · exact preserves dimension width budget

/-- The complete fold is exactly the recursive run, including diagonal stopping and both bases. -/
theorem hermiteAlternatingController_correct (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteAlternatingController dimension width budget).Arguments sizes //
      (hermiteAlternatingController dimension width budget).precondition sizes arguments}) :
    let result := (hermiteAlternatingController dimension width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingRun (MvPolynomial.eval sizes budget) (arguments.val (.inl ())).val := by
  exact ArrayFold.prefix_invariant
    (update dimension width budget sizes (fun _ => arguments.val (.inl ())))
    (arguments.val (.inr true)) (arguments.val (.inr false))
    (invariant dimension width budget sizes (fun _ => arguments.val (.inl ())))
    arguments.property.2.2.2
    (fun index state before => preserves dimension width budget sizes (fun _ => arguments.val (.inl ()))
      (arguments.val (.inr true)) (arguments.val (.inr false)) arguments.property index state before)
    (MvPolynomial.eval sizes budget) (by rfl)

end Polytime2.Computation
