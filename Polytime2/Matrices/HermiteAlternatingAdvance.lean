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

import Polytime2.Matrices.HermiteAlternatingWorkspace
import Polytime2.Matrices.IntegerBasisCompose

/-! # Fixed-width forward accumulation for the alternating controller

The state contains the current matrix and both accumulated bases. A canonical
prefix of a bounded positive lower triangular input fits one workspace derived
from the total pair budget. Advancing it keeps a diagonal state unchanged or
composes one pair's actual bases in presentation order.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- One basis capacity for every prefix of the bounded alternating run. -/
noncomputable def hermiteAlternatingRunBasisWidth (dimension width budget : MvPolynomial Parameter ℕ) :=
  1 + budget * (hermiteAlternatingBasisWidth dimension width + dimension + 1)

/-- Ordinary current matrix and two bases, at fixed polynomial widths. -/
noncomputable def hermiteAlternatingState (dimension width budget : MvPolynomial Parameter ℕ) :=
  (integerMatrices dimension dimension width).prod
    ((integerMatrices dimension dimension (hermiteAlternatingRunBasisWidth dimension width budget)).prod
      (integerMatrices dimension dimension (hermiteAlternatingRunBasisWidth dimension width budget)))

private def stateValues (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (hermiteAlternatingState dimension width budget).Carrier sizes) :=
  (state.1.val, state.2.1.val, state.2.2.val)

private def allowed (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (hermiteAlternatingState dimension width budget).Carrier sizes) : Prop :=
  ∃ original : (integerMatrices dimension dimension width).Carrier sizes,
    original.val.IsLowerTriangular ∧ (∀ index, 0 < original.val index index) ∧
    original.val.det.natAbs < 2 ^ MvPolynomial.eval sizes width ∧
    ∃ count, count < MvPolynomial.eval sizes budget ∧
      stateValues dimension width budget sizes (arguments ()) = IntegerMatrix.hermiteAlternatingRun count original.val

private theorem nextFits (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : Unit → (hermiteAlternatingState dimension width budget).Carrier sizes //
      allowed dimension width budget sizes arguments}) :
    let result := IntegerMatrix.hermiteAlternatingAdvance (stateValues dimension width budget sizes (arguments.val ()))
    (∀ row column, (result.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, (result.2.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteAlternatingRunBasisWidth dimension width budget)) ∧
    (∀ row column, (result.2.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes (hermiteAlternatingRunBasisWidth dimension width budget)) := by
  obtain ⟨original, lower, positive, determinant, count, within, same⟩ := arguments.property
  have bounds := IntegerMatrix.hermiteAlternatingAdvance_prefix_bound (MvPolynomial.eval sizes width)
    (MvPolynomial.eval sizes budget) (count + 1) original.val lower positive original.property determinant within
  have prefixEqual : IntegerMatrix.hermiteAlternatingAdvance (stateValues dimension width budget sizes (arguments.val ())) =
      IntegerMatrix.hermiteAlternatingAdvance^[count + 1] (original.val, 1, 1) := by
    rw [same, IntegerMatrix.hermiteAlternatingRun_eq_iterate]
    exact (Function.iterate_succ_apply' _ _ _).symm
  dsimp only
  rw [prefixEqual]
  simpa [hermiteAlternatingRunBasisWidth, hermiteAlternatingBasisWidth,
    IntegerMatrix.hermiteSweepBasisIncrement] using bounds

namespace Realizable.Internal

/-- Advance one canonical prefix at the full run's fixed workspace. -/
noncomputable def integerHermiteAlternatingAdvance (dimension width budget : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := hermiteAlternatingState dimension width budget
  outputDomain := hermiteAlternatingState dimension width budget
  precondition := allowed dimension width budget
  compute sizes arguments :=
    let result := IntegerMatrix.hermiteAlternatingAdvance (stateValues dimension width budget sizes (arguments.val ()))
    (⟨result.1, (nextFits dimension width budget sizes arguments).1⟩,
      ⟨result.2.1, (nextFits dimension width budget sizes arguments).2.1⟩,
      ⟨result.2.2, (nextFits dimension width budget sizes arguments).2.2⟩)

/-- Any genuine prefix before the total budget permits the fixed-width update. -/
theorem integerHermiteAlternatingAdvance_permitted (dimension width budget : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerHermiteAlternatingAdvance dimension width budget).Arguments sizes)
    (original : (integerMatrices dimension dimension width).Carrier sizes)
    (lower : original.val.IsLowerTriangular) (positive : ∀ index, 0 < original.val index index)
    (determinant : original.val.det.natAbs < 2 ^ MvPolynomial.eval sizes width)
    (count : ℕ) (within : count < MvPolynomial.eval sizes budget)
    (same : ((arguments ()).1.val, (arguments ()).2.1.val, (arguments ()).2.2.val) =
      IntegerMatrix.hermiteAlternatingRun count original.val) :
    (integerHermiteAlternatingAdvance dimension width budget).precondition sizes arguments :=
  ⟨original, lower, positive, determinant, count, within, same⟩

/-- The fixed-width update is exactly mathematical forward accumulation. -/
theorem integerHermiteAlternatingAdvance_correct (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingAdvance dimension width budget).Arguments sizes //
      (integerHermiteAlternatingAdvance dimension width budget).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingAdvance dimension width budget).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingAdvance ((arguments.val ()).1.val, (arguments.val ()).2.1.val, (arguments.val ()).2.2.val) := rfl

private theorem currentPermitted (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteAlternatingAdvance dimension width budget).Arguments sizes)
    (valid : (integerHermiteAlternatingAdvance dimension width budget).precondition sizes arguments) :
    (integerHermiteAlternatingPair dimension width).precondition sizes (fun _ => (arguments ()).1) := by
  obtain ⟨original, lower, positive, determinant, count, within, same⟩ := valid
  have shape := IntegerMatrix.hermiteAlternatingRun_triangular count original.val lower positive
  have det := IntegerMatrix.hermiteAlternatingRun_det_natAbs count original.val
  rw [← same] at shape det
  exact ⟨shape.1, shape.2, det.trans_lt determinant⟩

private theorem activeFits (dimension width budget : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingAdvance dimension width budget).Arguments sizes //
      (integerHermiteAlternatingAdvance dimension width budget).precondition sizes arguments})
    (notDiagonal : ¬ ∀ row column, row ≠ column → (arguments.val ()).1.val row column = 0) :
    let pair := (integerHermiteAlternatingPair dimension width).compute sizes
      ⟨fun _ => (arguments.val ()).1, currentPermitted dimension width budget sizes arguments.val arguments.property⟩
    (∀ row column, (pair.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, ((pair.2.1.val * (arguments.val ()).2.1.val) row column).natAbs <
      2 ^ MvPolynomial.eval sizes (hermiteAlternatingRunBasisWidth dimension width budget)) ∧
    (∀ row column, (((arguments.val ()).2.2.val * pair.2.2.val) row column).natAbs <
      2 ^ MvPolynomial.eval sizes (hermiteAlternatingRunBasisWidth dimension width budget)) := by
  have bounds := nextFits dimension width budget sizes arguments
  dsimp only [IntegerMatrix.hermiteAlternatingAdvance, stateValues] at bounds
  rw [ite_eq_right notDiagonal] at bounds
  have same := integerHermiteAlternatingPair_correct dimension width sizes
    ⟨fun _ => (arguments.val ()).1, currentPermitted dimension width budget sizes arguments.val arguments.property⟩
  rw [← same] at bounds
  exact bounds

/-- Stop or compose one pair and resize both accumulated bases to the full budget width. -/
theorem integerHermiteAlternatingAdvance_realizable (dimension width budget : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingAdvance dimension width budget).Realizable := by
  classical
  let computation := integerHermiteAlternatingAdvance dimension width budget
  let matrix := integerMatrices dimension dimension width
  let stepWidth := hermiteAlternatingBasisWidth dimension width
  let basisWidth := hermiteAlternatingRunBasisWidth dimension width budget
  let basis := integerMatrices dimension dimension basisWidth
  let condition sizes (arguments : computation.Arguments sizes) :=
    (integerMatrixIsDiagonal dimension width).compute sizes ⟨fun _ => (arguments ()).1, trivial⟩
  have guard := ((pairProjection_realizable matrix (basis.prod basis) false).withPrecondition
    computation.precondition (by intros; trivial)).followedBy
    (integerMatrixIsDiagonal_realizable dimension width) rfl (by intros; trivial)
  apply Realizable.ofCases condition guard
  · let branch := computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
      (fun _ _ valid => valid.1)
    apply (Realizable.argument computation.inputDomains () branch.precondition).withSpecification
      branch.precondition branch.compute (by intros; assumption)
    intro sizes arguments valid
    have diagonal := (integerMatrixIsDiagonal_correct dimension width sizes (arguments ()).1).mp valid.2
    have equal : IntegerMatrix.hermiteAlternatingAdvance (stateValues dimension width budget sizes (arguments ())) =
        stateValues dimension width budget sizes (arguments ()) := ite_eq_left diagonal
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg Prod.fst equal).symm
    · apply Prod.ext
      · apply Subtype.ext
        exact (congrArg (fun result => result.2.1) equal).symm
      · apply Subtype.ext
        exact (congrArg (fun result => result.2.2) equal).symm
  · let branch := computation.withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = false)
      (fun _ _ valid => valid.1)
    have permitted sizes (arguments : {arguments : computation.Arguments sizes // branch.precondition sizes arguments}) :=
      currentPermitted dimension width budget sizes arguments.val arguments.property.1
    have pair := (integerHermiteAlternatingPair_realizable dimension width).onResults
      computation.inputDomains branch.precondition (fun _ _ arguments => (arguments.val ()).1)
      (by intro sizes arguments; exact permitted sizes arguments)
      (fun _ => (pairProjection_realizable matrix (basis.prod basis) false).withPrecondition _ (by intros; trivial))
    let step sizes (arguments : {arguments : computation.Arguments sizes // branch.precondition sizes arguments}) :=
      (integerHermiteAlternatingPair dimension width).compute sizes
        ⟨fun _ => (arguments.val ()).1, permitted sizes arguments⟩
    have pairMatrix := pair.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
    have pairBases := pair.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
    have stepLeft := pairBases.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)
    have stepRight := pairBases.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)
    have oldBases := (pairProjection_realizable matrix (basis.prod basis) true).withPrecondition branch.precondition (by intros; trivial)
    have oldLeft := oldBases.followedBy (pairProjection_realizable basis basis false) rfl (by intros; trivial)
    have oldRight := oldBases.followedBy (pairProjection_realizable basis basis true) rfl (by intros; trivial)
    have products := (integerBasisCompose_realizable dimension dimension basisWidth basisWidth stepWidth stepWidth).onResults
      computation.inputDomains branch.precondition
      (fun name sizes arguments => match name with
        | 0 => (arguments.val ()).2.1 | 1 => (arguments.val ()).2.2
        | 2 => (step sizes arguments).2.1 | 3 => (step sizes arguments).2.2)
      (by intros; trivial) (by
        intro name
        fin_cases name
        · exact oldLeft
        · exact oldRight
        · exact stepLeft
        · exact stepRight)
    have bounded sizes (arguments : {arguments : computation.Arguments sizes // branch.precondition sizes arguments}) :=
      activeFits dimension width budget sizes ⟨arguments.val, arguments.property.1⟩ (by
        intro diagonal
        have accepted := (integerMatrixIsDiagonal_correct dimension width sizes (arguments.val ()).1).mpr diagonal
        have rejected := arguments.property.2
        change (integerMatrixIsDiagonal dimension width).compute sizes ⟨fun _ => (arguments.val ()).1, trivial⟩ = false at rejected
        rw [accepted] at rejected
        contradiction)
    have left := (products.followedBy (pairProjection_realizable _ _ false) rfl (by intros; trivial)).followedBy
      (integerMatrixResize_realizable dimension dimension (dimension + stepWidth + basisWidth) basisWidth) rfl
      (by intro sizes arguments valid; exact (bounded sizes ⟨arguments, valid⟩).2.1)
    have right := (products.followedBy (pairProjection_realizable _ _ true) rfl (by intros; trivial)).followedBy
      (integerMatrixResize_realizable dimension dimension (dimension + basisWidth + stepWidth) basisWidth) rfl
      (by intro sizes arguments valid; exact (bounded sizes ⟨arguments, valid⟩).2.2)
    have bases := Realizable.pairOutputs computation.inputDomains _ _ branch.precondition _ _ left right
    have completed := Realizable.pairOutputs computation.inputDomains _ _ branch.precondition _ _ pairMatrix bases
    apply completed.withSpecification branch.precondition branch.compute (by intros; assumption)
    intro sizes arguments valid
    have notDiagonal : ¬ ∀ row column, row ≠ column → (arguments ()).1.val row column = 0 := by
      intro diagonal
      have accepted := (integerMatrixIsDiagonal_correct dimension width sizes (arguments ()).1).mpr diagonal
      have rejected := valid.2
      change (integerMatrixIsDiagonal dimension width).compute sizes ⟨fun _ => (arguments ()).1, trivial⟩ = false at rejected
      rw [accepted] at rejected
      contradiction
    have same := integerHermiteAlternatingPair_correct dimension width sizes
      ⟨fun _ => (arguments ()).1, currentPermitted dimension width budget sizes arguments valid.1⟩
    have advance : IntegerMatrix.hermiteAlternatingAdvance (stateValues dimension width budget sizes (arguments ())) =
        ((step sizes ⟨arguments, valid⟩).1.val,
          (step sizes ⟨arguments, valid⟩).2.1.val * (arguments ()).2.1.val,
          (arguments ()).2.2.val * (step sizes ⟨arguments, valid⟩).2.2.val) := by
      dsimp only [IntegerMatrix.hermiteAlternatingAdvance, stateValues]
      rw [ite_eq_right notDiagonal, ← same]
    apply Prod.ext
    · apply Subtype.ext
      exact (congrArg Prod.fst advance).symm
    · apply Prod.ext
      · apply Subtype.ext
        exact (congrArg (fun result => result.2.1) advance).symm
      · apply Subtype.ext
        exact (congrArg (fun result => result.2.2) advance).symm

end Realizable.Internal
end Polytime2.Computation
