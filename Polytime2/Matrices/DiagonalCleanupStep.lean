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

import Polytime2.Matrices.DiagonalRepair
import Polytime2.Matrices.DiagonalChain

/-! # One guarded fixed-workspace cleanup update

On a positive diagonal with bounded total product and sufficient basis space,
leave an existing divisibility chain unchanged. Otherwise perform the complete
selected repair. The Boolean guard and arithmetic are certified by composition;
the result agrees with one step of the pure cleanup loop in both branches.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private def cleanupStepAllowed (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : (diagonalRepair length productWidth basisWidth).Arguments sizes) :=
  (∀ index, 0 < (arguments 0 index).val) ∧
    (∏ index, (arguments 0 index).val) ≤ 2 ^ MvPolynomial.eval sizes productWidth ∧
    ∃ prefixWidth : ℕ,
      (∀ row column, ((arguments 1).val row column).natAbs < 2 ^ prefixWidth) ∧
      (∀ row column, ((arguments 2).val row column).natAbs < 2 ^ prefixWidth) ∧
      prefixWidth + (4 * MvPolynomial.eval sizes (productWidth + 1) + 3) ≤ MvPolynomial.eval sizes basisWidth

private theorem cleanupRepairAllowed (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (diagonalRepair length productWidth basisWidth).Arguments sizes)
    (valid : cleanupStepAllowed length productWidth basisWidth sizes arguments)
    (failure : ¬IntegerMatrix.diagonalDivisibilityChain (fun index => (arguments 0 index).val)) :
    (diagonalRepair length productWidth basisWidth).precondition sizes arguments :=
  ⟨⟨failure, valid.2.2⟩, valid.1, valid.2.1⟩

/-- Stop at a divisibility chain, or repair the first failing adjacent pair. -/
noncomputable def diagonalCleanupStep (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) := by
  classical
  exact {
    inputDomains := (diagonalRepair length productWidth basisWidth).inputDomains
    outputDomain := (diagonalRepair length productWidth basisWidth).outputDomain
    precondition := cleanupStepAllowed length productWidth basisWidth
    compute := fun sizes arguments =>
      if chain : IntegerMatrix.diagonalDivisibilityChain (fun index => (arguments.val 0 index).val) then
        (arguments.val 0, (arguments.val 1, arguments.val 2))
      else (diagonalRepair length productWidth basisWidth).compute sizes
        ⟨arguments.val, cleanupRepairAllowed length productWidth basisWidth sizes arguments.val arguments.property chain⟩ }

theorem diagonalCleanupStep_realizable (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalCleanupStep length productWidth basisWidth).Realizable := by
  classical
  let computation := diagonalCleanupStep length productWidth basisWidth
  let condition sizes (arguments : computation.Arguments sizes) :=
    decide (IntegerMatrix.diagonalDivisibilityChain (fun index => (arguments 0 index).val))
  have tested := ((naturalDiagonalIsChain_realizable length (productWidth + 1)).withArguments
    computation.inputDomains (MultiTape.oneTape 0) (fun _ => rfl)).withPrecondition computation.precondition
      (by intros; trivial)
  have guard : (Computation.mk computation.inputDomains booleans computation.precondition
      (fun sizes arguments => condition sizes arguments.val)).Realizable := by
    apply tested.withSpecification computation.precondition _ (by intros; assumption)
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    change (naturalDiagonalIsChain length (productWidth + 1)).compute sizes
      ⟨(fun _ => arguments 0), trivial⟩ = true ↔ decide _ = true
    rw [decide_eq_true_eq]
    exact naturalDiagonalIsChain_correct length (productWidth + 1) sizes (arguments 0)
  apply Realizable.ofCases (computation := computation) condition guard
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have bases := (Realizable.argument computation.inputDomains 1 allowed).prodMk (Realizable.argument computation.inputDomains 2 allowed)
    have complete := (Realizable.argument computation.inputDomains 0 allowed).prodMk bases
    apply complete.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have chain := of_decide_eq_true valid.2
    simp only [computation, diagonalCleanupStep, Computation.withPrecondition, dite_eq_left chain]
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have complete := (diagonalRepair_realizable length productWidth basisWidth).withPrecondition allowed (by
      intro sizes arguments valid
      exact cleanupRepairAllowed length productWidth basisWidth sizes arguments valid.1 (of_decide_eq_false valid.2))
    apply complete.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have failure := of_decide_eq_false valid.2
    simp only [computation, diagonalCleanupStep, Computation.withPrecondition, dite_eq_right failure]

/-- Both guarded branches implement exactly one mathematical cleanup iteration. -/
theorem diagonalCleanupStep_correct (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalCleanupStep length productWidth basisWidth).Arguments sizes //
      (diagonalCleanupStep length productWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalCleanupStep length productWidth basisWidth).compute sizes arguments
    ((fun index => (result.1 index).val), (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.diagonalCleanupWithBases 1 (fun index => (arguments.val 0 index).val)
        (arguments.val 1).val (arguments.val 2).val := by
  classical
  by_cases chain : IntegerMatrix.diagonalDivisibilityChain (fun index => (arguments.val 0 index).val)
  · have stopped := (IntegerMatrix.diagonalViolation_none _).mpr chain
    simp only [diagonalCleanupStep, dite_eq_left chain, IntegerMatrix.diagonalCleanupWithBases, stopped]
  · have valid := cleanupRepairAllowed length productWidth basisWidth sizes arguments.val arguments.property chain
    simpa only [diagonalCleanupStep, dite_eq_right chain] using
      diagonalRepair_correct length productWidth basisWidth sizes ⟨arguments.val, valid⟩

end Polytime2.Computation.Realizable.Internal
