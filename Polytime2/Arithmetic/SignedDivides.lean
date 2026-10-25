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

import Polytime2.Arithmetic.SignedDivision
import Polytime2.Arithmetic.SignedWidth
import Polytime2.Computation.Conditional
import Polytime2.Computation.Specification

/-! # A total certified integer divisibility test

For every pair `(a,b)` of bounded signed integers, return whether `a` divides
`b`. If `a` is zero, test `b = 0`; otherwise test the Euclidean remainder.
There are no overflow or nonzero-divisor obligations for callers.
-/

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerDivides (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool := by
  classical
  exact {
    inputDomains := fun _ => EncodedDomain.binaryIntegers width
    outputDomain := EncodedDomain.booleans
    precondition := fun _ _ => True
    compute := fun _ arguments => decide ((arguments.val false).val ∣ (arguments.val true).val) }

theorem integerDivides_realizable (width : MvPolynomial Parameter ℕ) : (integerDivides width).Realizable := by
  classical
  let computation := integerDivides width
  let inputs := computation.inputDomains
  let condition (_sizes : Parameter → ℕ) (arguments : ∀ name, (inputs name).Carrier _sizes) :=
    decide ((arguments false).val = 0)
  have guard := (integerIsZero_realizable width).withArguments inputs (MultiTape.oneTape false) (fun _ => rfl)
  apply Realizable.ofCases (computation := computation) condition guard
  · let allowed sizes arguments := True ∧ condition sizes arguments = true
    have checked := ((integerIsZero_realizable width).withArguments inputs (MultiTape.oneTape true)
      (fun _ => rfl)).withPrecondition allowed (by intros; trivial)
    apply checked.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, trivial⟩)
      (by intros; trivial)
    intro sizes arguments valid
    have zero : (arguments false).val = 0 := of_decide_eq_true valid.2
    apply Bool.eq_iff_iff.mpr
    simp [integerDivides, computation, Computation.withArguments, Computation.withPrecondition,
      integerIsZero, unaryMap, zero]
  · let allowed sizes arguments := True ∧ condition sizes arguments = false
    let reversed := (integerRemainder width).onResults inputs allowed
      (fun choice _ arguments => if choice then arguments.val false else arguments.val true)
      (by intro sizes arguments; exact of_decide_eq_false arguments.property.2)
    have remainder : reversed.Realizable := by
      apply (integerRemainder_realizable width).onResults inputs allowed _ _
      intro choice
      cases choice
      · exact Realizable.argument inputs true allowed
      · exact Realizable.argument inputs false allowed
    have checked := remainder.followedBy (integerIsZero_realizable width) rfl (by intros; trivial)
    apply checked.withSpecification allowed (fun sizes arguments => computation.compute sizes ⟨arguments.val, trivial⟩)
      (by intros; trivial)
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    dsimp only [integerDivides, computation, Computation.followedBy, reversed, Computation.onResults,
      integerIsZero, unaryMap, integerRemainder, integerDivision]
    simp only [decide_eq_true_eq]
    exact Int.dvd_iff_emod_eq_zero.symm

/-- Test divisibility for independently bounded signed integers. -/
private noncomputable def implementation (divisorWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (integerDivides (divisorWidth + valueWidth)).onResults
    (fun choice => if choice then EncodedDomain.binaryIntegers valueWidth else EncodedDomain.binaryIntegers divisorWidth)
    (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (Realizable.Internal.integerWidenTo divisorWidth valueWidth (divisorWidth + valueWidth) rfl).compute sizes
          ⟨fun _ => arguments.val false, trivial⟩
      | true => (Realizable.Internal.integerWidenTo valueWidth divisorWidth (divisorWidth + valueWidth) (by ring)).compute sizes
          ⟨fun _ => arguments.val true, trivial⟩) (by intros; trivial)

/-- Widening both operands preserves their mathematical values and reuses divisibility. -/
private theorem implementation_realizable (divisorWidth valueWidth : MvPolynomial Parameter ℕ) :
    (implementation divisorWidth valueWidth).Realizable := by
  apply (integerDivides_realizable (divisorWidth + valueWidth)).onResults _ _ _ (by intros; trivial)
  intro choice
  cases choice
  · exact (Realizable.Internal.integerWidenTo_realizable divisorWidth valueWidth (divisorWidth + valueWidth) rfl).withArguments
      (fun choice => if choice then EncodedDomain.binaryIntegers valueWidth else EncodedDomain.binaryIntegers divisorWidth)
      (MultiTape.oneTape false) (by intros; rfl)
  · exact (Realizable.Internal.integerWidenTo_realizable valueWidth divisorWidth (divisorWidth + valueWidth) (by ring)).withArguments
      (fun choice => if choice then EncodedDomain.binaryIntegers valueWidth else EncodedDomain.binaryIntegers divisorWidth)
      (MultiTape.oneTape true) (by intros; rfl)

private theorem implementation_correct (divisorWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (implementation divisorWidth valueWidth).Arguments sizes) :
    (implementation divisorWidth valueWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      (arguments false).val ∣ (arguments true).val := by
  change decide ((arguments false).val ∣ (arguments true).val) = true ↔ _
  exact decide_eq_true_iff

/-- Decide divisibility of independently bounded mathematical integers. -/
noncomputable def integerDividesAtWidths (divisorWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  decision (fun choice => if choice then EncodedDomain.binaryIntegers valueWidth else EncodedDomain.binaryIntegers divisorWidth)
    (fun _ _ => True) (fun _ arguments => (arguments false).val ∣ (arguments true).val)

theorem integerDividesAtWidths_realizable (divisorWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerDividesAtWidths divisorWidth valueWidth).Realizable :=
  (implementation_realizable divisorWidth valueWidth).decision _
    (fun sizes arguments _valid => implementation_correct divisorWidth valueWidth sizes arguments)

/-- Width preparation is absent from the public divisibility contract. -/
theorem integerDividesAtWidths_correct (divisorWidth valueWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (integerDividesAtWidths divisorWidth valueWidth).Arguments sizes) :
    (integerDividesAtWidths divisorWidth valueWidth).compute sizes ⟨arguments, trivial⟩ = true ↔
      (arguments false).val ∣ (arguments true).val :=
  decision_correct _ _ _ sizes ⟨arguments, trivial⟩

end Polytime2.Computation
