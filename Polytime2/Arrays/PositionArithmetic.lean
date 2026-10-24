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

import Polytime2.Arrays.Indices
import Polytime2.Arrays.Count
import Polytime2.Arithmetic.SignedWidth
import Polytime2.Arithmetic.SignedComparison

/-! # Comparing finite array coordinates with mathematical sizes

Coordinate values and size parameters are converted to ordinary signed words
at derived widths. Reuse counting, widening, and signed comparisons. These
rules support active-block guards without exposing numbered storage positions
or requiring a caller-selected arithmetic capacity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Produce the mathematical size as a signed integer with derived capacity. -/
noncomputable def polynomialIntegerSize (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := binaryIntegers (length + 1)
  precondition _ _ := True
  compute sizes _ := ⟨(MvPolynomial.eval sizes length : ℤ), by
    simp only [Int.natAbs_natCast, map_add, map_one]
    exact (Nat.le_succ _).trans_lt Nat.lt_two_pow_self⟩

theorem polynomialIntegerSize_realizable (length : MvPolynomial Parameter ℕ) :
    (polynomialIntegerSize length).Realizable := by
  have counted := (arrayTrue_realizable length).followedBy (countFlags_realizable length) rfl (by intros; trivial)
  have natural := counted.reinterpretOutput (binaryNaturalsOfWidth (length + 1)) (fun _ value => value.toFin)
    (by intros; rfl) (by intro sizes value; change ArrayEncoding.bits (BitVec.ofFin value.toFin) = ArrayEncoding.bits value; rfl)
  have signed := natural.followedBy (integerOfMagnitude_realizable (length + 1)) rfl (by intros; trivial)
  apply signed.withSpecification (fun _ _ => True) (polynomialIntegerSize length).compute (by intros; trivial)
  intro sizes arguments valid
  apply Subtype.ext
  have count := countFlags_correct length sizes (fun _ => true)
  simp only [List.ofFn_const, List.count_replicate_self] at count
  change (((countFlags length).compute sizes ⟨(fun _ => fun _ => true), trivial⟩).toNat : ℤ) = _
  exact congrArg (fun value : ℕ => (value : ℤ)) count

/-- Read a coordinate's natural value at an internally widened signed width. -/
noncomputable def positionInteger (length extra targetWidth : MvPolynomial Parameter ℕ)
    (sameWidth : targetWidth = (length + 1) + extra) : Computation Parameter Unit :=
  ((integerOfMagnitude (length + 1)).reinterpretInputs (fun _ : Unit => arrayPosition length)
    (fun _ _ value => ⟨value.val, by
      simp only [map_add, map_one]
      exact value.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (fun _ _ => True) (by intros; trivial)).followedBy
      (integerWidenTo (length + 1) extra targetWidth sameWidth) rfl (by intros; trivial)

theorem positionInteger_realizable (length extra targetWidth : MvPolynomial Parameter ℕ)
    (sameWidth : targetWidth = (length + 1) + extra) :
    (positionInteger length extra targetWidth sameWidth).Realizable :=
  ((integerOfMagnitude_realizable (length + 1)).reinterpretInputs (fun _ : Unit => arrayPosition length)
    (fun _ _ value => ⟨value.val, by
      simp only [map_add, map_one]
      exact value.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)).followedBy
      (integerWidenTo_realizable (length + 1) extra targetWidth sameWidth) rfl (by intros; trivial)

/-- Decide whether a coordinate lies inside an active prefix of another size. -/
noncomputable def positionWithin (length bound : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := arrayPosition length
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := decide ((arguments.val ()).val < MvPolynomial.eval sizes bound)

theorem positionWithin_realizable (length bound : MvPolynomial Parameter ℕ) :
    (positionWithin length bound).Realizable := by
  let computation := positionWithin length bound
  let capacity := length + bound + 2
  have coordinate := positionInteger_realizable length (bound + 1) capacity (by dsimp [capacity]; ring)
  have limit := ((polynomialIntegerSize_realizable bound).followedBy
    (integerWidenTo_realizable (bound + 1) (length + 1) capacity (by dsimp [capacity]; ring)) rfl (by intros; trivial)).onResults
    computation.inputDomains computation.precondition (fun impossible => impossible.elim)
    (by intros; trivial) (fun impossible => impossible.elim)
  have compared := (integerLess_realizable capacity).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => if choice then
      (((polynomialIntegerSize bound).followedBy
        (integerWidenTo (bound + 1) (length + 1) capacity (by dsimp [capacity]; ring)) rfl (by intros; trivial)).onResults
          computation.inputDomains computation.precondition (fun impossible => impossible.elim)
          (by intros; trivial)).compute sizes arguments
      else (positionInteger length (bound + 1) capacity (by dsimp [capacity]; ring)).compute sizes arguments)
    (by intros; trivial) (by intro choice; cases choice; exact coordinate; exact limit)
  apply compared.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  change decide (((arguments ()).val : ℤ) < (MvPolynomial.eval sizes bound : ℤ)) = decide _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Int.ofNat_lt]

private noncomputable def positionsComparison (firstLength secondLength : MvPolynomial Parameter ℕ)
    (test : ℕ → ℕ → Bool) : Computation Parameter Bool where
  inputDomains name := arrayPosition (if name then secondLength else firstLength)
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := test (arguments.val false).val (arguments.val true).val

private noncomputable def signedComparison (width : MvPolynomial Parameter ℕ)
    (test : ℤ → ℤ → Bool) : Computation Parameter Bool where
  inputDomains _ := binaryIntegers width
  outputDomain := booleans
  precondition _ _ := True
  compute _ arguments := test (arguments.val false).val (arguments.val true).val

private theorem positionsComparison_realizable (firstLength secondLength : MvPolynomial Parameter ℕ)
    (naturalTest : ℕ → ℕ → Bool) (integerTest : ℤ → ℤ → Bool)
    (compatible : ∀ first second : ℕ, integerTest first second = naturalTest first second)
    (scalarRealizable : ∀ width : MvPolynomial Parameter ℕ, (signedComparison width integerTest).Realizable) :
    (positionsComparison firstLength secondLength naturalTest).Realizable := by
  let computation := positionsComparison firstLength secondLength naturalTest
  let capacity := firstLength + secondLength + 2
  let first := (positionInteger firstLength (secondLength + 1) capacity (by dsimp [capacity]; ring)).withArguments
    computation.inputDomains (MultiTape.oneTape false) (fun _ => rfl)
  let second := (positionInteger secondLength (firstLength + 1) capacity (by dsimp [capacity]; ring)).withArguments
    computation.inputDomains (MultiTape.oneTape true) (fun _ => rfl)
  have firstReady : first.Realizable := (positionInteger_realizable firstLength (secondLength + 1) capacity
    (by dsimp [capacity]; ring)).withArguments computation.inputDomains (MultiTape.oneTape false) (fun _ => rfl)
  have secondReady : second.Realizable := (positionInteger_realizable secondLength (firstLength + 1) capacity
    (by dsimp [capacity]; ring)).withArguments computation.inputDomains (MultiTape.oneTape true) (fun _ => rfl)
  have compared := (scalarRealizable capacity).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => if choice then second.compute sizes arguments else first.compute sizes arguments)
    (by intros; trivial) (by intro choice; cases choice; exact firstReady; exact secondReady)
  apply compared.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  exact compatible (arguments false).val (arguments true).val

/-- Compare the numeric values of coordinates from independent dimensions. -/
noncomputable def positionsEqual (firstLength secondLength : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  positionsComparison firstLength secondLength (fun first second => decide (first = second))

theorem positionsEqual_realizable (firstLength secondLength : MvPolynomial Parameter ℕ) :
    (positionsEqual firstLength secondLength).Realizable := by
  apply positionsComparison_realizable firstLength secondLength _ (fun first second => decide (first = second))
  · intro first second
    simp only [Int.natCast_inj]
  · exact integerEqual_realizable

/-- Compare coordinates from independent dimensions by their ordinary natural order. -/
noncomputable def positionsLess (firstLength secondLength : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  positionsComparison firstLength secondLength (fun first second => decide (first < second))

theorem positionsLess_realizable (firstLength secondLength : MvPolynomial Parameter ℕ) :
    (positionsLess firstLength secondLength).Realizable := by
  apply positionsComparison_realizable firstLength secondLength _ (fun first second => decide (first < second))
  · intro first second
    simp only [Int.ofNat_lt]
  · exact integerLess_realizable

end Polytime2.Computation.Realizable.Internal
