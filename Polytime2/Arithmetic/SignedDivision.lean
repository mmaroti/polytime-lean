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

import Polytime2.Arithmetic.SignedGcd
import Polytime2.Arithmetic.SignedDivisionMath

/-! # Certified Euclidean division of signed integers

Inputs have a common magnitude width `w` and the divisor is nonzero. Both
quotient and nonnegative remainder retain width `w`. One unsigned division
pass is bound before signed correction, so extracting the two results does
not repeat that pass. Quotient increment and remainder subtraction are private.
-/

namespace Polytime2.Computation.Realizable.Internal.SignedDivision

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def context (width : MvPolynomial Parameter ℕ) : Bool ⊕ Unit → EncodedDomain Parameter :=
  Sum.elim (fun _ => binaryIntegers width)
    (fun _ => (binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width))

def admissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (context width name).Carrier sizes) : Prop :=
  (arguments (.inl true)).val ≠ 0 ∧
    (arguments (.inr ())).1.val = (arguments (.inl false)).val.natAbs / (arguments (.inl true)).val.natAbs ∧
    (arguments (.inr ())).2.val = (arguments (.inl false)).val.natAbs % (arguments (.inl true)).val.natAbs

noncomputable def quotientWord (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments // admissible width sizes arguments}) : (binaryNaturalsOfWidth width).Carrier sizes :=
  ⟨quotientMagnitude (arguments.val (.inl false)).val (arguments.val (.inl true)).val, by
    rw [quotient_magnitude _ _ arguments.property.1]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans_lt (arguments.val (.inl false)).property⟩

noncomputable def remainderWord (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments // admissible width sizes arguments}) : (binaryNaturalsOfWidth width).Carrier sizes :=
  ⟨remainderMagnitude (arguments.val (.inl false)).val (arguments.val (.inl true)).val,
    (remainder_bound _ _ arguments.property.1).trans_lt (arguments.val (.inl true)).property⟩

theorem pairField_realizable (width : MvPolynomial Parameter ℕ)
    (allowed : ∀ sizes, (∀ name, (context width name).Carrier sizes) → Prop) (second : Bool) :
    (Computation.mk (context width) (binaryNaturalsOfWidth width) allowed
      (fun _ arguments => if second then (arguments.val (.inr ())).2 else (arguments.val (.inr ())).1)).Realizable := by
  cases second with
  | false =>
    exact (pairProjection_realizable (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth width) false).onResults
      (context width) allowed (fun _ _ arguments => arguments.val (.inr ())) (by intros; trivial)
      (fun _ => Realizable.argument (context width) (.inr ()) allowed)
  | true =>
    exact (pairProjection_realizable (binaryNaturalsOfWidth width) (binaryNaturalsOfWidth width) true).onResults
      (context width) allowed (fun _ _ arguments => arguments.val (.inr ())) (by intros; trivial)
      (fun _ => Realizable.argument (context width) (.inr ()) allowed)

theorem originalSign_realizable (width : MvPolynomial Parameter ℕ)
    (allowed : ∀ sizes, (∀ name, (context width name).Carrier sizes) → Prop) (name : Bool) :
    (Computation.mk (context width) booleans allowed
      (fun _ arguments => SignedEncoding.negative (arguments.val (.inl name)).val)).Realizable :=
  (integerNegative_realizable width).onResults (context width) allowed
    (fun _ _ arguments => arguments.val (.inl name)) (by intros; trivial)
    (fun _ => Realizable.argument (context width) (.inl name) allowed)

/-- The correction consumes the stored unsigned pair under its mathematical contract. -/
theorem correctedWords_realizable (width : MvPolynomial Parameter ℕ) :
    (Computation.mk (context width) ((binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width))
      (admissible width) (fun sizes arguments => (quotientWord width sizes arguments, remainderWord width sizes arguments))).Realizable := by
  let inputs := context width
  let allowed := admissible width
  let word := binaryNaturalsOfWidth width
  have field := pairField_realizable width allowed
  have sign := originalSign_realizable width allowed
  have remainderNonzero := (field true).followedBy (Realizable.Internal.naturalNonzero_realizable width)
    rfl (by intros; trivial)
  have rounded := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool)
    (fun flags => flags false && flags true)).onResults inputs allowed
    (fun name _ arguments => if name then decide (0 < (arguments.val (.inr ())).2.val)
      else SignedEncoding.negative (arguments.val (.inl false)).val)
    (by intros; trivial) (by intro name; cases name; exact sign false; exact remainderNonzero)
  have roundReady : (Computation.mk inputs booleans allowed
      (fun _ arguments => adjust (arguments.val (.inl false)).val (arguments.val (.inr ())).2.val)).Realizable := by
    exact rounded.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments valid
      change (SignedEncoding.negative (arguments (.inl false)).val &&
        decide (0 < (arguments (.inr ())).2.val)) =
          adjust (arguments (.inl false)).val (arguments (.inr ())).2.val
      apply Bool.eq_iff_iff.mpr
      simp only [SignedEncoding.negative, adjust, Bool.and_eq_true, decide_eq_true_eq]
      omega)
  have incremented := (field false).followedBy (naturalIncrement_realizable width) rfl (by intros; trivial)
  have quotientCandidate := Realizable.conditional inputs word allowed
    (fun _ arguments => adjust (arguments.val (.inl false)).val (arguments.val (.inr ())).2.val)
    (fun sizes arguments => (naturalIncrement width).compute sizes
      ⟨(fun _ => (arguments.val (.inr ())).1), trivial⟩)
    (fun _ arguments => (arguments.val (.inr ())).1) roundReady incremented (field false)
  have quotientReady : (Computation.mk inputs word allowed (quotientWord width)).Realizable := by
    exact quotientCandidate.withSpecification allowed (quotientWord width) (by intros; assumption) (by
      intro sizes arguments valid
      apply Fin.ext
      have expected := quotient_modular (MvPolynomial.eval sizes width)
        (arguments (.inl false)).val (arguments (.inl true)).val valid.1 (arguments (.inl false)).property
      rw [← valid.2.1, ← valid.2.2] at expected
      cases correction : adjust (arguments (.inl false)).val (arguments (.inr ())).2.val <;>
        simpa only [quotientWord, naturalIncrement, unaryMap, correction, Bool.false_eq_true, ↓reduceIte] using expected)
  have divisorMagnitude := (integerMagnitude_realizable width).onResults inputs allowed
    (fun _ _ arguments => arguments.val (.inl true)) (by intros; trivial)
    (fun _ => Realizable.argument inputs (.inl true) allowed)
  have reduced := (naturalSubtract_realizable width).onResults inputs allowed
    (fun name _ arguments => if name then (arguments.val (.inr ())).2 else
      ⟨(arguments.val (.inl true)).val.natAbs, (arguments.val (.inl true)).property⟩)
    (by
      intro sizes arguments
      change (arguments.val (.inr ())).2.val ≤ (arguments.val (.inl true)).val.natAbs
      rw [arguments.property.2.2]
      exact (Nat.mod_lt _ (Int.natAbs_pos.mpr arguments.property.1)).le)
    (by intro name; cases name; exact divisorMagnitude; exact field true)
  let remainderDifference sizes (arguments : {arguments // allowed sizes arguments}) : word.Carrier sizes :=
    ⟨(arguments.val (.inl true)).val.natAbs - (arguments.val (.inr ())).2.val,
      (Nat.sub_le _ _).trans_lt (arguments.val (.inl true)).property⟩
  have differenceReady : (Computation.mk inputs word allowed remainderDifference).Realizable := reduced
  have remainderCandidate := Realizable.conditional inputs word allowed
    (fun _ arguments => adjust (arguments.val (.inl false)).val (arguments.val (.inr ())).2.val)
    remainderDifference (fun _ arguments => (arguments.val (.inr ())).2) roundReady differenceReady (field true)
  have remainderReady : (Computation.mk inputs word allowed (remainderWord width)).Realizable := by
    exact remainderCandidate.withSpecification allowed (remainderWord width) (by intros; assumption) (by
      intro sizes arguments valid
      apply Fin.ext
      have expected : (if adjust (arguments (.inl false)).val (arguments (.inr ())).2.val then
          (arguments (.inl true)).val.natAbs - (arguments (.inr ())).2.val else (arguments (.inr ())).2.val) =
            remainderMagnitude (arguments (.inl false)).val (arguments (.inl true)).val := by
        rw [valid.2.2]
        rfl
      cases correction : adjust (arguments (.inl false)).val (arguments (.inr ())).2.val <;>
        simpa only [correction, Bool.false_eq_true, ↓reduceIte, remainderWord, remainderDifference] using expected)
  exact Realizable.pairOutputs inputs word word allowed _ _ quotientReady remainderReady

def correctedAdmissible (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (context width name).Carrier sizes) : Prop :=
  (arguments (.inl true)).val ≠ 0 ∧
    (arguments (.inr ())).1.val = quotientMagnitude (arguments (.inl false)).val (arguments (.inl true)).val ∧
    (arguments (.inr ())).2.val = remainderMagnitude (arguments (.inl false)).val (arguments (.inl true)).val

noncomputable def signResults (width : MvPolynomial Parameter ℕ) : Computation Parameter (Bool ⊕ Unit) where
  inputDomains := context width
  outputDomain := (binaryIntegers width).prod (binaryIntegers width)
  precondition := correctedAdmissible width
  compute sizes arguments := (integerDivision width).compute sizes
    ⟨(fun name => arguments.val (.inl name)), arguments.property.1⟩

theorem signResults_realizable (width : MvPolynomial Parameter ℕ) : (signResults width).Realizable := by
  let inputs := context width
  let allowed := correctedAdmissible width
  let word := binaryNaturalsOfWidth width
  have field := pairField_realizable width allowed
  have originalSign := originalSign_realizable width allowed
  have quotientNonzero := (field false).followedBy (Realizable.Internal.naturalNonzero_realizable width)
    rfl (by intros; trivial)
  have tested := (booleanOperation_realizable (Parameter := Parameter) (Argument := Bool ⊕ Unit)
    (fun flags => (flags (.inl false) != flags (.inl true)) && flags (.inr ()))).onResults inputs allowed
    (fun name _ arguments => match name with
      | .inl original => SignedEncoding.negative (arguments.val (.inl original)).val
      | .inr _ => decide (0 < (arguments.val (.inr ())).1.val))
    (by intros; trivial) (by
      intro name
      cases name with
      | inl original => exact originalSign original
      | inr singleton => cases singleton; exact quotientNonzero)
  have quotientSign : (Computation.mk inputs booleans allowed
      (fun _ arguments => SignedEncoding.negative ((arguments.val (.inl false)).val /
        (arguments.val (.inl true)).val))).Realizable := by
    exact tested.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments valid
      change ((SignedEncoding.negative (arguments (.inl false)).val !=
          SignedEncoding.negative (arguments (.inl true)).val) &&
        decide (0 < (arguments (.inr ())).1.val)) = _
      rw [valid.2.1]
      exact quotient_sign _ _ valid.1)
  have quotientParts := Realizable.pairOutputs inputs booleans word allowed _ _ quotientSign (field false)
  have quotientConstructed := quotientParts.followedBy (Realizable.Internal.integerOfParts_realizable width) rfl (by
    intro sizes arguments valid
    change SignedEncoding.negative ((arguments (.inl false)).val / (arguments (.inl true)).val) = true →
      (arguments (.inr ())).1.val ≠ 0
    rw [valid.2.1, quotient_magnitude _ _ valid.1]
    intro sign zero
    have negative : (arguments (.inl false)).val / (arguments (.inl true)).val < 0 := of_decide_eq_true sign
    exact (ne_of_lt negative) (Int.natAbs_eq_zero.mp zero))
  have quotientReady : (Computation.mk inputs (binaryIntegers width) allowed
      (fun sizes arguments => ((signResults width).compute sizes arguments).1)).Realizable := by
    exact quotientConstructed.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments valid
      apply Subtype.ext
      change (if SignedEncoding.negative ((arguments (.inl false)).val / (arguments (.inl true)).val) then
        -((arguments (.inr ())).1.val : ℤ) else ((arguments (.inr ())).1.val : ℤ)) =
          (arguments (.inl false)).val / (arguments (.inl true)).val
      rw [valid.2.1, quotient_magnitude _ _ valid.1]
      exact SignedEncoding.restore _)
  have remainderConstructed := (field true).followedBy
    (Realizable.Internal.integerOfMagnitude_realizable width) rfl (by intros; trivial)
  have remainderReady : (Computation.mk inputs (binaryIntegers width) allowed
      (fun sizes arguments => ((signResults width).compute sizes arguments).2)).Realizable := by
    exact remainderConstructed.withSpecification allowed _ (by intros; assumption) (by
      intro sizes arguments valid
      apply Subtype.ext
      change ((arguments (.inr ())).2.val : ℤ) = (arguments (.inl false)).val % (arguments (.inl true)).val
      rw [valid.2.2]
      exact (correct _ _ valid.1).2)
  exact Realizable.pairOutputs inputs (binaryIntegers width) (binaryIntegers width) allowed _ _ quotientReady remainderReady

noncomputable def continuation (width : MvPolynomial Parameter ℕ) : Computation Parameter (Bool ⊕ Unit) where
  inputDomains := context width
  outputDomain := (binaryIntegers width).prod (binaryIntegers width)
  precondition := admissible width
  compute sizes arguments := (integerDivision width).compute sizes
    ⟨(fun name => arguments.val (.inl name)), arguments.property.1⟩

theorem continuation_realizable (width : MvPolynomial Parameter ℕ) : (continuation width).Realizable := by
  let hostInputs := Sum.elim (context width)
    (fun _ : Unit => (binaryNaturalsOfWidth width).prod (binaryNaturalsOfWidth width))
  let originalSelection : Bool ↪ Bool ⊕ Unit := ⟨Sum.inl, Sum.inl_injective⟩
  let selection : Bool ⊕ Unit ↪ (Bool ⊕ Unit) ⊕ Unit :=
    originalSelection.sumMap (Function.Embedding.refl Unit)
  have signed := (signResults_realizable width).withArguments hostInputs selection
    (by intro name; cases name <;> rfl)
  have complete := (correctedWords_realizable width).letThen signed (fun _ => rfl) rfl (by
    intro sizes arguments valid
    change (arguments (.inl true)).val ≠ 0 ∧ _ ∧ _
    exact ⟨valid.1, rfl, rfl⟩)
  exact complete.withSpecification (admissible width) (continuation width).compute
    (by intros; assumption) (by intros; rfl)

end Polytime2.Computation.Realizable.Internal.SignedDivision

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

theorem integerDivision_realizable (width : MvPolynomial Parameter ℕ) :
    (integerDivision width).Realizable := by
  let inputs := (integerDivision width).inputDomains
  let allowed := (integerDivision width).precondition
  have divided := (Realizable.Internal.naturalDivision_realizable width).onResults inputs allowed
    (fun name _ arguments => ⟨(arguments.val name).val.natAbs, (arguments.val name).property⟩)
    (by intro sizes arguments; exact Int.natAbs_pos.mpr arguments.property)
    (by
      intro name
      exact (integerMagnitude_realizable width).onResults inputs allowed
        (fun _ _ arguments => arguments.val name) (by intros; trivial)
        (fun _ => Realizable.argument inputs name allowed))
  have complete := divided.letThen (Realizable.Internal.SignedDivision.continuation_realizable width)
    (fun _ => rfl) rfl (by
      intro sizes arguments valid
      exact ⟨valid, rfl, rfl⟩)
  exact complete.withSpecification allowed (integerDivision width).compute
    (by intros; assumption) (by intros; rfl)

/-- The ordinary Euclidean quotient needs only a nonzero divisor. -/
noncomputable def integerQuotient (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains := (integerDivision width).inputDomains
  outputDomain := binaryIntegers width
  precondition := (integerDivision width).precondition
  compute sizes arguments := ((integerDivision width).compute sizes arguments).1

theorem integerQuotient_realizable (width : MvPolynomial Parameter ℕ) :
    (integerQuotient width).Realizable := by
  exact ((integerDivision_realizable width).followedBy
    (pairProjection_realizable (binaryIntegers width) (binaryIntegers width) false) rfl (by intros; trivial)).withSpecification
      (integerQuotient width).precondition (integerQuotient width).compute (by intros; assumption) (by intros; rfl)

/-- The Euclidean remainder is nonnegative even for a negative divisor. -/
noncomputable def integerRemainder (width : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains := (integerDivision width).inputDomains
  outputDomain := binaryIntegers width
  precondition := (integerDivision width).precondition
  compute sizes arguments := ((integerDivision width).compute sizes arguments).2

theorem integerRemainder_realizable (width : MvPolynomial Parameter ℕ) :
    (integerRemainder width).Realizable := by
  exact ((integerDivision_realizable width).followedBy
    (pairProjection_realizable (binaryIntegers width) (binaryIntegers width) true) rfl (by intros; trivial)).withSpecification
      (integerRemainder width).precondition (integerRemainder width).compute (by intros; assumption) (by intros; rfl)

theorem integerRemainder_correct (width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerRemainder width).Arguments sizes)
    (valid : (integerRemainder width).precondition sizes arguments) :
    let answer := (integerRemainder width).compute sizes ⟨arguments, valid⟩
    0 ≤ answer.val ∧ answer.val < ((arguments true).val.natAbs : ℤ) :=
  ⟨Int.emod_nonneg _ valid, Int.emod_lt _ valid⟩

end Polytime2.Computation
