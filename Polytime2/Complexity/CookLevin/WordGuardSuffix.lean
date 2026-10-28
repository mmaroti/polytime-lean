import Polytime2.Complexity.CookLevin.WordGuardPrefix
import Polytime2.Arrays.PositionReverse

/-! # Certified reverse-order suffix blocks of the letter guard

Each fixed template port is an affine address in the suffix position or its
reverse. Reversal and affine arithmetic reuse existing certified operations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

private theorem suffixEnd_fits (base : MvPolynomial Bool ℕ) (sizes : Bool → ℕ)
    (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true))) :
    MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true + 1 +
        (2 * letterExpression.gateCount + 5) * position.val + (2 * letterExpression.gateCount + 5) ≤
      MvPolynomial.eval sizes (wordGuardWires base) := by
  have bounded : position.val < sizes true := by simpa only [MvPolynomial.eval_X] using position.isLt
  have scaled := Nat.mul_le_mul_left (2 * letterExpression.gateCount + 5) (Nat.succ_le_of_lt bounded)
  simp only [Nat.mul_succ] at scaled
  simp only [wordGuardWires, map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
  omega

/-- Specialization-fixed origin, stride, and reversal flag for a template port. -/
private noncomputable def suffixPortData (base : MvPolynomial Bool ℕ)
    (port : Unit ⊕ Fin (Fintype.card Letter + 2)) : MvPolynomial Bool ℕ × ℕ × Bool :=
  match port with
  | .inl () => (base + MvPolynomial.C letterExpression.gateCount * MvPolynomial.X true + 1,
      2 * letterExpression.gateCount + 5, false)
  | .inr index => if index.val < Fintype.card Letter then
      (MvPolynomial.C index.val, Fintype.card Letter, true)
    else if index.val = Fintype.card Letter then
      (base + MvPolynomial.C (letterExpression.gateCount - 1), letterExpression.gateCount, true)
    else (base + MvPolynomial.C letterExpression.gateCount * MvPolynomial.X true,
      2 * letterExpression.gateCount + 5, false)

private theorem suffixReference_fits (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ) (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true)))
    (port : Unit ⊕ Fin (Fintype.card Letter + 2)) :
    let data := suffixPortData base port
    MvPolynomial.eval sizes data.1 + data.2.1 * (if data.2.2 then position.rev else position).val <
      MvPolynomial.eval sizes (wordGuardWires base) := by
  cases port with
  | inl singleton =>
    cases singleton
    have fits := suffixEnd_fits base sizes position
    simp only [suffixPortData, Bool.false_eq_true, ↓reduceIte, map_add, map_mul, map_one,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    omega
  | inr index =>
    by_cases original : index.val < Fintype.card Letter
    · simpa only [suffixPortData, ite_eq_left original, ↓reduceIte, MvPolynomial.eval_C] using
        wordGuardInput_fits base available sizes position.rev ⟨index.val, original⟩
    · by_cases selected : index.val = Fintype.card Letter
      · have fits := wordGuardPrefixEnd_fits base sizes position.rev
        have positive := letterExpression_positive
        simp only [suffixPortData, ite_eq_right original, ite_eq_left selected, ↓reduceIte, map_add, MvPolynomial.eval_C]
        omega
      · have fits := suffixEnd_fits base sizes position
        simp only [suffixPortData, ite_eq_right original, ite_eq_right selected, Bool.false_eq_true, ↓reduceIte,
          map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
        omega

private noncomputable def suffixCoordinate (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (port : Unit ⊕ Fin (Fintype.card Letter + 2)) : Computation Bool Unit :=
  let data := suffixPortData base port
  unaryMap (arrayPosition (MvPolynomial.X true)) (arrayPosition (wordGuardWires base)) (fun _ _ => True)
    (fun sizes position => ⟨MvPolynomial.eval sizes data.1 + data.2.1 *
      (if data.2.2 then position.val.rev else position.val).val,
      suffixReference_fits base available sizes position.val port⟩)

private theorem suffixCoordinate_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (port : Unit ⊕ Fin (Fintype.card Letter + 2)) : (suffixCoordinate base available port).Realizable := by
  let data := suffixPortData base port
  have bounded (sizes : Bool → ℕ) (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true))) :
      MvPolynomial.eval sizes data.1 + data.2.1 * position.val < MvPolynomial.eval sizes (wordGuardWires base) := by
    by_cases reversed : data.2.2 = true
    · have fits := suffixReference_fits base available sizes position.rev port
      change MvPolynomial.eval sizes data.1 + data.2.1 *
        (if data.2.2 then position.rev.rev else position.rev).val < _ at fits
      simpa only [reversed, ↓reduceIte, Fin.rev_rev] using fits
    · have fits := suffixReference_fits base available sizes position port
      change MvPolynomial.eval sizes data.1 + data.2.1 *
        (if data.2.2 then position.rev else position).val < _ at fits
      simpa only [ite_eq_right reversed] using fits
  have address := wordGuardAddress_realizable base data.1 data.2.1 bounded
  by_cases reversed : data.2.2 = true
  · have ready := (arrayPositionReverse_realizable (MvPolynomial.X true)).followedBy address rfl (by intros; trivial)
    apply ready.withSpecification (fun _ _ => True) (suffixCoordinate base available port).compute (by intros; trivial)
    intro sizes arguments accepted
    apply Fin.ext
    change MvPolynomial.eval sizes data.1 + data.2.1 * (arguments ()).rev.val =
      MvPolynomial.eval sizes data.1 + data.2.1 * (if data.2.2 then (arguments ()).rev else arguments ()).val
    rw [ite_eq_left reversed]
  · apply address.withSpecification (fun _ _ => True) (suffixCoordinate base available port).compute (by intros; trivial)
    intro sizes arguments accepted
    apply Fin.ext
    change MvPolynomial.eval sizes data.1 + data.2.1 * (arguments ()).val =
      MvPolynomial.eval sizes data.1 + data.2.1 * (if data.2.2 then (arguments ()).rev else arguments ()).val
    rw [ite_eq_right reversed]

/-- Emit the next suffix block, visiting letter positions in reverse order. -/
noncomputable def wordGuardSuffix (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Unit :=
  (letterGuardSuffix.emitTemplateAt letterGuardSuffix_valid (wordGuardWires base)).onResults
    (fun _ => arrayPosition (MvPolynomial.X true)) (fun _ _ => True)
    (fun port sizes arguments => (suffixCoordinate base available port).compute sizes arguments)
    (by
      intro sizes arguments
      change MvPolynomial.eval sizes (base + MvPolynomial.C letterExpression.gateCount * MvPolynomial.X true + 1) +
        (2 * letterExpression.gateCount + 5) * (arguments.val ()).val + letterGuardSuffix.gateCount ≤ _
      simp only [map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [letterGuardSuffix_gateCount]
      exact suffixEnd_fits base sizes (arguments.val ()))

theorem wordGuardSuffix_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (wordGuardSuffix base available).Realizable := by
  apply (letterGuardSuffix.emitTemplateAt_realizable letterGuardSuffix_valid (wordGuardWires base)).onResults
  intro port
  exact suffixCoordinate_realizable base available port

/-- The suffix block is exactly the existing compiler's two remaining letter
copies and five joining gates at the specified reverse-order position. -/
theorem wordGuardSuffix_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (wordGuardSuffix base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGuardSuffix base available).compute sizes arguments index)) =
      ((Expression.conjunctionTail
        (wordLetterExpression (MvPolynomial.eval sizes (MvPolynomial.X true)) (arguments.val ()).rev)
        (MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).rev.val + letterExpression.gateCount - 1)
        (MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true +
          (2 * letterExpression.gateCount + 5) * (arguments.val ()).val)).compile
        (MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true + 1 +
          (2 * letterExpression.gateCount + 5) * (arguments.val ()).val)).1 := by
  let start := (suffixCoordinate base available (.inl ())).compute sizes arguments
  let inputs := fun port => (suffixCoordinate base available (.inr port)).compute sizes arguments
  let names := layerNames (fun port => (inputs port).val)
  have startValue : start.val = MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true + 1 +
      (2 * letterExpression.gateCount + 5) * (arguments.val ()).val := by
    change MvPolynomial.eval sizes (base + MvPolynomial.C letterExpression.gateCount * MvPolynomial.X true + 1) +
      (2 * letterExpression.gateCount + 5) * (arguments.val ()).val = _
    simp only [map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have selectedValue : names (Fintype.card Letter) = MvPolynomial.eval sizes base +
      letterExpression.gateCount * (arguments.val ()).rev.val + letterExpression.gateCount - 1 := by
    have within : Fintype.card Letter < Fintype.card Letter + 2 := by omega
    simp only [names, layerNames, dite_eq_left within]
    change MvPolynomial.eval sizes (base + MvPolynomial.C (letterExpression.gateCount - 1)) +
      letterExpression.gateCount * (arguments.val ()).rev.val = _
    simp only [map_add, MvPolynomial.eval_C]
    have positive := letterExpression_positive
    omega
  have tailValue : names (Fintype.card Letter + 1) = MvPolynomial.eval sizes base +
      letterExpression.gateCount * sizes true + (2 * letterExpression.gateCount + 5) * (arguments.val ()).val := by
    have within : Fintype.card Letter + 1 < Fintype.card Letter + 2 := by omega
    simp only [names, layerNames, dite_eq_left within]
    have outside : ¬ Fintype.card Letter + 1 < Fintype.card Letter := by omega
    have different : Fintype.card Letter + 1 ≠ Fintype.card Letter := by omega
    simp only [inputs, suffixCoordinate, unaryMap, suffixPortData, ite_eq_right outside,
      ite_eq_right different, Bool.false_eq_true, ↓reduceIte, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have letterRename : letterExpression.rename names =
      wordLetterExpression (MvPolynomial.eval sizes (MvPolynomial.X true)) (arguments.val ()).rev := by
    apply Expression.rename_eq_of_agree letterExpression_valid
    intro wire bounded
    have within : wire < Fintype.card Letter + 2 := by omega
    simp only [names, layerNames, wordLetterExpression, dite_eq_left bounded, dite_eq_left within]
    simp only [inputs, suffixCoordinate, unaryMap, suffixPortData, ite_eq_left bounded,
      ↓reduceIte, MvPolynomial.eval_C, finProdFinEquiv, Equiv.coe_fn_mk]
  have expressionEqual : letterGuardSuffix.rename names =
      Expression.conjunctionTail
        (wordLetterExpression (MvPolynomial.eval sizes (MvPolynomial.X true)) (arguments.val ()).rev)
        (MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).rev.val + letterExpression.gateCount - 1)
        (MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true +
          (2 * letterExpression.gateCount + 5) * (arguments.val ()).val) := by
    rw [letterGuardSuffix, Expression.conjunctionTail_rename, letterRename, selectedValue, tailValue]
  have fits : start.val + letterGuardSuffix.gateCount ≤ MvPolynomial.eval sizes (wordGuardWires base) := by
    rw [startValue, letterGuardSuffix_gateCount]
    exact suffixEnd_fits base sizes (arguments.val ())
  have emitted := letterGuardSuffix.emitTemplateAt_value letterGuardSuffix_valid (wordGuardWires base)
    sizes start inputs fits
  rw [expressionEqual, startValue] at emitted
  exact emitted

end Polytime2.Complexity.CookLevin
