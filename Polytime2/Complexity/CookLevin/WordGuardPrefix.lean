import Polytime2.Complexity.CookLevin.WordGuardLayout
import Polytime2.Circuit.ExpressionTemplate

/-! # Certified prefix blocks of the letter-code guard

The base is the number of wires already available. The precondition on that
base says that the external word bits are among those available wires.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

/-- Exact wire count after appending the complete word-code expression. -/
noncomputable def wordGuardWires (base : MvPolynomial Bool ℕ) : MvPolynomial Bool ℕ :=
  base + MvPolynomial.C letterExpression.gateCount * MvPolynomial.X true +
    MvPolynomial.C (2 * letterExpression.gateCount + 5) * MvPolynomial.X true + 1

theorem wordGuardLength_bounded (base : MvPolynomial Bool ℕ) (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (MvPolynomial.X true) ≤ MvPolynomial.eval sizes (wordGuardWires base) := by
  have scaled := Nat.mul_le_mul_right (sizes true) (Nat.succ_le_of_lt letterExpression_positive)
  simp only [Nat.one_mul] at scaled
  simp only [wordGuardWires, map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
  omega

theorem wordGuardPrefixEnd_fits (base : MvPolynomial Bool ℕ) (sizes : Bool → ℕ)
    (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true))) :
    MvPolynomial.eval sizes base + letterExpression.gateCount * position.val + letterExpression.gateCount ≤
      MvPolynomial.eval sizes (wordGuardWires base) := by
  have bounded : position.val < sizes true := by simpa only [MvPolynomial.eval_X] using position.isLt
  have scaled := Nat.mul_le_mul_left letterExpression.gateCount (Nat.succ_le_of_lt bounded)
  simp only [Nat.mul_succ] at scaled
  simp only [wordGuardWires, map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
  omega

theorem wordGuardInput_fits (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ) (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true)))
    (letter : Fin (Fintype.card Letter)) :
    letter.val + Fintype.card Letter * position.val < MvPolynomial.eval sizes (wordGuardWires base) := by
  have bounded := (finProdFinEquiv (position, letter)).isLt
  have original : letter.val + Fintype.card Letter * position.val < sizes true * Fintype.card Letter := by
    simpa only [finProdFinEquiv, Equiv.coe_fn_mk, MvPolynomial.eval_X] using bounded
  have fits := available sizes
  simp only [wordGuardWires, map_add, map_mul, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
  omega

/-- Emit the first copy of the fixed letter-code test at its prefix position. -/
noncomputable def wordGuardPrefix (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Unit :=
  (letterExpression.emitTemplateAt letterExpression_valid (wordGuardWires base)).onResults
    (fun _ => arrayPosition (MvPolynomial.X true)) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl () => ⟨MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).val, by
          have fits := wordGuardPrefixEnd_fits base sizes (arguments.val ())
          have positive := letterExpression_positive
          change MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).val <
            MvPolynomial.eval sizes (wordGuardWires base)
          omega⟩
      | .inr letter => ⟨letter.val + Fintype.card Letter * (arguments.val ()).val,
          wordGuardInput_fits base available sizes (arguments.val ()) letter⟩)
    (by intro sizes arguments; exact wordGuardPrefixEnd_fits base sizes (arguments.val ()))

theorem wordGuardAddress_realizable (base : MvPolynomial Bool ℕ) (origin : MvPolynomial Bool ℕ) (stride : ℕ)
      (bounded : ∀ sizes (position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true))),
        MvPolynomial.eval sizes origin + stride * position.val < MvPolynomial.eval sizes (wordGuardWires base)) :
      (Computation.mk (fun _ : Unit => arrayPosition (MvPolynomial.X true)) (arrayPosition (wordGuardWires base)) (fun _ _ => True)
        (fun sizes arguments => ⟨MvPolynomial.eval sizes origin + stride * (arguments.val ()).val,
          bounded sizes (arguments.val ())⟩)).Realizable := by
    let wires := wordGuardWires base
    have widened := wireOfPosition_realizable (MvPolynomial.X true) wires (wordGuardLength_bounded base)
    have computed := widened.followedBy (wireAffine_realizable wires origin stride) rfl (by
      intro sizes arguments accepted
      change MvPolynomial.eval sizes origin + stride *
        ((wireOfPosition (MvPolynomial.X true) wires (wordGuardLength_bounded base)).compute sizes ⟨arguments, accepted⟩).val < _
      rw [wireOfPosition_value]
      exact bounded sizes (arguments ()))
    exact computed.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

theorem wordGuardPrefix_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (wordGuardPrefix base available).Realizable := by
  let wires := wordGuardWires base
  apply (letterExpression.emitTemplateAt_realizable letterExpression_valid wires).onResults
  intro name
  cases name with
  | inl singleton =>
    cases singleton
    exact wordGuardAddress_realizable base base letterExpression.gateCount (by
      intro sizes position
      have fits := wordGuardPrefixEnd_fits base sizes position
      have positive := letterExpression_positive
      change MvPolynomial.eval sizes base + letterExpression.gateCount * position.val <
        MvPolynomial.eval sizes (wordGuardWires base)
      omega)
  | inr letter =>
    have ready := wordGuardAddress_realizable base (MvPolynomial.C letter.val) (Fintype.card Letter) (by
      intro sizes position
      simpa only [MvPolynomial.eval_C] using wordGuardInput_fits base available sizes position letter)
    apply ready.withSpecification (fun _ _ => True) _ (by intros; trivial)
    intro sizes arguments accepted
    apply Fin.ext
    exact congrArg (fun value => value + Fintype.card Letter * (arguments ()).val)
      (MvPolynomial.eval_C letter.val)

/-- The emitted prefix block is exactly the mathematical one-letter compiler. -/
theorem wordGuardPrefix_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (wordGuardPrefix base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGuardPrefix base available).compute sizes arguments index)) =
      ((wordLetterExpression (MvPolynomial.eval sizes (MvPolynomial.X true)) (arguments.val ())).compile
        (MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).val)).1 := by
  let start : Fin (MvPolynomial.eval sizes (wordGuardWires base)) :=
    ⟨MvPolynomial.eval sizes base + letterExpression.gateCount * (arguments.val ()).val, by
      have fits := wordGuardPrefixEnd_fits base sizes (arguments.val ())
      have positive := letterExpression_positive
      omega⟩
  let inputs : Fin (Fintype.card Letter) → Fin (MvPolynomial.eval sizes (wordGuardWires base)) :=
    fun letter => ⟨letter.val + Fintype.card Letter * (arguments.val ()).val,
      wordGuardInput_fits base available sizes (arguments.val ()) letter⟩
  exact letterExpression.emitTemplateAt_value letterExpression_valid (wordGuardWires base) sizes start inputs
    (wordGuardPrefixEnd_fits base sizes (arguments.val ()))

end Polytime2.Complexity.CookLevin
