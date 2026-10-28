import Polytime2.Circuit.WireArithmetic

/-! # Widening canonical gate references

This operation changes the finite bound of each operand while retaining the
same mathematical gate. Constants and NAND operands use the existing sum,
product, and coordinate computations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Circuit

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Increase reference capacity without changing a gate's natural wire numbers. -/
noncomputable def gateWiden (source target : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target) : Computation Parameter Unit :=
  unaryMap (gateDomain source) (gateDomain target) (fun _ _ => True)
    (fun sizes gate => gate.val.map id (fun pair => (pair.1.castLE (bounded sizes), pair.2.castLE (bounded sizes))))

theorem gateWiden_realizable (source target : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target) :
    (gateWiden source target bounded).Realizable := by
  have coordinates := wireOfPosition_realizable source target bounded
  have paired := coordinates.prodMap coordinates
  have right := paired.followedBy
    (sumInr_realizable booleans ((arrayPosition target).prod (arrayPosition target))) rfl (by intros; trivial)
  have rightReady := right.withSpecification (fun _ _ => True)
    (fun sizes arguments => Sum.inr ((arguments.val ()).1.castLE (bounded sizes), (arguments.val ()).2.castLE (bounded sizes)))
    (by intros; trivial) (by intros; rfl)
  have branches := sumCases_realizable booleans ((arrayPosition source).prod (arrayPosition source))
    (gateDomain target) (fun _ _ => True) (fun _ _ => True)
    (fun _ value => Sum.inl value.val)
    (fun sizes value => Sum.inr (value.val.1.castLE (bounded sizes), value.val.2.castLE (bounded sizes)))
    (sumInl_realizable booleans ((arrayPosition target).prod (arrayPosition target))) rightReady
  apply branches.withSpecification (gateWiden source target bounded).precondition
    (gateWiden source target bounded).compute (by
      intro sizes arguments allowed
      change (arguments ()).elim (fun _ => True) (fun _ => True)
      cases arguments () <;> trivial)
  intro sizes arguments allowed
  simp only [sumCases, gateWiden, unaryMap]
  cases arguments () <;> rfl

theorem gateWiden_value (source target : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target)
    (sizes : Parameter → ℕ) (gate : (gateDomain source).Carrier sizes) :
    gateValue ((gateWiden source target bounded).compute sizes ⟨(fun _ => gate), trivial⟩) = gateValue gate := by
  cases gate <;> rfl

end Polytime2.Circuit
