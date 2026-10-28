import Polytime2.Complexity.CookLevin.WordGuardSuffix
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FlattenRecords

/-! # Tabulating every prefix block of the word-code guard -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

private noncomputable def suffixRows (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Empty :=
  arrayTabulate Empty.elim (wordGuardSuffix base available).outputDomain (MvPolynomial.X true)
    (fun sizes _ position => (wordGuardSuffix base available).compute sizes ⟨(fun _ => position), trivial⟩)

private theorem suffixRows_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (suffixRows base available).Realizable := by
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Bool :=
    Sum.elim Empty.elim (fun _ => arrayPosition (MvPolynomial.X true))
  have selected := (wordGuardSuffix_realizable base available).onArguments inputs (fun _ _ => True)
    (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  exact selected.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Emit the remaining copies and joining gates in reverse word order. -/
noncomputable def wordGuardSuffixes (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    Computation Bool Empty :=
  (suffixRows base available).followedBy
    (arrayFlattenRecords (gateDomain (wordGuardWires base)) letterGuardSuffix.gateCount (MvPolynomial.X true))
    rfl (by intros; trivial)

theorem wordGuardSuffixes_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (wordGuardSuffixes base available).Realizable :=
  (suffixRows_realizable base available).followedBy
    (arrayFlattenRecords_realizable (gateDomain (wordGuardWires base)) letterGuardSuffix.gateCount (MvPolynomial.X true))
    rfl (by intros; trivial)

/-- The entire flat suffix array is the exact mathematical compiler suffix. -/
theorem wordGuardSuffixes_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (wordGuardSuffixes base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGuardSuffixes base available).compute sizes arguments index)) =
      (List.ofFn (fun position : Fin (MvPolynomial.eval sizes (MvPolynomial.X true)) =>
        ((Expression.conjunctionTail (wordLetterExpression _ position.rev)
          (MvPolynomial.eval sizes base + letterExpression.gateCount * position.rev.val + letterExpression.gateCount - 1)
          (MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true +
            (2 * letterExpression.gateCount + 5) * position.val)).compile
          (MvPolynomial.eval sizes base + letterExpression.gateCount * sizes true + 1 +
            (2 * letterExpression.gateCount + 5) * position.val)).1)).flatten := by
  simp only [wordGuardSuffixes, followedBy]
  rw [List.ofFn_comp' _ gateValue, arrayFlattenRecords_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext position
  exact wordGuardSuffix_value base available sizes ⟨(fun _ => position), trivial⟩

end Polytime2.Complexity.CookLevin
