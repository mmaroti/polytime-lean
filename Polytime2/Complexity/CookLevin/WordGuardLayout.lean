import Polytime2.Complexity.CookLevin.WordGuard
import Polytime2.Circuit.UniformConjunction

/-! # Fixed templates and exact layout of the letter-code guard

The prefix template is the fixed one-letter test. Its suffix template reuses
that test twice, together with the already computed prefix and tail wires.
-/

namespace Polytime2.Complexity.CookLevin

open Circuit

/-- The fixed letter test has fresh gates, so its output is its last gate. -/
theorem letterExpression_positive : 0 < letterExpression.gateCount := by
  have count := Expression.truthTable_gateCount (Fintype.card Letter) 0 canonicalLetter
  change letterExpression.gateCount + 4 = 5 * 2 ^ Fintype.card Letter at count
  have positive : 0 < 2 ^ Fintype.card Letter := Nat.two_pow_pos _
  omega

theorem letterExpression_valid : letterExpression.Valid (Fintype.card Letter) :=
  Expression.truthTable_valid (Fintype.card Letter) 0 (Fintype.card Letter) canonicalLetter (by omega)

/-- Letter inputs, followed by ports for the computed selector and tail. -/
noncomputable def letterGuardSuffix : Expression :=
  Expression.conjunctionTail letterExpression (Fintype.card Letter) (Fintype.card Letter + 1)

theorem letterGuardSuffix_valid : letterGuardSuffix.Valid (Fintype.card Letter + 2) :=
  Expression.conjunctionTail_valid (letterExpression_valid.mono (by omega)) (by omega) (by omega)

theorem letterGuardSuffix_gateCount : letterGuardSuffix.gateCount = 2 * letterExpression.gateCount + 5 :=
  Expression.conjunctionTail_gateCount _ _ _

/-- Exact gate blocks of the existing mathematical letter-code guard. -/
theorem wordGuardExpression_compile_blocks (length start : ℕ) :
    ((wordGuardExpression length).compile start).1 =
      (List.ofFn (fun position : Fin length =>
        ((wordLetterExpression length position).compile (start + letterExpression.gateCount * position.val)).1)).flatten ++
      [.inl true] ++
      (List.ofFn (fun index : Fin length =>
        ((Expression.conjunctionTail (wordLetterExpression length index.rev)
          (start + letterExpression.gateCount * index.rev.val + letterExpression.gateCount - 1)
          (start + letterExpression.gateCount * length + (2 * letterExpression.gateCount + 5) * index.val)).compile
          (start + letterExpression.gateCount * length + 1 + (2 * letterExpression.gateCount + 5) * index.val)).1)).flatten := by
  apply Expression.allExpressions_compile_blocks (wordLetterExpression length) letterExpression.gateCount
    letterExpression_positive
  intro position
  exact Expression.rename_gateCount _ _

end Polytime2.Complexity.CookLevin
