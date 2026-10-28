import Polytime2.Circuit.Guard
import Mathlib.Tactic.Ring

/-! # Exact template layout for appending an input guard -/

namespace Polytime2.Circuit.Expression

/-- The selector compiler uses three predicate copies and five joining gates. -/
theorem selectWire_compile_blocks (predicate : Expression) (positive : 0 < predicate.gateCount)
    (start output : ℕ) :
    ((select predicate (.wire output) (.constant false)).compile start).1 =
      (predicate.compile start).1 ++ [.inr (start + predicate.gateCount - 1, output)] ++
      (predicate.compile (start + predicate.gateCount + 1)).1 ++
      (predicate.compile (start + 2 * predicate.gateCount + 1)).1 ++
      [.inr (start + 2 * predicate.gateCount, start + 3 * predicate.gateCount), .inl false,
       .inr (start + 3 * predicate.gateCount + 1, start + 3 * predicate.gateCount + 2),
       .inr (start + predicate.gateCount, start + 3 * predicate.gateCount + 3)] := by
  have firstOutput : (predicate.compile start).2 = start + predicate.gateCount - 1 := by
    have result := compile_output predicate start positive
    omega
  have secondOutput : (predicate.compile (start + predicate.gateCount + 1)).2 = start + 2 * predicate.gateCount := by
    have result := compile_output predicate (start + predicate.gateCount + 1) positive
    omega
  have thirdOutput : (predicate.compile (start + 2 * predicate.gateCount + 1)).2 = start + 3 * predicate.gateCount := by
    have result := compile_output predicate (start + 2 * predicate.gateCount + 1) positive
    omega
  simp only [select, compile, compile_length, gateCount, firstOutput, Nat.add_zero, List.nil_append,
    List.append_nil, List.append_assoc, List.cons_append, List.length_append, List.length_cons, List.length_nil]
  simp only [Nat.zero_add, ← Nat.add_assoc]
  rw [show start + predicate.gateCount + 1 + predicate.gateCount =
    start + 2 * predicate.gateCount + 1 by omega, secondOutput, thirdOutput]
  simp only [List.append_cancel_left_eq, List.cons.injEq, Sum.inr.injEq, Prod.mk.injEq, true_and, and_true]
  repeat' constructor <;> omega

end Polytime2.Circuit.Expression
