import Polytime2.Circuit.Observe

/-! # Rejecting invalid Boolean input encodings

Append an input predicate to a circuit and conjoin it with the existing
answer. The original computation is retained once; only the predicate's
expression contributes new gates. This supplies the word-code guard for
bounded verifier circuits.
-/

namespace Polytime2.Circuit

def guard (inputs : ℕ) (circuit : Network) (predicate : Expression) : Network :=
  let expression := Expression.select predicate (.wire circuit.2) (.constant false)
  let appended := expression.compile (inputs + circuit.1.length)
  (circuit.1 ++ appended.1, appended.2)

theorem guard_expression_valid {inputs : ℕ} {circuit : Network} {predicate : Expression}
    (valid : Valid inputs circuit) (predicateValid : predicate.Valid inputs) :
    (Expression.select predicate (.wire circuit.2) (.constant false)).Valid
      (inputs + circuit.1.length) :=
  Expression.select_valid (predicateValid.mono (Nat.le_add_right _ _)) valid.2 trivial

theorem guard_valid {inputs : ℕ} {circuit : Network} {predicate : Expression}
    (valid : Valid inputs circuit) (predicateValid : predicate.Valid inputs) :
    Valid inputs (guard inputs circuit predicate) := by
  have appended := Expression.compile_valid (guard_expression_valid valid predicateValid)
  exact ⟨(wellFormed_append _ _ _).mpr ⟨valid.1, appended.1⟩,
    by simpa only [guard, List.length_append, Nat.add_assoc] using appended.2⟩

theorem guard_length (inputs : ℕ) (circuit : Network) (predicate : Expression) :
    (guard inputs circuit predicate).1.length = circuit.1.length + (3 * predicate.gateCount + 5) := by
  simp only [guard, List.length_append, Expression.compile_length, Expression.select, Expression.gateCount]
  omega

theorem guard_correct {inputs : ℕ} {circuit : Network} {predicate : Expression}
    (valid : Valid inputs circuit) (predicateValid : predicate.Valid inputs)
    (assignment : Fin inputs → Bool) :
    evaluate inputs (guard inputs circuit predicate) assignment =
      (predicate.eval (inputValues assignment) && evaluate inputs circuit assignment) := by
  let expression := Expression.select predicate (.wire circuit.2) (.constant false)
  change run inputs (circuit.1 ++ (expression.compile (inputs + circuit.1.length)).1)
    (inputValues assignment) (expression.compile (inputs + circuit.1.length)).2 = _
  rw [run_append, Expression.compile_correct (guard_expression_valid valid predicateValid)]
  simp only [Expression.select_eval, Expression.eval]
  have unchanged : predicate.eval (run inputs circuit.1 (inputValues assignment)) =
      predicate.eval (inputValues assignment) :=
    Expression.eval_eq_of_agree predicateValid (fun wire bound => run_preserves circuit.1 inputs _ wire bound)
  rw [unchanged]
  cases predicate.eval (inputValues assignment) <;> rfl

end Polytime2.Circuit
