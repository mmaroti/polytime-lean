import Polytime2.Circuit.Compile
import Mathlib.Algebra.BigOperators.Fin

/-! # Simultaneous Boolean circuit layers

Compile a finite family of expressions into one shared program. Every
expression reads the original wire prefix, even though fresh gates are emitted
sequentially. The output is an ordinary function naming each result wire.
This is the layer construction needed to unroll machine transitions without
substituting the previous transition's entire expression tree.
-/

namespace Polytime2.Circuit

/-- A gate program with a finite family of selected result wires. -/
abbrev Layer (width : ℕ) := List Gate × (Fin width → ℕ)

/-- Emit a whole layer after the existing wire prefix. -/
def compileLayer : (width : ℕ) → ℕ → (Fin width → Expression) → Layer width
  | 0, _, _ => ([], Fin.elim0)
  | width + 1, start, expressions =>
    let head := (expressions 0).compile start
    let tail := compileLayer width (start + head.1.length) (fun index => expressions index.succ)
    (head.1 ++ tail.1, Fin.cases head.2 tail.2)

theorem compileLayer_length (width start : ℕ) (expressions : Fin width → Expression) :
    (compileLayer width start expressions).1.length = ∑ index, (expressions index).gateCount := by
  induction width generalizing start with
  | zero => simp [compileLayer]
  | succ width induction =>
    simp [compileLayer, List.length_append, Expression.compile_length, induction,
      Fin.sum_univ_succ]

/-- Layer compilation defines every result wire and reads only existing
wires. Starting later is permitted, for appending to a larger program. -/
theorem compileLayer_valid (width : ℕ) {available start : ℕ}
    (expressions : Fin width → Expression)
    (valid : ∀ index, (expressions index).Valid available) (fits : available ≤ start) :
    WellFormed start (compileLayer width start expressions).1 ∧
      ∀ index, (compileLayer width start expressions).2 index <
        start + (compileLayer width start expressions).1.length := by
  induction width generalizing start with
  | zero => exact ⟨trivial, fun index => Fin.elim0 index⟩
  | succ width induction =>
    have head := Expression.compile_valid ((valid 0).mono fits)
    have tail := induction (start := start + ((expressions 0).compile start).1.length)
      (fun index => expressions index.succ) (fun index => valid index.succ) (by omega)
    constructor
    · exact (wellFormed_append _ _ _).mpr ⟨head.1, tail.1⟩
    · intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · simpa only [compileLayer, Fin.cases_zero, List.length_append, Nat.add_assoc] using
          Nat.lt_of_lt_of_le head.2 (Nat.le_add_right _ _)
      · simpa only [compileLayer, Fin.cases_succ, List.length_append, Nat.add_assoc] using tail.2 index

/-- Each layer result equals its expression evaluated before any layer gates
were emitted. Results may share any number of original input wires. -/
theorem compileLayer_correct (width : ℕ) {available start : ℕ}
    (expressions : Fin width → Expression)
    (valid : ∀ index, (expressions index).Valid available) (fits : available ≤ start)
    (values : ℕ → Bool) (index : Fin width) :
    run start (compileLayer width start expressions).1 values
      ((compileLayer width start expressions).2 index) = (expressions index).eval values := by
  induction width generalizing start values with
  | zero => exact Fin.elim0 index
  | succ width induction =>
    let head := (expressions 0).compile start
    let middle := run start head.1 values
    let tail := compileLayer width (start + head.1.length) (fun index => expressions index.succ)
    change run start (head.1 ++ tail.1) values (Fin.cases head.2 tail.2 index) = _
    rw [run_append]
    refine Fin.cases ?_ (fun position => ?_) index
    · change run (start + head.1.length) tail.1 middle head.2 = _
      rw [run_preserves tail.1 _ middle head.2 (Expression.compile_valid ((valid 0).mono fits)).2]
      exact Expression.compile_correct ((valid 0).mono fits) values
    · change run (start + head.1.length) tail.1 middle (tail.2 position) = _
      rw [induction (start := start + head.1.length) (fun index => expressions index.succ)
        (fun index => valid index.succ) (by omega) middle position]
      exact Expression.eval_eq_of_agree (valid position.succ)
        (fun wire bound => run_preserves head.1 start values wire (by omega))

end Polytime2.Circuit
