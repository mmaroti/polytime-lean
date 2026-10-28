import Polytime2.Circuit.Observe
import Polytime2.Circuit.UniformLayer
import Mathlib.Tactic.Ring

/-! # Exact block layout of conjunction compilation

Each selector contributes one prefix copy. After the terminal true constant,
reverse-order suffix blocks contain its remaining two copies and five gates.
-/

namespace Polytime2.Circuit.Expression

/-- The part of a conjunction step emitted after the selector and tail.
Its two supplied wires are the already computed selector and tail values. -/
def conjunctionTail (expression : Expression) (selected tail : ℕ) : Expression :=
  .nand (.nand (.wire selected) (.wire tail))
    (.nand (.nand expression expression) (.constant false))

theorem conjunctionTail_valid {expression : Expression} {selected tail available : ℕ}
    (valid : expression.Valid available) (selectedBound : selected < available) (tailBound : tail < available) :
    (conjunctionTail expression selected tail).Valid available :=
  ⟨⟨selectedBound, tailBound⟩, ⟨⟨valid, valid⟩, trivial⟩⟩

theorem conjunctionTail_rename (expression : Expression) (selected tail : ℕ) (names : ℕ → ℕ) :
    (conjunctionTail expression selected tail).rename names =
      conjunctionTail (expression.rename names) (names selected) (names tail) := rfl

theorem conjunctionTail_gateCount (expression : Expression) (selected tail : ℕ) :
    (conjunctionTail expression selected tail).gateCount = 2 * expression.gateCount + 5 := by
  simp only [conjunctionTail, gateCount]
  omega

theorem allExpressions_compile_cons (expression : Expression) (rest : List Expression) (start : ℕ) :
    ((allExpressions (expression :: rest)).compile start).1 =
      (expression.compile start).1 ++
      ((allExpressions rest).compile (start + expression.gateCount)).1 ++
      ((conjunctionTail expression (expression.compile start).2
        ((allExpressions rest).compile (start + expression.gateCount)).2).compile
          (start + expression.gateCount + (allExpressions rest).gateCount)).1 := by
  simp only [allExpressions, select, conjunctionTail, compile, compile_length, gateCount,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero, List.nil_append,
    List.append_nil, List.append_assoc, Nat.add_assoc]

/-- Exact flat layout for a conjunction of equal-size positive expressions. -/
theorem allExpressions_compile_blocks {length : ℕ} (expressions : Fin length → Expression)
    (count : ℕ) (positive : 0 < count) (counts : ∀ index, (expressions index).gateCount = count)
    (start : ℕ) :
    ((allExpressions (List.ofFn expressions)).compile start).1 =
      (List.ofFn (fun index => ((expressions index).compile (start + count * index.val)).1)).flatten ++
      [.inl true] ++
      (List.ofFn (fun index =>
        ((conjunctionTail (expressions index.rev)
          (start + count * index.rev.val + count - 1)
          (start + count * length + (2 * count + 5) * index.val)).compile
          (start + count * length + 1 + (2 * count + 5) * index.val)).1)).flatten := by
  induction length generalizing start with
  | zero => rfl
  | succ length induction =>
    have restCount : (allExpressions (List.ofFn (fun index : Fin length => expressions index.succ))).gateCount =
        3 * (length * count) + 5 * length + 1 := by
      rw [allExpressions_gateCount, List.map_ofFn]
      simp only [Function.comp_def, counts]
      simp
    have firstOutput : ((expressions 0).compile start).2 = start + count - 1 := by
      have output := compile_output (expressions 0) start (by rw [counts]; exact positive)
      rw [counts] at output
      omega
    have restOutput : ((allExpressions (List.ofFn (fun index : Fin length => expressions index.succ))).compile
        (start + count)).2 = start + count * (length + 1) + (2 * count + 5) * length := by
      have output := compile_output (allExpressions (List.ofFn (fun index : Fin length => expressions index.succ)))
        (start + count) (by rw [restCount]; omega)
      rw [restCount] at output
      have arithmetic : start + count + (3 * (length * count) + 5 * length + 1) =
          (start + count * (length + 1) + (2 * count + 5) * length) + 1 := by ring
      omega
    have lastBase : start + count + (3 * (length * count) + 5 * length + 1) =
        start + count * (length + 1) + 1 + (2 * count + 5) * length := by ring
    rw [List.ofFn_succ, allExpressions_compile_cons]
    rw [counts, firstOutput, restOutput, restCount, lastBase]
    rw [induction (fun index => expressions index.succ) (fun index => counts index.succ) (start + count)]
    rw [List.ofFn_succ, List.ofFn_succ']
    simp only [List.flatten_cons, List.flatten_append, List.concat_eq_append,
      Fin.val_zero, Nat.mul_zero, Nat.add_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
      Fin.rev_castSucc, Fin.rev_last]
    have prefixes : (List.ofFn (fun index : Fin length =>
        ((expressions index.succ).compile (start + count + count * index.val)).1)).flatten =
        (List.ofFn (fun index : Fin length =>
          ((expressions index.succ).compile (start + count * (index.val + 1))).1)).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      congr 2
      ring
    rw [prefixes]
    have suffixes : (List.ofFn (fun index : Fin length =>
        ((conjunctionTail (expressions index.rev.succ)
          (start + count + count * index.rev.val + count - 1)
          (start + count + count * length + (2 * count + 5) * index.val)).compile
          (start + count + count * length + 1 + (2 * count + 5) * index.val)).1)) =
        (List.ofFn (fun index : Fin length =>
          ((conjunctionTail (expressions index.rev.succ)
            (start + count * (index.rev.val + 1) + count - 1)
            (start + count * (length + 1) + (2 * count + 5) * index.val)).compile
            (start + count * (length + 1) + 1 + (2 * count + 5) * index.val)).1)) := by
      apply congrArg List.ofFn
      funext index
      have selected : start + count + count * index.rev.val + count - 1 =
          start + count * (index.rev.val + 1) + count - 1 := by congr 1; ring
      have tail : start + count + count * length + (2 * count + 5) * index.val =
          start + count * (length + 1) + (2 * count + 5) * index.val := by ring
      have base : start + count + count * length + 1 + (2 * count + 5) * index.val =
          start + count * (length + 1) + 1 + (2 * count + 5) * index.val := by ring
      rw [selected, tail, base]
    rw [suffixes]
    simp only [List.flatten_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

end Polytime2.Circuit.Expression
