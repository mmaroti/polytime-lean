import Polytime2.Circuit.Observe
import Polytime2.Circuit.UniformLayer

/-! # Directly indexed disjunction observer gates

A disjunction compiler emits three prefix gates per observed wire, one false
constant, and two suffix gates per wire in reverse order. These formulas let
the uniform constructor tabulate gates without traversing expression trees.
-/

namespace Polytime2.Circuit.Expression

private theorem anyWire_compile_cons (wire : ℕ) (rest : List ℕ) (start : ℕ) :
    ((anyWire (wire :: rest)).compile start).1 =
      [.inl true, .inr (wire, start), .inr (wire, wire)] ++
        ((anyWire rest).compile (start + 3)).1 ++
        [.inr (start + 2, start + 3 + 5 * rest.length),
          .inr (start + 1, start + 5 * rest.length + 4)] := by
  have output := compile_output (anyWire rest) (start + 3) (by rw [anyWire_gateCount]; omega)
  rw [anyWire_gateCount] at output
  have result : ((anyWire rest).compile (start + 3)).2 = start + 3 + 5 * rest.length := by omega
  change ((select (.wire wire) (.constant true) (anyWire rest)).compile start).1 = _
  simp only [select, compile, compile_length, anyWire_gateCount,
    List.length_cons, List.length_nil, Nat.add_zero, Nat.add_assoc, result, List.nil_append, List.append_nil, List.cons_append, List.append_assoc]
  simp only [List.cons.injEq, List.append_cancel_left_eq, Sum.inr.injEq, Prod.mk.injEq, true_and, and_true]
  omega

/-- Exact prefix, constant, and reversed-suffix layout of a disjunction. -/
theorem anyWire_compile_blocks {length : ℕ} (wires : Fin length → ℕ) (start : ℕ) :
    ((anyWire (List.ofFn wires)).compile start).1 =
      (List.ofFn (fun index : Fin length =>
        [.inl true, .inr (wires index, start + 3 * index.val), .inr (wires index, wires index)])).flatten ++
      [.inl false] ++
      (List.ofFn (fun index : Fin length =>
        [.inr (start + 3 * (length - 1 - index.val) + 2, start + 3 * length + 2 * index.val),
          .inr (start + 3 * (length - 1 - index.val) + 1, start + 3 * length + 2 * index.val + 1)])).flatten := by
  induction length generalizing start with
  | zero => rfl
  | succ length induction =>
    rw [List.ofFn_succ, anyWire_compile_cons, induction]
    rw [List.ofFn_succ, List.ofFn_succ']
    simp only [List.flatten_cons, List.flatten_append, List.concat_eq_append, List.length_ofFn,
      Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Nat.mul_zero, Nat.add_zero]
    have prefixesEqual : (List.ofFn (fun index : Fin length =>
        [.inl true, Sum.inr (wires index.succ, start + 3 + 3 * index.val),
          .inr (wires index.succ, wires index.succ)])).flatten =
      (List.ofFn (fun index : Fin length =>
        [.inl true, Sum.inr (wires index.succ, start + 3 * (index.val + 1)),
          .inr (wires index.succ, wires index.succ)])).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext index
      simp only [List.cons.injEq, Sum.inr.injEq, Prod.mk.injEq, true_and, and_true]
      omega
    have suffixesEqual : (List.ofFn (fun index : Fin length =>
        ([Sum.inr (start + 3 + 3 * (length - 1 - index.val) + 2, start + 3 + 3 * length + 2 * index.val),
          Sum.inr (start + 3 + 3 * (length - 1 - index.val) + 1, start + 3 + 3 * length + 2 * index.val + 1)] : List Gate))) =
      List.ofFn (fun index : Fin length =>
        [.inr (start + 3 * (length + 1 - 1 - index.val) + 2, start + 3 * (length + 1) + 2 * index.val),
          .inr (start + 3 * (length + 1 - 1 - index.val) + 1, start + 3 * (length + 1) + 2 * index.val + 1)]) := by
      apply congrArg List.ofFn
      funext index
      have bounded := index.isLt
      simp only [List.cons.injEq, Sum.inr.injEq, Prod.mk.injEq, and_true]
      repeat' constructor <;> omega
    rw [prefixesEqual, suffixesEqual]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.flatten_nil, List.append_nil]
    simp only [List.cons.injEq, List.append_cancel_left_eq, Sum.inr.injEq, Prod.mk.injEq, true_and, and_true]
    repeat' constructor <;> omega

end Polytime2.Circuit.Expression
