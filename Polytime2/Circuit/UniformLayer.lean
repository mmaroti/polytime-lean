import Polytime2.Circuit.Layer

/-! # Uniform blocks in a circuit layer

Local transition tables all have the same fixed gate count. Their layer can
therefore be tabulated as fixed-size blocks at arithmetic offsets, rather
than constructed by runtime list concatenation and expression traversal.
These equations identify that array construction with the existing compiler.
-/

namespace Polytime2.Circuit

theorem compileLayer_uniform_length (width start blockSize : ℕ) (expressions : Fin width → Expression)
    (uniform : ∀ index, (expressions index).gateCount = blockSize) :
    (compileLayer width start expressions).1.length = width * blockSize := by
  rw [compileLayer_length]
  simp only [uniform, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- One fixed-size block per output, at a directly computed starting wire. -/
theorem compileLayer_uniform_gates (width start blockSize : ℕ) (expressions : Fin width → Expression)
    (uniform : ∀ index, (expressions index).gateCount = blockSize) :
    (compileLayer width start expressions).1 =
      (List.ofFn (fun index => ((expressions index).compile (start + index.val * blockSize)).1)).flatten := by
  induction width generalizing start with
  | zero => rfl
  | succ width induction =>
    simp only [compileLayer, List.ofFn_succ, List.flatten_cons, Fin.val_zero, Nat.zero_mul, Nat.add_zero,
      Expression.compile_length, uniform]
    rw [induction _ (fun index => expressions index.succ) (fun index => uniform index.succ)]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext index
    congr 2
    simp only [Fin.val_succ, Nat.add_mul, Nat.one_mul]
    omega

/-- A compiled local block ends at an explicitly computed wire coordinate. -/
theorem compileLayer_uniform_output (width start blockSize : ℕ) (expressions : Fin width → Expression)
    (uniform : ∀ index, (expressions index).gateCount = blockSize) (positive : 0 < blockSize)
    (index : Fin width) :
    (compileLayer width start expressions).2 index + 1 = start + (index.val + 1) * blockSize := by
  induction width generalizing start with
  | zero => exact Fin.elim0 index
  | succ width induction =>
    refine Fin.cases ?_ (fun position => ?_) index
    · simpa only [compileLayer, Fin.cases_zero, Fin.val_zero, Nat.zero_add, Nat.one_mul, uniform] using
        Expression.compile_output (expressions 0) start (by rw [uniform]; exact positive)
    · simp only [compileLayer, Fin.cases_succ, Expression.compile_length, uniform]
      rw [induction _ (fun index => expressions index.succ) (fun index => uniform index.succ) position]
      simp only [Fin.val_succ, Nat.add_mul, Nat.one_mul]
      omega

end Polytime2.Circuit
