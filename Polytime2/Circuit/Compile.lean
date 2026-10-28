import Polytime2.Circuit.Basic

/-! # Compiling NAND expressions to shared-wire circuits

The compiler appends fresh gates to an existing wire prefix. Its contract
states acyclicity, preservation of that prefix, evaluation correctness, and
an exact gate count. This is a mathematical construction; its polynomial-time
realization is a separate obligation in the bounded-machine compiler.
-/

namespace Polytime2.Circuit

/-- Boolean expressions used to describe a fixed finite transition table.
Compiled circuits refer to wires instead of recursively copying expressions. -/
inductive Expression where
  | wire (index : ℕ)
  | constant (value : Bool)
  | nand (left right : Expression)

namespace Expression

def eval (expression : Expression) (values : ℕ → Bool) : Bool :=
  match expression with
  | .wire index => values index
  | .constant value => value
  | .nand left right => !(left.eval values && right.eval values)

def Valid (available : ℕ) (expression : Expression) : Prop :=
  match expression with
  | .wire index => index < available
  | .constant _ => True
  | .nand left right => left.Valid available ∧ right.Valid available

/-- Constants and NANDs each emit one gate; wire references emit none. -/
def gateCount (expression : Expression) : ℕ :=
  match expression with
  | .wire _ => 0
  | .constant _ => 1
  | .nand left right => left.gateCount + right.gateCount + 1

/-- Substitute wire names without duplicating the expressions defining them. -/
def rename (names : ℕ → ℕ) (expression : Expression) : Expression :=
  match expression with
  | .wire index => .wire (names index)
  | .constant value => .constant value
  | .nand left right => .nand (left.rename names) (right.rename names)

theorem rename_eval (names : ℕ → ℕ) (expression : Expression) (values : ℕ → Bool) :
    (expression.rename names).eval values = expression.eval (values ∘ names) := by
  induction expression with
  | wire index => rfl
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    simp only [rename, eval, leftInduction, rightInduction]

theorem rename_gateCount (names : ℕ → ℕ) (expression : Expression) :
    (expression.rename names).gateCount = expression.gateCount := by
  induction expression with
  | wire index => rfl
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    simp only [rename, gateCount, leftInduction, rightInduction]

theorem rename_valid {expression : Expression} {source target : ℕ}
    (valid : expression.Valid source) (names : ℕ → ℕ)
    (bounded : ∀ wire < source, names wire < target) :
    (expression.rename names).Valid target := by
  induction expression with
  | wire index => exact bounded index valid
  | constant value => trivial
  | nand left right leftInduction rightInduction =>
    exact ⟨leftInduction valid.1, rightInduction valid.2⟩

/-- Renaming depends only on the input references occurring in a valid expression. -/
theorem rename_eq_of_agree {expression : Expression} {available : ℕ}
    (valid : expression.Valid available) (first second : ℕ → ℕ)
    (agree : ∀ wire < available, first wire = second wire) :
    expression.rename first = expression.rename second := by
  induction expression with
  | wire index => exact congrArg Expression.wire (agree index valid)
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    exact congrArg₂ Expression.nand (leftInduction valid.1) (rightInduction valid.2)

/-- Compile into the fresh wires starting at `start`, returning the selected
output wire alongside the emitted gates. -/
def compile (start : ℕ) (expression : Expression) : Network :=
  match expression with
  | .wire index => ([], index)
  | .constant value => ([.inl value], start)
  | .nand left right =>
    let first := left.compile start
    let second := right.compile (start + first.1.length)
    (first.1 ++ second.1 ++ [.inr (first.2, second.2)],
      start + first.1.length + second.1.length)

theorem compile_length (expression : Expression) (start : ℕ) :
    (expression.compile start).1.length = expression.gateCount := by
  induction expression generalizing start with
  | wire index => rfl
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    simp [compile, gateCount, leftInduction, rightInduction, Nat.add_assoc]

theorem Valid.mono {expression : Expression} {start larger : ℕ}
    (valid : expression.Valid start) (bounded : start ≤ larger) : expression.Valid larger := by
  induction expression with
  | wire index => exact Nat.lt_of_lt_of_le valid bounded
  | constant value => trivial
  | nand left right leftInduction rightInduction =>
    exact ⟨leftInduction valid.1, rightInduction valid.2⟩

theorem eval_eq_of_agree {expression : Expression} {start : ℕ}
    (valid : expression.Valid start) {first second : ℕ → Bool}
    (agree : ∀ wire < start, first wire = second wire) :
    expression.eval first = expression.eval second := by
  induction expression with
  | wire index => exact agree index valid
  | constant value => rfl
  | nand left right leftInduction rightInduction =>
    exact congrArg₂ (fun a b => !(a && b)) (leftInduction valid.1) (rightInduction valid.2)

/-- Compilation yields a circuit whose every reference is defined. -/
theorem compile_valid {expression : Expression} {start : ℕ}
    (valid : expression.Valid start) : Circuit.Valid start (expression.compile start) := by
  induction expression generalizing start with
  | wire index => exact ⟨trivial, valid⟩
  | constant value => exact ⟨⟨trivial, trivial⟩, by simp [compile]⟩
  | nand left right leftInduction rightInduction =>
    obtain ⟨firstValid, firstOutput⟩ := leftInduction valid.1
    obtain ⟨secondValid, secondOutput⟩ := rightInduction
      (valid.2.mono (Nat.le_add_right start (left.compile start).1.length))
    constructor
    · simp only [compile, wellFormed_append, List.length_append]
      refine ⟨⟨firstValid, secondValid⟩, ?_⟩
      change (_ < _ ∧ _ < _) ∧ True
      exact ⟨⟨by omega, by omega⟩, trivial⟩
    · simp only [compile, List.length_append, List.length_singleton]
      omega

/-- The emitted output equals the expression on the original wire values. -/
theorem compile_correct {expression : Expression} {start : ℕ}
    (valid : expression.Valid start) (values : ℕ → Bool) :
    run start (expression.compile start).1 values (expression.compile start).2 =
      expression.eval values := by
  induction expression generalizing start values with
  | wire index => rfl
  | constant value => simp [compile, run, Gate.eval, eval]
  | nand left right leftInduction rightInduction =>
    let first := left.compile start
    let middle := run start first.1 values
    let second := right.compile (start + first.1.length)
    let final := run (start + first.1.length) second.1 middle
    have leftBound := (compile_valid valid.1).2
    have leftValue : final first.2 = left.eval values := by
      rw [show final first.2 = middle first.2 from
        run_preserves second.1 _ middle first.2 leftBound]
      exact leftInduction valid.1 values
    have rightValue : final second.2 = right.eval values := by
      change run (start + first.1.length) (right.compile (start + first.1.length)).1
        middle (right.compile (start + first.1.length)).2 = _
      rw [rightInduction (valid.2.mono (Nat.le_add_right start first.1.length)) middle]
      exact eval_eq_of_agree valid.2 (fun wire bound => run_preserves first.1 start values wire bound)
    change run start (first.1 ++ second.1 ++ [.inr (first.2, second.2)]) values
      (start + first.1.length + second.1.length) = _
    rw [run_append, run_append]
    simp only [List.length_append, run, Nat.add_assoc, Function.update_self, Gate.eval]
    change (!(final first.2 && final second.2) : Bool) = _
    rw [leftValue, rightValue]
    rfl

/-- Every expression emitting gates selects its last emitted wire. -/
theorem compile_output (expression : Expression) (start : ℕ)
    (positive : 0 < expression.gateCount) :
    (expression.compile start).2 + 1 = start + expression.gateCount := by
  cases expression with
  | wire index => simp [gateCount] at positive
  | constant value => rfl
  | nand left right =>
    simp only [compile, compile_length, gateCount]
    omega


end Expression

end Polytime2.Circuit
