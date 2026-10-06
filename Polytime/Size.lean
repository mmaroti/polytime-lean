import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! # Size parameters

`none` names the primary parameter N; `some k` names an auxiliary parameter.
Bounds concern admissible assignments, not the definition of domain values.
-/

namespace Polytime

structure SizeContext (Param : Type) [Fintype Param] where
  bound : Param → Polynomial ℕ

structure SizeAssignment (Param : Type) where
  N : ℕ
  auxiliary : Param → ℕ

namespace SizeAssignment

def valuation (a : SizeAssignment Param) : Option Param → ℕ
  | none => a.N
  | some k => a.auxiliary k

end SizeAssignment

namespace SizeContext

def Admissible [Fintype Param] (ctx : SizeContext Param) (a : SizeAssignment Param) : Prop :=
  ∀ k, a.auxiliary k ≤ (ctx.bound k).eval a.N

end SizeContext

abbrev SizeExpr (Param : Type) := MvPolynomial (Option Param) ℕ

namespace SizeExpr

noncomputable section

def main : SizeExpr Param := MvPolynomial.X none
def parameter (k : Param) : SizeExpr Param := MvPolynomial.X (some k)
def constant (n : ℕ) : SizeExpr Param := MvPolynomial.C n

def eval (e : SizeExpr Param) (a : SizeAssignment Param) : ℕ :=
  MvPolynomial.eval a.valuation e

def envelope [Fintype Param] (e : SizeExpr Param) (ctx : SizeContext Param) : Polynomial ℕ :=
  e.eval₂ Polynomial.C (fun | none => Polynomial.X | some k => ctx.bound k)

@[simp] theorem eval_main (a : SizeAssignment Param) : eval main a = a.N := by
  simp [eval, main, SizeAssignment.valuation]

@[simp] theorem eval_parameter (k : Param) (a : SizeAssignment Param) :
    eval (parameter k) a = a.auxiliary k := by
  simp [eval, parameter, SizeAssignment.valuation]

@[simp] theorem eval_constant (n : ℕ) (a : SizeAssignment Param) : eval (constant n) a = n := by
  simp [eval, constant]

@[simp] theorem eval_add (e f : SizeExpr Param) (a : SizeAssignment Param) :
    eval (e + f) a = eval e a + eval f a := by simp [eval]

@[simp] theorem eval_mul (e f : SizeExpr Param) (a : SizeAssignment Param) :
    eval (e * f) a = eval e a * eval f a := by simp [eval]

@[simp] theorem eval_pow (e : SizeExpr Param) (n : ℕ) (a : SizeAssignment Param) :
    eval (e ^ n) a = eval e a ^ n := by simp [eval]

theorem eval_mono (e : SizeExpr Param) (a b : Option Param → ℕ) (h : ∀ k, a k ≤ b k) :
    MvPolynomial.eval a e ≤ MvPolynomial.eval b e := by
  induction e using MvPolynomial.induction_on with
  | C n => simp
  | add e f he hf => simpa using Nat.add_le_add he hf
  | mul_X e k he => simpa using Nat.mul_le_mul he (h k)

theorem eval_le_envelope [Fintype Param] (e : SizeExpr Param) (ctx : SizeContext Param)
    (a : SizeAssignment Param) (ha : ctx.Admissible a) :
    e.eval a ≤ (e.envelope ctx).eval a.N := by
  have heq : (e.envelope ctx).eval a.N =
      MvPolynomial.eval (fun | none => a.N | some k => (ctx.bound k).eval a.N) e := by
    induction e using MvPolynomial.induction_on with
    | C n => simp [envelope]
    | add e f he hf => simpa [envelope] using congrArg₂ (· + ·) he hf
    | mul_X e k he => cases k <;> simp_all [envelope]
  rw [heq]
  apply eval_mono
  intro k
  cases k with
  | none => exact le_rfl
  | some k => exact ha k

end
end SizeExpr
end Polytime
