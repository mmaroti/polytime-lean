import Polytime2.TM0.LocalMachine

/-! # Finite windows for bounded machine simulation

Truncating a radius-one parallel computation to a finite interval cannot
affect a cell until a signal from the boundary can reach it. A window of
radius twice the time allowance therefore preserves every cell at which the
machine head could finish. No bound on the original input word length is
needed for this locality argument.
-/

namespace Polytime2

open Turing

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]

/-- Retain precisely the cells of a symmetric finite interval. Outside that
interval the tape has blank symbols and no head marker. -/
def window (radius : ℕ) (contents : ℤ → Cell Symbol State) : ℤ → Cell Symbol State :=
  fun position => if -(radius : ℤ) ≤ position ∧ position ≤ radius then contents position
    else (default, none)

/-- A local transition followed by finite-window truncation. -/
def windowEvolve (machine : TM0.Machine Symbol State) (radius : ℕ)
    (contents : ℤ → Cell Symbol State) : ℤ → Cell Symbol State :=
  window radius (evolve machine contents)

/-- Boundary effects propagate by at most one cell per time step. The
initial tape is unrestricted, including symbols outside the retained window. -/
theorem windowEvolve_agree (machine : TM0.Machine Symbol State) (radius steps : ℕ)
    (contents : ℤ → Cell Symbol State) (position : ℤ)
    (inside : -(radius : ℤ) + steps ≤ position ∧ position ≤ (radius : ℤ) - steps) :
    (windowEvolve machine radius)^[steps] (window radius contents) position =
      (evolve machine)^[steps] contents position := by
  induction steps generalizing position with
  | zero => simpa [window] using
      (ite_eq_left (show -(radius : ℤ) ≤ position ∧ position ≤ radius by simpa using inside) :
        (if -(radius : ℤ) ≤ position ∧ position ≤ radius then contents position else (default, none)) = _)
  | succ steps induction =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (if -(radius : ℤ) ≤ position ∧ position ≤ radius then _ else _) = _
    rw [ite_eq_left (by constructor <;> omega)]
    simp only [evolve]
    rw [induction (position - 1) (by constructor <;> omega),
      induction position (by constructor <;> omega),
      induction (position + 1) (by constructor <;> omega)]

/-- Radius twice the time allowance is sufficient to observe every possible
final head position. This is a linear-size spatial window. -/
theorem windowEvolve_agree_head_range (machine : TM0.Machine Symbol State) (steps : ℕ)
    (contents : ℤ → Cell Symbol State) (position : ℤ)
    (bounded : -(steps : ℤ) ≤ position ∧ position ≤ steps) :
    (windowEvolve machine (2 * steps))^[steps] (window (2 * steps) contents) position =
      (evolve machine)^[steps] contents position := by
  apply windowEvolve_agree
  constructor <;> push_cast <;> omega

/-- Truncation cannot create a head outside the source's reachable interval. -/
theorem windowEvolve_no_head_outside (machine : TM0.Machine Symbol State)
    (radius steps : ℕ) (configuration : TM0.Cfg Symbol State) (position : ℤ)
    (outside : position < -(steps : ℤ) ∨ (steps : ℤ) < position) :
    (((windowEvolve machine radius)^[steps] (window radius (cells 0 configuration))) position).2 = none := by
  induction steps generalizing position with
  | zero =>
    have away : position ≠ 0 := by omega
    simp [window, cells, away]
    split_ifs <;> rfl
  | succ steps hypothesis =>
    rw [Function.iterate_succ_apply']
    simp only [windowEvolve, window]
    split_ifs with inside
    · simp only [evolve, localStep, hypothesis position (by omega), incoming,
        hypothesis (position - 1) (by omega), hypothesis (position + 1) (by omega), Option.bind_none,
        Option.or_none]
    · rfl

end Polytime2
