import Polytime2.Complexity.CookLevin.CellCircuit
import Polytime2.Complexity.CookLevin.Window

/-! # Finite array realization of the mathematical tape window

The interval from `-radius` through `radius` is an ordinary finite array.
Clamped neighbor indices stay inside that array; the boundary update supplies
blank, unmarked cells for the missing neighbors. These are mathematical
coordinates, independently of a circuit codec or machine implementation.
-/

namespace Polytime2.Complexity.CookLevin

open Turing

variable {Symbol State : Type} [Inhabited Symbol]

def windowPosition (radius : ℕ) (index : Fin (2 * radius + 1)) : ℤ :=
  (index.val : ℤ) - radius

def windowArray (radius : ℕ) (contents : ℤ → Cell Symbol State) :
    Fin (2 * radius + 1) → Cell Symbol State :=
  fun index => contents (windowPosition radius index)

theorem windowPosition_surjective (radius : ℕ) (position : ℤ)
    (inside : -(radius : ℤ) ≤ position ∧ position ≤ radius) :
    ∃ index : Fin (2 * radius + 1), windowPosition radius index = position := by
  refine ⟨⟨(position + radius).toNat, by omega⟩, ?_⟩
  dsimp [windowPosition]
  omega

theorem window_at_position (radius : ℕ) (contents : ℤ → Cell Symbol State)
    (index : Fin (2 * radius + 1)) :
    window radius contents (windowPosition radius index) = contents (windowPosition radius index) := by
  have inside : -(radius : ℤ) ≤ windowPosition radius index ∧ windowPosition radius index ≤ radius := by
    dsimp [windowPosition]
    have bounded := index.isLt
    constructor <;> omega
  simp [window, inside]

theorem window_idempotent (radius : ℕ) (contents : ℤ → Cell Symbol State) :
    window radius (window radius contents) = window radius contents := by
  funext position
  by_cases inside : -(radius : ℤ) ≤ position ∧ position ≤ radius
  · simp only [window, ite_eq_left inside]
  · simp only [window, ite_eq_right inside]

/-- Left, center, and right neighbors, with safe indices at both boundaries. -/
def windowNeighbors (radius : ℕ) (index : Fin (2 * radius + 1)) :
    Fin 3 → Fin (2 * radius + 1) :=
  fun argument => if argument.val = 0 then ⟨index.val - 1, by omega⟩
    else if argument.val = 1 then index
    else ⟨min (index.val + 1) (2 * radius), by omega⟩

/-- Missing neighbors contribute blank symbols without head markers. -/
def windowUpdate [Inhabited State] (machine : TM0.Machine Symbol State) (radius : ℕ)
    (index : Fin (2 * radius + 1)) (neighbors : Fin 3 → Cell Symbol State) : Cell Symbol State :=
  localStep machine (if index.val = 0 then (default, none) else neighbors 0) (neighbors 1)
    (if index.val = 2 * radius then (default, none) else neighbors 2)

theorem window_left (radius : ℕ) (contents : ℤ → Cell Symbol State)
    (index : Fin (2 * radius + 1)) :
    (if index.val = 0 then (default, none)
      else windowArray radius contents (windowNeighbors radius index 0)) =
      window radius contents (windowPosition radius index - 1) := by
  have bounded := index.isLt
  by_cases zero : index.val = 0
  · have outside : ¬ (-(radius : ℤ) ≤ windowPosition radius index - 1 ∧
        windowPosition radius index - 1 ≤ radius) := by dsimp [windowPosition]; omega
    simp only [zero, ite_true, window, ite_eq_right outside]
  · have inside : -(radius : ℤ) ≤ windowPosition radius index - 1 ∧
        windowPosition radius index - 1 ≤ radius := by dsimp [windowPosition]; constructor <;> omega
    simp only [zero, ite_false, windowArray, windowNeighbors, Fin.val_zero, ite_true, window,
      ite_eq_left inside]
    congr 1
    dsimp [windowPosition]
    omega

theorem window_right (radius : ℕ) (contents : ℤ → Cell Symbol State)
    (index : Fin (2 * radius + 1)) :
    (if index.val = 2 * radius then (default, none)
      else windowArray radius contents (windowNeighbors radius index 2)) =
      window radius contents (windowPosition radius index + 1) := by
  have bounded := index.isLt
  by_cases last : index.val = 2 * radius
  · have outside : ¬ (-(radius : ℤ) ≤ windowPosition radius index + 1 ∧
        windowPosition radius index + 1 ≤ radius) := by dsimp [windowPosition]; omega
    simp only [last, ite_true, window, ite_eq_right outside]
  · have inside : -(radius : ℤ) ≤ windowPosition radius index + 1 ∧
        windowPosition radius index + 1 ≤ radius := by dsimp [windowPosition]; constructor <;> omega
    simp [last, windowArray, windowNeighbors, window, inside,
      Nat.min_eq_left (show index.val + 1 ≤ 2 * radius by omega)]
    congr 1
    dsimp [windowPosition]
    omega

/-- The finite array transition is precisely the truncated parallel TM0
transition. In particular, no tape support or padding invariant is assumed. -/
theorem windowArray_step [Inhabited State] (machine : TM0.Machine Symbol State) (radius : ℕ)
    (contents : ℤ → Cell Symbol State) :
    cellTransition (windowNeighbors radius) (windowUpdate machine radius) (windowArray radius contents) =
      windowArray radius (windowEvolve machine radius (window radius contents)) := by
  funext index
  simp only [cellTransition, windowUpdate]
  rw [window_left, window_right]
  change localStep machine _ (contents (windowPosition radius index)) _ = _
  simp only [windowArray, windowEvolve, window_at_position, evolve]

theorem windowArray_window (radius : ℕ) (contents : ℤ → Cell Symbol State) :
    windowArray radius (window radius contents) = windowArray radius contents := by
  funext index
  exact window_at_position radius contents index

theorem windowEvolve_closed [Inhabited State] (machine : TM0.Machine Symbol State)
    (radius steps : ℕ) (contents : ℤ → Cell Symbol State) :
    window radius ((windowEvolve machine radius)^[steps] (window radius contents)) =
      (windowEvolve machine radius)^[steps] (window radius contents) := by
  cases steps with
  | zero => exact window_idempotent radius contents
  | succ steps =>
    rw [Function.iterate_succ_apply']
    exact window_idempotent radius _

/-- Finite array dynamics simulate every time step of the truncated tape. -/
theorem windowArray_iterate [Inhabited State] (machine : TM0.Machine Symbol State)
    (radius steps : ℕ) (contents : ℤ → Cell Symbol State) :
    (cellTransition (windowNeighbors radius) (windowUpdate machine radius))^[steps]
        (windowArray radius contents) =
      windowArray radius ((windowEvolve machine radius)^[steps] (window radius contents)) := by
  induction steps with
  | zero => exact (windowArray_window radius contents).symm
  | succ steps induction =>
    rw [Function.iterate_succ_apply', induction, windowArray_step, windowEvolve_closed,
      Function.iterate_succ_apply']

end Polytime2.Complexity.CookLevin
