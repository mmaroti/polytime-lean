import Polytime2.TM0.SourceTrace
import Lean.Elab.Tactic.Omega

/-! # A local presentation of Mathlib TM0 transitions

An absolute tape cell contains its symbol and, at the unique head position,
the current state. One parallel radius-one update simulates a TM0 transition.
Halting configurations stay fixed. This is mathematical simulation of the
same machine used by `PolynomialTime`, not a replacement complexity model.
-/

namespace Polytime2

open Turing SourceTrace

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]

/-- A tape symbol together with an optional head and state marker. -/
abbrev Cell (Symbol State : Type) := Symbol × Option State

/-- Ordinary mathematical dynamics of a finite array of marked cells. -/
def cellTransition {positions : ℕ} (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (contents : Fin positions → Cell Symbol State) : Fin positions → Cell Symbol State :=
  fun position => update position (fun argument => contents (neighbors position argument))

/-- Embed a head-relative Mathlib tape at an absolute integer position. -/
def cells (head : ℤ) (configuration : TM0.Cfg Symbol State) : ℤ → Cell Symbol State :=
  fun position => (configuration.Tape.nth (position - head),
    if position = head then some configuration.q else none)

/-- A neighbor sends a head marker only when its machine action moves in
the specified direction. -/
def incoming (machine : TM0.Machine Symbol State) (direction : Dir)
    (neighbor : Cell Symbol State) : Option State :=
  neighbor.2.bind fun state =>
    (machine state neighbor.1).bind fun action =>
      match action.2 with
      | .write _ => none
      | .move movement => if movement = direction then some action.1 else none

/-- A cell updates from itself and its two neighbors. On well-formed
configurations at most one incoming head exists. -/
def localStep (machine : TM0.Machine Symbol State)
    (left center right : Cell Symbol State) : Cell Symbol State :=
  match center.2 with
  | some state =>
    match machine state center.1 with
    | none => center
    | some (next, .write symbol) => (symbol, some next)
    | some (_, .move _) => (center.1, none)
  | none => (center.1, (incoming machine .right left).or (incoming machine .left right))

/-- Update the absolute head position consistently with a TM0 transition. -/
def advanceHead (machine : TM0.Machine Symbol State) (head : ℤ)
    (configuration : TM0.Cfg Symbol State) : ℤ :=
  match machine configuration.q configuration.Tape.head with
  | some (_, .move .left) => head - 1
  | some (_, .move .right) => head + 1
  | _ => head

theorem incoming_cells (machine : TM0.Machine Symbol State) (direction : Dir)
    (head position : ℤ) (configuration : TM0.Cfg Symbol State) :
    incoming machine direction (cells head configuration position) =
      if position = head then
        (machine configuration.q configuration.Tape.head).bind (fun action =>
          match action.2 with
          | .write _ => none
          | .move movement => if movement = direction then some action.1 else none)
      else none := by
  by_cases equal : position = head
  · subst position
    simp [cells, incoming]
  · simp [cells, incoming, equal]

/-- A radius-one parallel update agrees with one actual Mathlib TM0 step,
including movement in either direction, writing, and absorbing halts. -/
theorem localStep_cells (machine : TM0.Machine Symbol State) (head position : ℤ)
    (configuration : TM0.Cfg Symbol State) :
    localStep machine (cells head configuration (position - 1))
      (cells head configuration position) (cells head configuration (position + 1)) =
      cells (advanceHead machine head configuration) (advance machine configuration) position := by
  classical
  have center : cells head configuration position =
      (configuration.Tape.nth (position - head),
        if position = head then some configuration.q else none) := rfl
  rw [center]
  cases action : machine configuration.q configuration.Tape.head with
  | none =>
    by_cases here : position = head
    · subst position
      simp [localStep, cells, advance, advanceHead, TM0.step, action]
    · simp only [localStep, here, ite_false]
      rw [incoming_cells, incoming_cells]
      simp [action, cells, advance, advanceHead, TM0.step, here]
  | some instruction =>
    obtain ⟨next, instruction⟩ := instruction
    cases instruction with
    | write symbol =>
      by_cases here : position = head
      · subst position
        simp [localStep, cells, advance, advanceHead, TM0.step, action, Tape.write]
      · simp only [localStep, here, ite_false]
        rw [incoming_cells, incoming_cells]
        simp [action, cells, advance, advanceHead, TM0.step, here,
          show position - head ≠ 0 by omega]
    | move direction =>
      cases direction <;> by_cases here : position = head
      all_goals try { subst position; simp [localStep, cells, advance, advanceHead, TM0.step, action] }
      all_goals
        simp only [localStep, here, ite_false]
        rw [incoming_cells, incoming_cells]
        simp [action, cells, advance, advanceHead, TM0.step]
      all_goals try omega
      all_goals constructor
      all_goals try { congr 1; omega }
      all_goals split_ifs <;> first | rfl | (exfalso; omega)

/-- Parallel evolution of an integer-indexed tape of marked cells. -/
def evolve (machine : TM0.Machine Symbol State) (contents : ℤ → Cell Symbol State) :
    ℤ → Cell Symbol State :=
  fun position => localStep machine (contents (position - 1)) (contents position)
    (contents (position + 1))

/-- Keep the absolute head position alongside the original TM0 configuration. -/
def locatedAdvance (machine : TM0.Machine Symbol State)
    (located : ℤ × TM0.Cfg Symbol State) : ℤ × TM0.Cfg Symbol State :=
  (advanceHead machine located.1 located.2, advance machine located.2)

/-- Every bounded parallel trace is exactly a trace of the original machine,
with halted configurations repeated. -/
theorem evolve_iterate (machine : TM0.Machine Symbol State) (steps : ℕ)
    (head : ℤ) (configuration : TM0.Cfg Symbol State) :
    (evolve machine)^[steps] (cells head configuration) =
      cells ((locatedAdvance machine)^[steps] (head, configuration)).1
        ((locatedAdvance machine)^[steps] (head, configuration)).2 := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
    rw [Function.iterate_succ_apply', induction, Function.iterate_succ_apply']
    funext position
    exact localStep_cells machine _ position _

theorem locatedAdvance_iterate_configuration (machine : TM0.Machine Symbol State) (steps : ℕ)
    (head : ℤ) (configuration : TM0.Cfg Symbol State) :
    ((locatedAdvance machine)^[steps] (head, configuration)).2 =
      (advance machine)^[steps] configuration := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
    simp only [Function.iterate_succ_apply', locatedAdvance, induction]

/-- A transition moves the absolute head by at most one cell. -/
theorem advanceHead_bounds (machine : TM0.Machine Symbol State) (head : ℤ)
    (configuration : TM0.Cfg Symbol State) :
    head - 1 ≤ advanceHead machine head configuration ∧
      advanceHead machine head configuration ≤ head + 1 := by
  unfold advanceHead
  cases machine configuration.q configuration.Tape.head with
  | none => simp; omega
  | some instruction =>
    obtain ⟨next, instruction⟩ := instruction
    cases instruction with
    | write symbol => simp; omega
    | move direction => cases direction <;> simp <;> omega

/-- Polynomial-time traces fit in a window whose radius is the time bound. -/
theorem locatedAdvance_head_bounds (machine : TM0.Machine Symbol State) (steps : ℕ)
    (head : ℤ) (configuration : TM0.Cfg Symbol State) :
    head - steps ≤ ((locatedAdvance machine)^[steps] (head, configuration)).1 ∧
      ((locatedAdvance machine)^[steps] (head, configuration)).1 ≤ head + steps := by
  induction steps with
  | zero => simp
  | succ steps induction =>
    rw [Function.iterate_succ_apply']
    have next := advanceHead_bounds machine
      ((locatedAdvance machine)^[steps] (head, configuration)).1
      ((locatedAdvance machine)^[steps] (head, configuration)).2
    change head - (steps + 1 : ℕ) ≤ advanceHead machine _ _ ∧
      advanceHead machine _ _ ≤ head + (steps + 1 : ℕ)
    push_cast
    omega

end Polytime2
