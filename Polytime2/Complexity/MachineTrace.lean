import Polytime2.TM0.FiniteWindow
import Polytime2.Complexity.PolynomialTime

/-! # Bounded local simulation of certified word-machine traces

The polynomial-time contract stops at the actual halting time. Circuit
unrolling uses a predetermined time allowance. Absorbing halts bridge those
two conventions without adding any runtime hypothesis.
-/

namespace Polytime2.Complexity

open Turing SourceTrace

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]

/-- The existing exact word-machine certificate supplies the full canonical
output at its time allowance, not merely at an existential halting time. -/
theorem runs_advance (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter → Symbol) (input output : Word) (allowance : ℕ)
    (runs : Internal.Runs machine entry letters input output allowance) :
    ∃ finalState, (advance machine)^[allowance]
      ⟨entry, Tape.mk₁ (input.map letters)⟩ =
        ⟨finalState, Tape.mk₁ (output.map letters)⟩ ∧
      TM0.step machine ⟨finalState, Tape.mk₁ (output.map letters)⟩ = none := by
  obtain ⟨ticks, finalState, bounded, trace, halt⟩ := runs
  exact ⟨finalState, advance_iterate_of_halted_trace machine bounded trace halt, halt⟩

/-- A certified word computation is simulated by local parallel evolution
throughout its full allowance. Its absolute final head lies in the interval
given by `locatedAdvance_head_bounds`. -/
theorem runs_evolve (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter → Symbol) (input output : Word) (allowance : ℕ)
    (runs : Internal.Runs machine entry letters input output allowance) :
    ∃ head finalState,
      -(allowance : ℤ) ≤ head ∧ head ≤ allowance ∧
      (evolve machine)^[allowance] (cells 0 ⟨entry, Tape.mk₁ (input.map letters)⟩) =
        cells head ⟨finalState, Tape.mk₁ (output.map letters)⟩ := by
  obtain ⟨finalState, finalConfiguration, _halt⟩ := runs_advance machine entry letters input output allowance runs
  let initial : TM0.Cfg Symbol State := ⟨entry, Tape.mk₁ (input.map letters)⟩
  let head := ((locatedAdvance machine)^[allowance] (0, initial)).1
  have bounded := locatedAdvance_head_bounds machine allowance 0 initial
  refine ⟨head, finalState, by simpa using bounded.1, by simpa using bounded.2, ?_⟩
  rw [evolve_iterate, locatedAdvance_iterate_configuration, finalConfiguration]

/-- A Boolean-output certificate is accepted precisely by a marked accepting
cell in the reachable interval of the infinite local evolution. -/
theorem runs_accepting (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (input : Word) (answer : Bool) (allowance : ℕ)
    (runs : Internal.Runs machine entry letters input [Sum.inl answer] allowance) :
    (∃ position, (-(allowance : ℤ) ≤ position ∧ position ≤ allowance) ∧
      ∃ state, (evolve machine)^[allowance] (cells 0 ⟨entry, Tape.mk₁ (input.map letters)⟩) position =
        (letters (Sum.inl true), some state)) ↔ answer = true := by
  obtain ⟨head, finalState, lower, upper, trace⟩ := runs_evolve machine entry letters input
    [Sum.inl answer] allowance runs
  rw [trace]
  constructor
  · rintro ⟨position, _inside, state, equal⟩
    have marker := congrArg Prod.snd equal
    have here : position = head := by
      by_contra different
      simp [cells, different] at marker
    subst position
    have symbol := congrArg Prod.fst equal
    have symbols : letters (Sum.inl answer) = letters (Sum.inl true) := by
      simpa [cells, Tape.mk₁, Tape.mk₂, Tape.mk'] using symbol
    exact Sum.inl.inj (letters.injective symbols)
  · intro trueAnswer
    subst answer
    refine ⟨head, ⟨lower, upper⟩, finalState, ?_⟩
    simp [cells, Tape.mk₁, Tape.mk₂, Tape.mk']

/-- Direct finite-array evolution observes exactly a certified Boolean output.
The window may also retain input cells beyond the reachable head interval. -/
theorem runs_window_accepting (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (input : Word) (answer : Bool) (allowance radius : ℕ)
    (wide : 2 * allowance ≤ radius)
    (runs : Internal.Runs machine entry letters input [Sum.inl answer] allowance) :
    (∃ index state,
      (cellTransition (windowNeighbors radius) (windowUpdate machine radius))^[allowance]
        (windowArray radius (cells 0 ⟨entry, Tape.mk₁ (input.map letters)⟩)) index =
          (letters (Sum.inl true), some state)) ↔ answer = true := by
  rw [← runs_accepting machine entry letters input answer allowance runs, windowArray_iterate]
  let initial : TM0.Cfg Symbol State := ⟨entry, Tape.mk₁ (input.map letters)⟩
  have agreement (position : ℤ) (inside : -(allowance : ℤ) ≤ position ∧ position ≤ allowance) :=
    windowEvolve_agree machine radius allowance (cells 0 initial) position (by constructor <;> omega)
  constructor
  · rintro ⟨index, state, hit⟩
    have reachable : -(allowance : ℤ) ≤ windowPosition radius index ∧ windowPosition radius index ≤ allowance := by
      by_contra outside
      have absent := windowEvolve_no_head_outside machine radius allowance initial
        (windowPosition radius index) (by omega)
      have marker := congrArg Prod.snd hit
      change (((windowEvolve machine radius)^[allowance] (window radius (cells 0 initial)))
        (windowPosition radius index)).2 = some state at marker
      rw [absent] at marker
      cases marker
    exact ⟨windowPosition radius index, reachable, state, (agreement _ reachable).symm.trans hit⟩
  · rintro ⟨position, inside, state, hit⟩
    obtain ⟨index, equal⟩ := windowPosition_surjective radius position (by constructor <;> omega)
    refine ⟨index, state, ?_⟩
    change ((windowEvolve machine radius)^[allowance] (window radius (cells 0 initial)))
      (windowPosition radius index) = _
    rw [equal, agreement position inside]
    exact hit

end Polytime2.Complexity
