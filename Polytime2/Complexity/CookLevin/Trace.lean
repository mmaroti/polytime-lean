import Polytime2.Complexity.CookLevin.LocalMachine
import Polytime2.Complexity.PolynomialTime

/-! # Bounded local simulation of certified word-machine traces

The polynomial-time contract stops at the actual halting time. Circuit
unrolling uses a predetermined time allowance. Absorbing halts bridge those
two conventions without adding any runtime hypothesis.
-/

namespace Polytime2.Complexity.CookLevin

open Turing

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]

/-- A successful optional trace is unchanged when halts become self-loops. -/
theorem advance_iterate_of_trace (machine : TM0.Machine Symbol State) (ticks : ℕ)
    {initial final : TM0.Cfg Symbol State}
    (trace : (fun current => current.bind (TM0.step machine))^[ticks] (some initial) = some final) :
    (advance machine)^[ticks] initial = final := by
  induction ticks generalizing final with
  | zero => exact Option.some.inj trace
  | succ ticks induction =>
    rw [Function.iterate_succ_apply'] at trace ⊢
    cases middle : (fun current => current.bind (TM0.step machine))^[ticks] (some initial) with
    | none => simp [middle] at trace
    | some configuration =>
      rw [induction middle]
      have transition : TM0.step machine configuration = some final := by
        simpa [middle] using trace
      simp [advance, transition]

/-- Running to any larger bound preserves an already halted result. -/
theorem advance_iterate_of_halted_trace (machine : TM0.Machine Symbol State)
    {ticks allowance : ℕ} {initial final : TM0.Cfg Symbol State}
    (bounded : ticks ≤ allowance)
    (trace : (fun current => current.bind (TM0.step machine))^[ticks] (some initial) = some final)
    (halt : TM0.step machine final = none) :
    (advance machine)^[allowance] initial = final := by
  have split : allowance = (allowance - ticks) + ticks := by omega
  rw [split, Function.iterate_add_apply, advance_iterate_of_trace machine ticks trace]
  exact Function.iterate_fixed (by simp [advance, halt]) _

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

end Polytime2.Complexity.CookLevin
