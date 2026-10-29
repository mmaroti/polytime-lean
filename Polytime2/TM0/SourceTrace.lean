import Mathlib.Computability.TuringMachine.PostTuringMachine
import Lean.Elab.Tactic.Omega

/-! # Source-machine traces with absorbing halts -/

namespace Polytime2.SourceTrace

open Turing

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]

/-- Perform one transition, leaving a halted configuration unchanged. -/
def advance (machine : TM0.Machine Symbol State) (configuration : TM0.Cfg Symbol State) :
    TM0.Cfg Symbol State :=
  (TM0.step machine configuration).getD configuration

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

end Polytime2.SourceTrace
