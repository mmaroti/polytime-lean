import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Tactic

/-! # Exact TM0 trace transport and sequential word computations

These foundational rules work on Mathlib TM0 machines and tapes. Alphabet
transport preserves transitions; sequential composition adds one stationary
handover transition. No new execution model is introduced.
-/

namespace Polytime2.TM0Word

open Turing

universe sourceLevel targetLevel

/-- Transport a successful counted trace through a simulation that preserves
successful transitions. Halting may be handled differently by the target. -/
theorem trace_map {Source : Type sourceLevel} {Target : Type targetLevel}
    {source : Source → Option Source} {target : Target → Option Target}
    (embed : Source → Target)
    (transition : ∀ first second, source first = some second → target (embed first) = some (embed second))
    {ticks : ℕ} {initial final : Source}
    (trace : (fun current => current.bind source)^[ticks] (some initial) = some final) :
    (fun current => current.bind target)^[ticks] (some (embed initial)) = some (embed final) := by
  induction ticks generalizing final with
  | zero => simpa using congrArg (Option.map embed) trace
  | succ ticks hypothesis =>
    rw [Function.iterate_succ_apply'] at trace ⊢
    cases middle : (fun current => current.bind source)^[ticks] (some initial) with
    | none => simp [middle] at trace
    | some configuration =>
      rw [hypothesis middle]
      exact transition configuration final (by simpa [middle] using trace)

section Alphabet

variable {Symbol TargetSymbol State : Type} [Inhabited Symbol] [Inhabited TargetSymbol]
variable [Inhabited State]

/-- Relabel symbols using a pointed map and a left inverse on reachable cells. -/
def mapMachine (source : TM0.Machine Symbol State) (forward : PointedMap Symbol TargetSymbol)
    (backward : TargetSymbol → Symbol) : TM0.Machine TargetSymbol State :=
  fun state symbol => (source state (backward symbol)).map fun command =>
    (command.1, match command.2 with
      | .move direction => .move direction
      | .write value => .write (forward value))

def mapConfiguration (forward : PointedMap Symbol TargetSymbol) (source : TM0.Cfg Symbol State) :
    TM0.Cfg TargetSymbol State := ⟨source.q, source.Tape.map forward⟩

theorem map_step (source : TM0.Machine Symbol State) (forward : PointedMap Symbol TargetSymbol)
    (backward : TargetSymbol → Symbol) (inverse : Function.LeftInverse backward forward)
    (configuration : TM0.Cfg Symbol State) :
    TM0.step (mapMachine source forward backward) (mapConfiguration forward configuration) =
      (TM0.step source configuration).map (mapConfiguration forward) := by
  rcases configuration with ⟨state, tape⟩
  have headInverse : backward (forward.f tape.head) = tape.head := inverse _
  cases equation : source state tape.head with
  | none => simp [TM0.step, mapMachine, mapConfiguration, headInverse, equation]
  | some command =>
    rcases command with ⟨next, instruction⟩
    cases instruction <;>
      simp [TM0.step, mapMachine, mapConfiguration, headInverse, equation, Tape.map_move]

theorem map_trace (source : TM0.Machine Symbol State) (forward : PointedMap Symbol TargetSymbol)
    (backward : TargetSymbol → Symbol) (inverse : Function.LeftInverse backward forward)
    {ticks : ℕ} {initial final : TM0.Cfg Symbol State}
    (trace : (fun current => current.bind (TM0.step source))^[ticks] (some initial) = some final) :
    (fun current => current.bind (TM0.step (mapMachine source forward backward)))^[ticks]
      (some (mapConfiguration forward initial)) = some (mapConfiguration forward final) := by
  apply trace_map (mapConfiguration forward) _ trace
  intro first second transition
  rw [map_step source forward backward inverse, transition]
  rfl

end Alphabet

section Sequencing

variable {Symbol First Second : Type} [Inhabited Symbol] [Inhabited First] [Inhabited Second]

/-- Run two word machines in sequence, handing the entire final tape of the
first to the second at its entry state. -/
def sequence (first : TM0.Machine Symbol First) (second : TM0.Machine Symbol Second)
    (secondEntry : Second) : TM0.Machine Symbol (Sum First Second)
  | .inl state, symbol => match first state symbol with
    | some command => some (.inl command.1, command.2)
    | none => some (.inr secondEntry, .write symbol)
  | .inr state, symbol => (second state symbol).map fun command => (.inr command.1, command.2)

theorem sequence_trace (first : TM0.Machine Symbol First) (second : TM0.Machine Symbol Second)
    {firstEntry firstExit : First} {secondEntry secondExit : Second}
    {initial middle final : Tape Symbol} {firstTicks secondTicks : ℕ}
    (firstTrace : (fun current => current.bind (TM0.step first))^[firstTicks]
      (some ⟨firstEntry, initial⟩) = some ⟨firstExit, middle⟩)
    (firstHalt : TM0.step first ⟨firstExit, middle⟩ = none)
    (secondTrace : (fun current => current.bind (TM0.step second))^[secondTicks]
      (some ⟨secondEntry, middle⟩) = some ⟨secondExit, final⟩) :
    (fun current => current.bind (TM0.step (sequence first second secondEntry)))^[firstTicks + 1 + secondTicks]
      (some ⟨.inl firstEntry, initial⟩) = some ⟨.inr secondExit, final⟩ := by
  have firstLift := trace_map (fun c : TM0.Cfg Symbol First =>
    (⟨.inl c.q, c.Tape⟩ : TM0.Cfg Symbol (Sum First Second))) (target := TM0.step (sequence first second secondEntry))
    (by
      rintro ⟨state, tape⟩ next transition
      cases equation : first state tape.head with
      | none => simp [TM0.step, equation] at transition
      | some command =>
        rcases command with ⟨nextState, instruction⟩
        cases instruction <;>
          simp only [TM0.step, equation, Option.map_some, Option.some.injEq] at transition <;>
          cases transition <;> simp [TM0.step, sequence, equation]) firstTrace
  have stopped : first firstExit middle.head = none := by
    cases equation : first firstExit middle.head <;> simp_all [TM0.step]
  have handover : TM0.step (sequence first second secondEntry) ⟨.inl firstExit, middle⟩ =
      some ⟨.inr secondEntry, middle⟩ := by simp [TM0.step, sequence, stopped, Tape.write_self]
  have secondLift := trace_map (fun c : TM0.Cfg Symbol Second =>
    (⟨.inr c.q, c.Tape⟩ : TM0.Cfg Symbol (Sum First Second))) (target := TM0.step (sequence first second secondEntry))
    (by
      rintro ⟨state, tape⟩ next transition
      cases equation : second state tape.head with
      | none => simp [TM0.step, equation] at transition
      | some command =>
        rcases command with ⟨nextState, instruction⟩
        cases instruction <;>
          simp only [TM0.step, equation, Option.map_some, Option.some.injEq] at transition <;>
          cases transition <;> simp [TM0.step, sequence, equation]) secondTrace
  rw [show firstTicks + 1 + secondTicks = secondTicks + (1 + firstTicks) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, firstLift]
  simpa only [Function.iterate_one, Option.bind_some, handover] using secondLift

end Sequencing
end Polytime2.TM0Word
