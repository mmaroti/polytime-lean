/-
Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Polytime2.Complexity

/-! # Static wiring into a larger tape collection

A component uses an injective map of its tape names into enclosing tape names.
Its alphabet is the enclosing alphabet pulled back along that map, so alphabet
and blank compatibility require no runtime conversions. Range selection is
static mathematical data; it never depends on input values or tape lengths.
-/

namespace Polytime2.MultiTape

-- sourceLevel, targetLevel: local and enclosing tape names.
-- valueLevel: dependent families installed along a wiring.
-- symbolLevel: enclosing alphabets; stateLevel: the component controller.
universe sourceLevel targetLevel valueLevel symbolLevel stateLevel

variable {Source : Type sourceLevel} {Target : Type targetLevel}

/-- Replace wired fields and leave all other fields unchanged. -/
noncomputable def install (wiring : Source ↪ Target) {Family : Target → Type valueLevel}
    (localValues : ∀ name, Family (wiring name)) (original : ∀ name, Family name) :
    ∀ name, Family name := by
  classical
  exact fun name => if located : ∃ source, wiring source = name then
    located.choose_spec ▸ localValues located.choose else original name

@[simp] theorem install_at (wiring : Source ↪ Target) {Family : Target → Type valueLevel}
    (localValues : ∀ name, Family (wiring name)) (original : ∀ name, Family name) (name : Source) :
    install wiring localValues original (wiring name) = localValues name := by
  classical
  unfold install
  rw [dite_eq_left ⟨name, rfl⟩]
  generalize_proofs located
  have chosen : located.choose = name := wiring.injective located.choose_spec
  exact eq_of_heq ((eqRec_heq _ _).trans (by rw [chosen]))

theorem install_outside (wiring : Source ↪ Target) {Family : Target → Type valueLevel}
    (localValues : ∀ name, Family (wiring name)) (original : ∀ name, Family name)
    (name : Target) (outside : name ∉ Set.range wiring) :
    install wiring localValues original name = original name := by
  classical
  simp only [install, Set.mem_range] at outside ⊢
  exact dite_eq_right outside

/-- Bind a one-tape component to a named enclosing tape. -/
def oneTape (name : Target) : Unit ↪ Target :=
  ⟨fun _ => name, by intro first second _; cases first; cases second; rfl⟩

/-- Bind source and destination roles to distinct enclosing tapes. -/
def twoTapes (first second : Target) (distinct : first ≠ second) : Bool ↪ Target :=
  ⟨(fun | false => first | true => second), by
    intro left right equal
    cases left <;> cases right <;> simp_all⟩

@[simp] theorem oneTape_apply (name : Target) (source : Unit) : (oneTape name) source = name := rfl

@[simp] theorem twoTapes_false (first second : Target) (distinct : first ≠ second) :
    (twoTapes first second distinct) false = first := rfl

@[simp] theorem twoTapes_true (first second : Target) (distinct : first ≠ second) :
    (twoTapes first second distinct) true = second := rfl

@[simp] theorem install_one [DecidableEq Target] (name : Target) {Value : Type valueLevel}
    (changed : Unit → Value) (original : Target → Value) :
    install (oneTape name) changed original = Function.update original name (changed ()) := by
  funext target
  by_cases selected : target = name
  · subst target
    simp only [Function.update_self]
    exact install_at (oneTape name) changed original ()
  · have outside : target ∉ Set.range (oneTape name) := by
      rintro ⟨source, equal⟩
      exact selected equal.symm
    simp [install_outside _ _ _ _ outside, Function.update_of_ne selected]

@[simp] theorem install_two [DecidableEq Target] (first second : Target) (distinct : first ≠ second)
    {Value : Type valueLevel} (changed : Bool → Value) (original : Target → Value) :
    install (twoTapes first second distinct) changed original =
      Function.update (Function.update original first (changed false)) second (changed true) := by
  funext target
  by_cases selectedFirst : target = first
  · subst target
    simp only [Function.update_of_ne distinct, Function.update_self]
    exact install_at (twoTapes first second distinct) changed original false
  · by_cases selectedSecond : target = second
    · subst target
      simp only [Function.update_self]
      exact install_at (twoTapes first second distinct) changed original true
    · have outside : target ∉ Set.range (twoTapes first second distinct) := by
        rintro ⟨source, equal⟩
        cases source with
        | false => exact selectedFirst equal.symm
        | true => exact selectedSecond equal.symm
      simp [install_outside _ _ _ _ outside, Function.update_of_ne selectedFirst,
        Function.update_of_ne selectedSecond]

variable {Alphabet : Target → Type symbolLevel} [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}

/-- Run a local controller on its wired tapes, leaving every other tape stationary. -/
noncomputable def wire (wiring : Source ↪ Target)
    (machine : Machine (fun name => Alphabet (wiring name)) State) : Machine Alphabet State :=
  fun state symbols => (machine state (fun name => symbols (wiring name))).map fun command =>
    (command.1, install wiring command.2 (stationary symbols))

@[simp] theorem wired_act (wiring : Source ↪ Target)
    (actions : Actions (fun name => Alphabet (wiring name))) (tapes : Tapes Alphabet) :
    act (install wiring actions (stationary (read tapes))) tapes =
      install wiring (act actions (fun name => tapes (wiring name))) tapes := by
  classical
  funext name
  by_cases located : name ∈ Set.range wiring
  · obtain ⟨source, rfl⟩ := located
    simp only [act, install_at]
  · rw [install_outside wiring _ _ name located]
    simp only [act, install_outside wiring _ _ name located, stationary, read,
      Turing.Tape.write_self]

/-- Exact-cost embedding, including preservation of all unwired tapes. -/
theorem wire_steps (wiring : Source ↪ Target)
    (machine : Machine (fun name => Alphabet (wiring name)) State)
    {ticks : ℕ} {entry exit : State}
    {initial final : Tapes (fun name => Alphabet (wiring name))}
    (trace : Steps machine ticks (entry, initial) (exit, final))
    (enclosing : Tapes Alphabet) (agrees : ∀ name, enclosing (wiring name) = initial name) :
    Steps (wire wiring machine) ticks (entry, enclosing)
      (exit, install wiring final enclosing) := by
  classical
  generalize start : (entry, initial) = first at trace
  generalize finish : (exit, final) = last at trace
  induction trace generalizing entry exit initial final enclosing with
  | zero configuration =>
    have states : entry = exit := congrArg Prod.fst (start.trans finish.symm)
    have tapes : initial = final := congrArg Prod.snd (start.trans finish.symm)
    subst exit
    subst final
    have restored : install wiring initial enclosing = enclosing := by
      funext name
      by_cases located : name ∈ Set.range wiring
      · obtain ⟨source, rfl⟩ := located
        simp [agrees]
      · exact install_outside wiring _ _ name located
    rw [restored]
    exact .zero _
  | @next count first middle last transition rest hypothesis =>
    cases start
    cases equation : machine entry (read initial) with
    | none => simp [step, equation] at transition
    | some command =>
      rcases command with ⟨next, actions⟩
      simp only [step, equation, Option.map_some, Option.some.injEq] at transition
      subst middle
      let advanced := install wiring (act actions initial) enclosing
      have readMatches : (fun name => read enclosing (wiring name)) = read initial := by
        funext name; simp [read, agrees]
      have tapeMatches : (fun name => enclosing (wiring name)) = initial := funext agrees
      have stepped : step (wire wiring machine) (entry, enclosing) = some (next, advanced) := by
        simp only [step, wire, readMatches, equation, Option.map_some, wired_act, tapeMatches, advanced]
      have remainder := hypothesis advanced (by intro name; simp [advanced]) rfl finish
      have restored : install wiring final advanced = install wiring final enclosing := by
        funext name
        by_cases located : name ∈ Set.range wiring
        · obtain ⟨source, rfl⟩ := located
          simp
        · simp only [install_outside wiring _ _ name located, advanced]
      rw [restored] at remainder
      exact .next stepped remainder

namespace Realizes

-- parameterLevel: names of runtime size parameters.
universe parameterLevel

/-- Static tape wiring preserves the very same polynomial transition bound. -/
theorem wire {Parameter : Type parameterLevel} [Fintype Parameter]
    [Fintype Source] [Fintype Target] [∀ name, Fintype (Alphabet name)] [Fintype State]
    (wiring : Source ↪ Target)
    {machine : Machine (fun name => Alphabet (wiring name)) State} {entry exit : State}
    {precondition : (Parameter → ℕ) → Tapes (fun name => Alphabet (wiring name)) → Prop}
    {postcondition : (Parameter → ℕ) → Tapes (fun name => Alphabet (wiring name)) →
      Tapes (fun name => Alphabet (wiring name)) → Prop}
    (realization : Realizes machine entry exit precondition postcondition) :
    Realizes (MultiTape.wire wiring machine) entry exit
      (fun assignment tapes => precondition assignment (fun name => tapes (wiring name)))
      (fun assignment initial final => ∃ localFinal,
        postcondition assignment (fun name => initial (wiring name)) localFinal ∧
          final = install wiring localFinal initial) := by
  obtain ⟨halt, bound, runs⟩ := realization
  refine ⟨?_, bound, ?_⟩
  · intro symbols; simp [MultiTape.wire, halt]
  · intro assignment initial valid
    obtain ⟨ticks, localFinal, cost, trace, correct⟩ := runs assignment _ valid
    exact ⟨ticks, install wiring localFinal initial, cost,
      wire_steps wiring machine trace initial (by intro name; rfl), localFinal, correct, rfl⟩

end Realizes
end Polytime2.MultiTape
