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

import Polytime2.BinaryEncoding
import Polytime2.EncodedArray
import Polytime2.Binary
import Polytime2.Branch
import Polytime2.While

/-! # Fixed-region calling convention

The position functions in `Runs` are proof data, not controller registers.
Every transition preserves read-only data and cells outside reserved regions.
Heads may visit surrounding blanks, but can never change them.
-/

namespace Polytime2.CallingConvention

open MultiTape
open Binary (Symbol data word)

-- tapeLevel: tape roles; stateLevel: finite machine controllers.
-- parameterLevel: size names; carrierLevel: mathematical domain elements.
universe tapeLevel stateLevel parameterLevel carrierLevel
variable {TapeName : Type tapeLevel} {State : Type stateLevel}

abbrev Alphabet (TapeName : Type tapeLevel) := fun _ : TapeName => Symbol

/-- A head-relative coordinate converted to the fixed entry coordinate system. -/
def displacement : Option Turing.Dir → ℤ
  | none => 0
  | some .left => -1
  | some .right => 1

/-- At an absolute head position, only cells inside writable regions may change. -/
def Allowed (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (position : TapeName → ℤ) (symbols : Symbols (Alphabet TapeName))
    (actions : Actions (Alphabet TapeName)) : Prop :=
  ∀ name, (readOnly name = true ∨ position name < 0 ∨ (width name : ℤ) ≤ position name) →
    (actions name).1 = symbols name

/-- Counted execution with a proof of the calling convention at every step. -/
inductive Runs (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (machine : Machine (Alphabet TapeName) State) :
    ℕ → State → (TapeName → ℤ) → Tapes (Alphabet TapeName) →
      State → (TapeName → ℤ) → Tapes (Alphabet TapeName) → Prop
  | zero (state position tapes) : Runs width readOnly machine 0 state position tapes state position tapes
  | next {ticks state nextState finalState position finalPosition tapes finalTapes actions}
      (instruction : machine state (read tapes) = some (nextState, actions))
      (allowed : Allowed width readOnly position (read tapes) actions)
      (rest : Runs width readOnly machine ticks nextState
        (fun name => position name + displacement (actions name).2)
        (act actions tapes) finalState finalPosition finalTapes) :
      Runs width readOnly machine (ticks + 1) state position tapes finalState finalPosition finalTapes

namespace Runs

variable {width : TapeName → ℕ} {readOnly : TapeName → Bool}
variable {machine : Machine (Alphabet TapeName) State}

/-- Annotate a known transition with its region and head-position proofs. -/
theorem next_of_step {ticks state nextState finalState position nextPosition finalPosition
    tapes nextTapes finalTapes}
    (transition : step machine (state, tapes) = some (nextState, nextTapes))
    (safe : ∀ actions, machine state (read tapes) = some (nextState, actions) →
      Allowed width readOnly position (read tapes) actions ∧
      nextPosition = fun name => position name + displacement (actions name).2)
    (rest : Runs width readOnly machine ticks nextState nextPosition nextTapes
      finalState finalPosition finalTapes) :
    Runs width readOnly machine (ticks + 1) state position tapes
      finalState finalPosition finalTapes := by
  cases instruction : machine state (read tapes) with
  | none => simp [step, instruction] at transition
  | some command =>
    rcases command with ⟨following, actions⟩
    have equal : following = nextState ∧ act actions tapes = nextTapes := by
      simpa [step, instruction] using transition
    rcases equal with ⟨rfl, rfl⟩
    obtain ⟨allowed, positions⟩ := safe actions instruction
    rw [positions] at rest
    exact Runs.next instruction allowed rest

/-- A controller-determined position permits reuse of existing counted traces.
The positions are proof annotations; they do not enlarge the machine state. -/
theorem of_steps (position : State → TapeName → ℤ)
    (safe : ∀ state symbols nextState actions,
      machine state symbols = some (nextState, actions) →
      Allowed width readOnly (position state) symbols actions ∧
        position nextState = fun name => position state name + displacement (actions name).2)
    {ticks initial final} (trace : Steps machine ticks initial final) :
    Runs width readOnly machine ticks initial.1 (position initial.1) initial.2
      final.1 (position final.1) final.2 := by
  induction trace with
  | zero => exact .zero _ _ _
  | @next ticks initial middle final transition rest hypothesis =>
    obtain ⟨state, tapes⟩ := initial
    cases instruction : machine state (read tapes) with
    | none => simp [step, instruction] at transition
    | some command =>
      obtain ⟨nextState, actions⟩ := command
      have equal : middle = (nextState, act actions tapes) := by
        simpa [step, instruction] using transition.symm
      subst middle
      obtain ⟨allowed, positions⟩ := safe state (read tapes) nextState actions instruction
      rw [positions] at hypothesis
      exact .next instruction allowed hypothesis

/-- Lift an existing execution using an invariant that tracks runtime head
positions. This handles scans whose positions are not finite controller states. -/
theorem of_steps_invariant
    (invariant : (TapeName → ℤ) → State → Tapes (Alphabet TapeName) → Prop)
    (safe : ∀ position state tapes nextState actions,
      invariant position state tapes →
      machine state (read tapes) = some (nextState, actions) →
      Allowed width readOnly position (read tapes) actions ∧
        invariant (fun name => position name + displacement (actions name).2)
          nextState (act actions tapes))
    {ticks initial final} (trace : Steps machine ticks initial final)
    (position : TapeName → ℤ) (valid : invariant position initial.1 initial.2) :
    ∃ finalPosition, Runs width readOnly machine ticks initial.1 position initial.2
      final.1 finalPosition final.2 ∧ invariant finalPosition final.1 final.2 := by
  induction trace generalizing position with
  | zero => exact ⟨position, .zero _ _ _, valid⟩
  | @next ticks initial middle final transition rest hypothesis =>
    obtain ⟨state, tapes⟩ := initial
    cases instruction : machine state (read tapes) with
    | none => simp [step, instruction] at transition
    | some command =>
      obtain ⟨nextState, actions⟩ := command
      have equal : middle = (nextState, act actions tapes) := by
        simpa [step, instruction] using transition.symm
      subst middle
      obtain ⟨allowed, nextValid⟩ := safe position state tapes nextState actions valid instruction
      obtain ⟨finalPosition, trace, finalValid⟩ := hypothesis _ nextValid
      exact ⟨finalPosition, .next instruction allowed trace, finalValid⟩

/-- The proof-annotated run consists of actual transitions of the finite machine. -/
theorem steps {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes finalState finalPosition finalTapes) :
    Steps machine ticks (state, tapes) (finalState, finalTapes) := by
  induction trace with
  | zero => exact .zero _
  | next instruction allowed rest hypothesis =>
    exact .next (by simp [step, instruction]) hypothesis

/-- Safe runs compose without exposing or changing their physical boundaries. -/
theorem trans {firstTicks secondTicks firstState middleState finalState}
    {firstPosition middlePosition finalPosition firstTapes middleTapes finalTapes}
    (first : Runs width readOnly machine firstTicks firstState firstPosition firstTapes
      middleState middlePosition middleTapes)
    (second : Runs width readOnly machine secondTicks middleState middlePosition middleTapes
      finalState finalPosition finalTapes) :
    Runs width readOnly machine (firstTicks + secondTicks) firstState firstPosition firstTapes
      finalState finalPosition finalTapes := by
  induction first with
  | zero => simpa using second
  | next instruction allowed rest hypothesis =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Runs.next instruction allowed (hypothesis second)

/-- A fixed-width operation may act on a subregion of a larger tape. Writable
subregions must fit; read-only tapes may be positioned anywhere. -/
theorem regions (enclosingWidth : TapeName → ℕ) (offset : TapeName → ℤ)
    (fits : ∀ name, readOnly name = false →
      0 ≤ offset name ∧ offset name + width name ≤ enclosingWidth name)
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes finalState finalPosition finalTapes) :
    Runs enclosingWidth readOnly machine ticks state (fun name => position name + offset name) tapes
      finalState (fun name => finalPosition name + offset name) finalTapes := by
  induction trace with
  | zero => exact .zero _ _ _
  | @next ticks state nextState finalState position finalPosition tapes finalTapes actions
      instruction allowed rest hypothesis =>
    have safe : Allowed enclosingWidth readOnly (fun name => position name + offset name)
        (read tapes) actions := by
      intro name outside
      apply allowed name
      by_cases immutable : readOnly name = true
      · exact Or.inl immutable
      · have writable : readOnly name = false := Bool.eq_false_iff.mpr immutable
        obtain ⟨start, bounded⟩ := fits name writable
        rcases outside with immutable' | before | after
        · exact False.elim (immutable immutable')
        · change position name + offset name < 0 at before
          exact Or.inr (Or.inl (by omega))
        · change (enclosingWidth name : ℤ) ≤ position name + offset name at after
          exact Or.inr (Or.inr (by omega))
    have equal : (fun name => (position name + displacement (actions name).2) + offset name) =
        fun name => (position name + offset name) + displacement (actions name).2 := by
      funext name
      ring
    rw [equal] at hypothesis
    exact .next instruction safe hypothesis

/-- A component may preserve additional private inputs without making them
read-only for the enclosing algorithm. -/
theorem readOnly_mono {targetReadOnly : TapeName → Bool}
    (compatible : ∀ name, targetReadOnly name = true → readOnly name = true)
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes) :
    Runs width targetReadOnly machine ticks state position tapes
      finalState finalPosition finalTapes := by
  induction trace with
  | zero => exact .zero _ _ _
  | next instruction allowed rest hypothesis =>
    refine .next instruction ?_ hypothesis
    intro name premise
    apply allowed name
    rcases premise with readonly | before | after
    · exact Or.inl (compatible name readonly)
    · exact Or.inr (Or.inl before)
    · exact Or.inr (Or.inr after)

-- targetStateLevel: controllers used when combining routine states.
universe targetStateLevel

/-- Relabeling control states does not change tape safety or head positions. -/
theorem rename {TargetState : Type targetStateLevel}
    {target : Machine (Alphabet TapeName) TargetState} (embed : State → TargetState)
    (simulation : ∀ state symbols nextState actions,
      machine state symbols = some (nextState, actions) →
        target (embed state) symbols = some (embed nextState, actions))
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes) :
    Runs width readOnly target ticks (embed state) position tapes
      (embed finalState) finalPosition finalTapes := by
  induction trace with
  | zero => exact .zero _ _ _
  | next instruction allowed rest hypothesis =>
    exact .next (simulation _ _ _ _ instruction) allowed hypothesis

/-- A routine whose private finite memory determines its terminal state can
return through one common exit without changing any tape or head position. -/
theorem withExit_at {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes)
    (halt : machine finalState (read finalTapes) = none) :
    Runs width readOnly (MultiTape.withExit machine) (ticks + 1)
      (.inl state) position tapes (.inr ()) finalPosition finalTapes := by
  have lifted := trace.rename Sum.inl (target := MultiTape.withExit machine)
    (by intro state symbols nextState actions instruction; simp [MultiTape.withExit, instruction])
  have handover : Runs width readOnly (MultiTape.withExit machine) 1
      (.inl finalState) finalPosition finalTapes (.inr ()) finalPosition finalTapes := by
    apply Runs.next (nextState := Sum.inr ()) (actions := stationary (read finalTapes))
      (by simp [MultiTape.withExit, halt]) (by intro name premise; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using
      (Runs.zero (machine := MultiTape.withExit machine) (Sum.inr ()) finalPosition finalTapes)
  exact lifted.trans handover

/-- A uniformly halting exit is a special case of halting on the final data. -/
theorem withExit {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes)
    (halt : ∀ symbols, machine finalState symbols = none) :
    Runs width readOnly (MultiTape.withExit machine) (ticks + 1)
      (.inl state) position tapes (.inr ()) finalPosition finalTapes :=
  trace.withExit_at (halt _)

-- secondStateLevel: the controller of the following routine.
universe secondStateLevel

/-- Sequential composition preserves all region and read-only invariants,
including at the stationary handover between the two routines. -/
theorem sequence {SecondState : Type secondStateLevel}
    (second : Machine (Alphabet TapeName) SecondState) (secondEntry : SecondState)
    {firstEntry firstExit : State} {secondExit : SecondState}
    {firstTicks secondTicks firstPosition middlePosition finalPosition}
    {firstTapes middleTapes finalTapes}
    (firstTrace : Runs width readOnly machine firstTicks firstEntry firstPosition firstTapes
      firstExit middlePosition middleTapes)
    (firstHalt : ∀ symbols, machine firstExit symbols = none)
    (secondTrace : Runs width readOnly second secondTicks secondEntry middlePosition middleTapes
      secondExit finalPosition finalTapes) :
    Runs width readOnly (MultiTape.sequence machine second secondEntry)
      (firstTicks + secondTicks + 1) (.inl firstEntry) firstPosition firstTapes
      (.inr secondExit) finalPosition finalTapes := by
  have first := firstTrace.rename Sum.inl
    (target := MultiTape.sequence machine second secondEntry)
    (by intro state symbols nextState actions instruction; simp [MultiTape.sequence, instruction])
  have liftedSecond := secondTrace.rename Sum.inr
    (target := MultiTape.sequence machine second secondEntry)
    (by intro state symbols nextState actions instruction; simp [MultiTape.sequence, instruction])
  have handover : Runs width readOnly (MultiTape.sequence machine second secondEntry) 1
      (.inl firstExit) middlePosition middleTapes (.inr secondEntry) middlePosition middleTapes := by
    apply Runs.next (nextState := Sum.inr secondEntry)
      (actions := stationary (read middleTapes))
      (by simp [MultiTape.sequence, firstHalt]) (by intro name premise; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using
      (Runs.zero (machine := MultiTape.sequence machine second secondEntry)
        (Sum.inr secondEntry) middlePosition middleTapes)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans (handover.trans liftedSecond)

/-- A guard already stored on a tape selects the first safe routine. Both
selection and return preserve every region and read-only tape. -/
theorem branch_true {SecondState : Type secondStateLevel}
    (condition : Symbols (Alphabet TapeName) → Bool)
    (second : Machine (Alphabet TapeName) SecondState) (secondEntry : SecondState)
    {entry exit : State} {ticks position finalPosition tapes finalTapes}
    (selected : condition (read tapes) = true)
    (trace : Runs width readOnly machine ticks entry position tapes exit finalPosition finalTapes)
    (halt : ∀ symbols, machine exit symbols = none) :
    Runs width readOnly (MultiTape.withExit (branchMachine condition machine second entry secondEntry))
      (ticks + 2) (.inl (.inl ())) position tapes (.inr ()) finalPosition finalTapes := by
  have lifted := trace.rename (fun state => Sum.inr (Sum.inl state))
    (target := branchMachine condition machine second entry secondEntry)
    (by intro state symbols nextState actions instruction; simp [branchMachine, instruction])
  have choose : Runs width readOnly (branchMachine condition machine second entry secondEntry) 1
      (.inl ()) position tapes (.inr (.inl entry)) position tapes := by
    apply Runs.next (nextState := Sum.inr (Sum.inl entry)) (actions := stationary (read tapes))
      (by simp [branchMachine, selected]) (by intro name premise; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using
      (Runs.zero (machine := branchMachine condition machine second entry secondEntry)
        (Sum.inr (Sum.inl entry)) position tapes)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (choose.trans lifted).withExit
    (by intro symbols; simp [branchMachine, halt])

/-- The false branch has the same safety contract and stationary handovers. -/
theorem branch_false {FirstState : Type secondStateLevel}
    (condition : Symbols (Alphabet TapeName) → Bool)
    (first : Machine (Alphabet TapeName) FirstState) (firstEntry : FirstState)
    {entry exit : State} {ticks position finalPosition tapes finalTapes}
    (selected : condition (read tapes) = false)
    (trace : Runs width readOnly machine ticks entry position tapes exit finalPosition finalTapes)
    (halt : ∀ symbols, machine exit symbols = none) :
    Runs width readOnly (MultiTape.withExit (branchMachine condition first machine firstEntry entry))
      (ticks + 2) (.inl (.inl ())) position tapes (.inr ()) finalPosition finalTapes := by
  have lifted := trace.rename (fun state => Sum.inr (Sum.inr state))
    (target := branchMachine condition first machine firstEntry entry)
    (by intro state symbols nextState actions instruction; simp [branchMachine, instruction])
  have choose : Runs width readOnly (branchMachine condition first machine firstEntry entry) 1
      (.inl ()) position tapes (.inr (.inr entry)) position tapes := by
    apply Runs.next (nextState := Sum.inr (Sum.inr entry)) (actions := stationary (read tapes))
      (by simp [branchMachine, selected]) (by intro name premise; rfl)
    simpa only [stationary, displacement, add_zero, act_stationary] using
      (Runs.zero (machine := branchMachine condition first machine firstEntry entry)
        (Sum.inr (Sum.inr entry)) position tapes)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (choose.trans lifted).withExit
    (by intro symbols; simp [branchMachine, halt])

/-- A mathematical progress measure bounds a guard-driven loop. Guard and
body calls restore all their heads; stationary handovers preserve every region.
The progress measure and its bound are proof data, never machine registers. -/
theorem whileLoop {Guard : Type stateLevel} {Body : Type secondStateLevel}
    (guard : Machine (Alphabet TapeName) Guard) (body : Machine (Alphabet TapeName) Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols (Alphabet TapeName) → Bool) (invariant : Tapes (Alphabet TapeName) → Prop)
    (measure : Tapes (Alphabet TapeName) → ℕ) (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ initial, invariant initial → ∃ ticks final,
      ticks ≤ guardBound ∧ Runs width readOnly guard ticks guardEntry (fun _ => 0) initial
        guardExit (fun _ => 0) final ∧ invariant final ∧ measure final ≤ measure initial)
    (bodyRuns : ∀ initial, invariant initial → result (read initial) = true → ∃ ticks final,
      ticks ≤ bodyBound ∧ Runs width readOnly body ticks bodyEntry (fun _ => 0) initial
        bodyExit (fun _ => 0) final ∧ invariant final ∧ measure final < measure initial)
    (initial : Tapes (Alphabet TapeName)) (valid : invariant initial) :
    ∃ ticks final, ticks ≤ (measure initial + 1) * (guardBound + bodyBound + 2) ∧
      Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry) (fun _ => 0) initial (.inl guardExit) (fun _ => 0) final ∧
      invariant final ∧ result (read final) = false := by
  generalize ranking : measure initial = rank
  induction rank using Nat.strong_induction_on generalizing initial with
  | h rank hypothesis =>
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardedValid, guardMeasure⟩ := guardRuns initial valid
    have liftedGuard := guardTrace.rename Sum.inl
      (target := MultiTape.whileMachine guard body guardEntry bodyEntry result)
      (by intro state symbols next actions transition; simp [MultiTape.whileMachine, transition])
    cases tested : result (read guarded) with
    | false =>
      refine ⟨guardTicks, guarded, ?_, liftedGuard, guardedValid, tested⟩
      have positive : 1 ≤ rank + 1 := by omega
      have dominates := Nat.mul_le_mul_right (guardBound + bodyBound + 2) positive
      simp only [one_mul] at dominates
      omega
    | true =>
      obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, advancedValid, bodyMeasure⟩ :=
        bodyRuns guarded guardedValid tested
      have smaller : measure advanced < rank := by omega
      obtain ⟨restTicks, final, restCost, restTrace, finalValid, stopped⟩ :=
        hypothesis (measure advanced) smaller advanced advancedValid rfl
      have liftedBody := bodyTrace.rename Sum.inr
        (target := MultiTape.whileMachine guard body guardEntry bodyEntry result)
        (by intro state symbols next actions transition; simp [MultiTape.whileMachine, transition])
      have toBody : Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) 1
          (.inl guardExit) (fun _ => 0) guarded (.inr bodyEntry) (fun _ => 0) guarded := by
        apply Runs.next (nextState := Sum.inr bodyEntry) (actions := stationary (read guarded))
          (by simp [MultiTape.whileMachine, guardHalt, tested]) (by intro name premise; rfl)
        simpa only [stationary, displacement, add_zero, act_stationary] using
          (Runs.zero (machine := MultiTape.whileMachine guard body guardEntry bodyEntry result)
            (.inr bodyEntry) (fun _ => 0) guarded)
      have toGuard : Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) 1
          (.inr bodyExit) (fun _ => 0) advanced (.inl guardEntry) (fun _ => 0) advanced := by
        apply Runs.next (nextState := Sum.inl guardEntry) (actions := stationary (read advanced))
          (by simp [MultiTape.whileMachine, bodyHalt]) (by intro name premise; rfl)
        simpa only [stationary, displacement, add_zero, act_stationary] using
          (Runs.zero (machine := MultiTape.whileMachine guard body guardEntry bodyEntry result)
            (.inl guardEntry) (fun _ => 0) advanced)
      have trace := liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace)))
      refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, ?_, trace, finalValid, stopped⟩
      have dominated := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show measure advanced + 1 ≤ rank by omega)
      calc
        guardTicks + (1 + (bodyTicks + (1 + restTicks))) ≤
            (guardBound + bodyBound + 2) + rank * (guardBound + bodyBound + 2) := by omega
        _ = (rank + 1) * (guardBound + bodyBound + 2) := by ring

-- enclosingTapeLevel: tape roles of a caller containing the component.
universe enclosingTapeLevel

/-- Embed a safe component run in a larger collection of tapes. Every unwired
tape remains stationary, including private tapes and immutable size inputs. -/
theorem wire {EnclosingTape : Type enclosingTapeLevel}
    (wiring : TapeName ↪ EnclosingTape)
    (enclosingWidth : EnclosingTape → ℕ) (enclosingReadOnly : EnclosingTape → Bool)
    (widthMatches : ∀ name, enclosingWidth (wiring name) = width name)
    (readOnlyMatches : ∀ name, enclosingReadOnly (wiring name) = true → readOnly name = true)
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes)
    (enclosing : Tapes (Alphabet EnclosingTape)) (enclosingPosition : EnclosingTape → ℤ) :
    Runs enclosingWidth enclosingReadOnly (MultiTape.wire wiring machine) ticks state
      (install wiring position enclosingPosition) (install wiring tapes enclosing)
      finalState (install wiring finalPosition enclosingPosition) (install wiring finalTapes enclosing) := by
  classical
  induction trace with
  | zero => exact .zero _ _ _
  | @next ticks state nextState finalState position finalPosition tapes finalTapes actions
      instruction allowed rest hypothesis =>
    let outerTapes := install wiring tapes enclosing
    let outerPosition := install wiring position enclosingPosition
    let outerActions := install wiring actions (stationary (read outerTapes))
    have projected : (fun name => read outerTapes (wiring name)) = read tapes := by
      funext name
      simp [outerTapes, MultiTape.read]
    have outerInstruction : MultiTape.wire wiring machine state (read outerTapes) =
        some (nextState, outerActions) := by
      simp [MultiTape.wire, projected, instruction, outerActions]
    have outerAllowed : Allowed enclosingWidth enclosingReadOnly outerPosition
        (read outerTapes) outerActions := by
      intro name premise
      by_cases located : name ∈ Set.range wiring
      · obtain ⟨localName, rfl⟩ := located
        simp only [outerActions, install_at]
        have localPremise : readOnly localName = true ∨
            position localName < 0 ∨ (width localName : ℤ) ≤ position localName := by
          simp only [outerPosition, install_at, widthMatches] at premise
          rcases premise with readonly | before | after
          · exact Or.inl (readOnlyMatches localName readonly)
          · exact Or.inr (Or.inl before)
          · exact Or.inr (Or.inr after)
        simpa [outerTapes, MultiTape.read] using allowed localName localPremise
      · simp [outerActions, install_outside _ _ _ _ located, stationary]
    have nextPosition : (fun name => outerPosition name + displacement (outerActions name).2) =
        install wiring (fun name => position name + displacement (actions name).2) enclosingPosition := by
      funext name
      by_cases located : name ∈ Set.range wiring
      · obtain ⟨localName, rfl⟩ := located
        simp [outerPosition, outerActions]
      · simp [outerPosition, outerActions, install_outside _ _ _ _ located, stationary,
          displacement]
    have nextTapes : act outerActions outerTapes = install wiring (act actions tapes) enclosing := by
      have pulled : (fun name => outerTapes (wiring name)) = tapes := by
        funext name; simp [outerTapes]
      simp only [outerActions, wired_act, pulled, outerTapes, install_overwrite]
    have advanced := Runs.next outerInstruction outerAllowed
      (by simpa only [nextPosition, nextTapes] using hypothesis)
    exact advanced

/-- Wire a routine with explicit entry and exit head positions. -/
theorem wire_at_of_eq {EnclosingTape : Type enclosingTapeLevel}
    (wiring : TapeName ↪ EnclosingTape)
    (enclosingWidth : EnclosingTape → ℕ) (enclosingReadOnly : EnclosingTape → Bool)
    (widthMatches : ∀ name, enclosingWidth (wiring name) = width name)
    (readOnlyMatches : ∀ name, enclosingReadOnly (wiring name) = true → readOnly name = true)
    {ticks state finalState localPosition localFinalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state localPosition tapes
      finalState localFinalPosition finalTapes)
    (position finalPosition : EnclosingTape → ℤ)
    (initial final : Tapes (Alphabet EnclosingTape))
    (positionMatches : ∀ name, position (wiring name) = localPosition name)
    (finalPositionMatches : ∀ name, finalPosition (wiring name) = localFinalPosition name)
    (outsidePositions : ∀ name, name ∉ Set.range wiring → finalPosition name = position name)
    (initialMatches : ∀ name, initial (wiring name) = tapes name)
    (finalMatches : ∀ name, final (wiring name) = finalTapes name)
    (outsideMatches : ∀ name, name ∉ Set.range wiring → final name = initial name) :
    Runs enclosingWidth enclosingReadOnly (MultiTape.wire wiring machine) ticks
      state position initial finalState finalPosition final := by
  classical
  have initialPositionEq : install wiring localPosition position = position := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at, positionMatches]
    · exact install_outside _ _ _ _ located
  have finalPositionEq : install wiring localFinalPosition position = finalPosition := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at, finalPositionMatches]
    · rw [install_outside _ _ _ _ located, outsidePositions name located]
  have initialEq : install wiring tapes initial = initial := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at, initialMatches]
    · exact install_outside _ _ _ _ located
  have finalEq : install wiring finalTapes initial = final := by
    funext name
    by_cases located : name ∈ Set.range wiring
    · obtain ⟨name, rfl⟩ := located
      rw [install_at, finalMatches]
    · rw [install_outside _ _ _ _ located, outsideMatches name located]
  simpa only [initialPositionEq, finalPositionEq, initialEq, finalEq] using
    trace.wire wiring enclosingWidth enclosingReadOnly widthMatches readOnlyMatches initial position

/-- Wire a restoring routine using field equalities rather than exposing the
installation function in each caller's execution theorem. -/
theorem wire_of_eq {EnclosingTape : Type enclosingTapeLevel}
    (wiring : TapeName ↪ EnclosingTape)
    (enclosingWidth : EnclosingTape → ℕ) (enclosingReadOnly : EnclosingTape → Bool)
    (widthMatches : ∀ name, enclosingWidth (wiring name) = width name)
    (readOnlyMatches : ∀ name, enclosingReadOnly (wiring name) = true → readOnly name = true)
    {ticks state finalState tapes finalTapes}
    (trace : Runs width readOnly machine ticks state (fun _ => 0) tapes
      finalState (fun _ => 0) finalTapes)
    (initial final : Tapes (Alphabet EnclosingTape))
    (initialMatches : ∀ name, initial (wiring name) = tapes name)
    (finalMatches : ∀ name, final (wiring name) = finalTapes name)
    (outsideMatches : ∀ name, name ∉ Set.range wiring → final name = initial name) :
    Runs enclosingWidth enclosingReadOnly (MultiTape.wire wiring machine) ticks
      state (fun _ => 0) initial finalState (fun _ => 0) final := by
  exact trace.wire_at_of_eq wiring enclosingWidth enclosingReadOnly widthMatches readOnlyMatches
    (fun _ => 0) (fun _ => 0) initial final
    (by intro name; rfl) (by intro name; rfl) (by intro name outside; rfl)
    initialMatches finalMatches outsideMatches

end Runs

/-- The absolute cell changed by one transition is precisely its old head cell. -/
theorem action_nth (actions : Actions (Alphabet TapeName)) (tapes : Tapes (Alphabet TapeName))
    (position : TapeName → ℤ) (name : TapeName) (index : ℤ) :
    (act actions tapes name).nth
        (index - (position name + displacement (actions name).2)) =
      if index = position name then (actions name).1 else (tapes name).nth (index - position name) := by
  cases movementEq : (actions name).2 with
  | none => simp [act, movementEq, displacement, Turing.Tape.write_nth, sub_eq_zero]
  | some direction =>
    cases direction with
    | left =>
      have offset : index - (position name + -1) - 1 = index - position name := by omega
      simp [act, movementEq, displacement, offset, Turing.Tape.write_nth, sub_eq_zero]
    | right =>
      have offset : index - (position name + 1) + 1 = index - position name := by omega
      simp [act, movementEq, displacement, offset, Turing.Tape.write_nth, sub_eq_zero]

/-- Every read-only cell and every cell outside a writable region is preserved,
including during intermediate execution, not merely at the final boundary. -/
theorem Runs.preserves {width : TapeName → ℕ} {readOnly : TapeName → Bool}
    {machine : Machine (Alphabet TapeName) State}
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes finalState finalPosition finalTapes)
    (name : TapeName) (index : ℤ)
    (readOnlyProof : readOnly name = true ∨ index < 0 ∨ (width name : ℤ) ≤ index) :
    (finalTapes name).nth (index - finalPosition name) = (tapes name).nth (index - position name) := by
  induction trace with
  | zero => rfl
  | next instruction allowed rest hypothesis =>
    rw [hypothesis, action_nth]
    split
    next equal =>
      subst index
      simpa [MultiTape.read] using allowed name readOnlyProof
    next different => rfl

/-- A routine that restores its heads restores each read-only tape exactly.
This supplies canonical inputs when composing encoded-domain routines. -/
theorem Runs.readOnly_tape {width : TapeName → ℕ} {readOnly : TapeName → Bool}
    {machine : Machine (Alphabet TapeName) State}
    {ticks state finalState tapes finalTapes}
    (trace : Runs width readOnly machine ticks state (fun _ => 0) tapes
      finalState (fun _ => 0) finalTapes)
    (name : TapeName) (immutable : readOnly name = true) :
    finalTapes name = tapes name := by
  have cells : ∀ index : ℤ, (finalTapes name).nth index = (tapes name).nth index := by
    intro index
    simpa only [sub_zero] using trace.preserves name index (Or.inl immutable)
  generalize finalEq : finalTapes name = finalTape at cells ⊢
  generalize initialEq : tapes name = initialTape at cells ⊢
  cases finalTape with
  | mk finalHead finalLeft finalRight =>
    cases initialTape with
    | mk initialHead initialLeft initialRight =>
      have heads := cells 0
      have left : finalLeft = initialLeft := Turing.ListBlank.ext (fun index =>
        cells (-(index + 1 : ℕ)))
      have right : finalRight = initialRight := Turing.ListBlank.ext (fun index =>
        cells (index + 1 : ℕ))
      congr

-- targetTapeLevel: the enclosing collection used by a restoring call.
universe targetTapeLevel

/-- Lift a restoring call and expose its named results directly. Installation,
zero head positions, and preservation of other tapes are handled once here. -/
theorem Runs.wire_restoring {width : TapeName → ℕ} {readOnly : TapeName → Bool}
    {machine : Machine (Alphabet TapeName) State}
    {EnclosingTape : Type targetTapeLevel}
    (wiring : TapeName ↪ EnclosingTape)
    (enclosingWidth : EnclosingTape → ℕ) (enclosingReadOnly : EnclosingTape → Bool)
    (widthMatches : ∀ name, enclosingWidth (wiring name) = width name)
    (readOnlyMatches : ∀ name, enclosingReadOnly (wiring name) = true → readOnly name = true)
    (initial : Tapes (Alphabet EnclosingTape)) {ticks state finalState tapes finalTapes}
    (initialMatches : ∀ name, initial (wiring name) = tapes name)
    (trace : Runs width readOnly machine ticks state (fun _ => 0)
      tapes finalState (fun _ => 0) finalTapes) :
    ∃ final, Runs enclosingWidth enclosingReadOnly (MultiTape.wire wiring machine) ticks
        state (fun _ => 0) initial finalState (fun _ => 0) final ∧
      (∀ name, final (wiring name) = finalTapes name) ∧
      (∀ name, name ∉ Set.range wiring → final name = initial name) ∧
      (∀ name, readOnly name = true → final (wiring name) = initial (wiring name)) := by
  classical
  have initialEqual : tapes = fun name => initial (wiring name) :=
    funext (fun name => (initialMatches name).symm)
  rw [initialEqual] at trace
  have lifted := trace.wire wiring enclosingWidth enclosingReadOnly widthMatches readOnlyMatches
    initial (fun _ => 0)
  have positions : install wiring (fun _ => (0 : ℤ))
      (fun _ : EnclosingTape => (0 : ℤ)) = fun _ => 0 := install_self wiring _
  rw [install_self, positions] at lifted
  refine ⟨install wiring finalTapes initial, lifted, install_at wiring finalTapes initial,
    install_outside wiring finalTapes initial, ?_⟩
  intro name immutable
  exact (install_at wiring finalTapes initial name).trans (trace.readOnly_tape name immutable)

/-- Blank surroundings at a known absolute head position. The interior is arbitrary. -/
def Region (width : ℕ) (position : ℤ) (tape : Turing.Tape Symbol) : Prop :=
  ∀ index : ℤ, index < 0 ∨ (width : ℤ) ≤ index → tape.nth (index - position) = 0

/-- The blank surroundings remain blank at every execution boundary. -/
theorem Runs.region {width : TapeName → ℕ} {readOnly : TapeName → Bool}
    {machine : Machine (Alphabet TapeName) State}
    {ticks state finalState position finalPosition tapes finalTapes}
    (trace : Runs width readOnly machine ticks state position tapes
      finalState finalPosition finalTapes)
    (name : TapeName) (initial : Region (width name) (position name) (tapes name)) :
    Region (width name) (finalPosition name) (finalTapes name) := by
  intro index outside
  rw [trace.preserves name index (Or.inr outside)]
  exact initial index outside

/-- A canonical binary word contains no blank cell inside its fixed width. -/
theorem word_nth_blank_iff (bits : List Bool) (index : ℤ) :
    (Turing.Tape.mk' (Turing.ListBlank.mk [0]) (Turing.ListBlank.mk (word bits ++ [0]))).nth index = 0 ↔
      index < 0 ∨ (bits.length : ℤ) ≤ index := by
  cases index with
  | ofNat index =>
    simp only [Int.ofNat_eq_natCast, Turing.Tape.mk'_nth_nat,
      Turing.ListBlank.nth_mk]
    by_cases inside : index < bits.length
    · have wordInside : index < (word bits).length := by simpa [word] using inside
      rw [List.getI_append _ _ _ wordInside, List.getI_eq_getElem (word bits) wordInside]
      simp only [word, List.getElem_map]
      have nonblank : data bits[index] ≠ 0 := by cases bits[index] <;> decide
      simp only [nonblank, false_iff]
      omega
    · have outside : (word bits).length ≤ index := by simpa [word] using Nat.le_of_not_gt inside
      rw [List.getI_append_right _ _ _ outside]
      have zero : ([0] : List Symbol).getI (index - (word bits).length) = 0 := by
        cases index - (word bits).length <;> rfl
      rw [zero]
      simp only [true_iff]
      omega
  | negSucc index =>
    simp only [Turing.Tape.nth,
      Turing.Tape.mk'_left, Turing.ListBlank.nth_mk]
    have zero : ([0] : List Symbol).getI index = 0 := by cases index <;> rfl
    rw [zero]
    simp

/-- Canonical data begin at the head, with blank cells on both sides. -/
def tape (bits : List Bool) : Turing.Tape Symbol := Turing.Tape.mk₁ (word bits)

/-- Arbitrary initial contents occupy the output's declared width. -/
def buffer (contents : List Symbol) : Turing.Tape Symbol := Turing.Tape.mk₁ contents

/-- The existing bit encoding determines the complete argument tape. -/
noncomputable def encoded {Parameter : Type parameterLevel} [Fintype Parameter]
    (domain : EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (assignment : Parameter → ℕ) (value : domain.Carrier assignment) : Turing.Tape Symbol :=
  tape (EncodedDomain.ArrayEncoding.bits (domain.encode assignment value))

/-- Lifting a fixed codec to runtime sizes preserves its tape. -/
@[simp] theorem encoded_constant {Parameter : Type parameterLevel} [Fintype Parameter]
    (domain : EncodedDomain.{0, carrierLevel} Empty) (assignment : Parameter → ℕ)
    (value : domain.Carrier Empty.elim) :
    encoded domain.constant assignment value = encoded domain Empty.elim value := by
  simp only [encoded, EncodedDomain.constant, EncodedDomain.ofCodec,
    EncodedDomain.ArrayEncoding.bits_cast]

/-- Size parameters are immutable unary words; zero uses the empty region. -/
def unary (count : ℕ) : Turing.Tape Symbol := tape (List.replicate count true)

/-- The unary size domain and the physical size-tape convention agree. -/
theorem encoded_unary {Parameter : Type parameterLevel} [Fintype Parameter]
    (parameter : Parameter) (assignment : Parameter → ℕ) :
    encoded (EncodedDomain.unary.{parameterLevel, carrierLevel} parameter) assignment PUnit.unit = unary (assignment parameter) := by
  have equal : (fun index : Fin (assignment parameter) =>
      (BitVec.allOnes (assignment parameter)).getLsbD index.val) = fun _ => true := by
    funext index
    simp [index.isLt]
  simp only [encoded, EncodedDomain.unary, EncodedDomain.ofCodec]
  rw [EncodedDomain.ArrayEncoding.bits_cast]
  simp only [EncodedDomain.ArrayEncoding.bits, equal, List.ofFn_const, unary]

/-- Explicit surrounding blanks describe the same tape as the canonical buffer. -/
theorem buffer_padding (contents : List Symbol) :
    Turing.Tape.mk' (Turing.ListBlank.mk [0]) (Turing.ListBlank.mk (contents ++ [0])) =
      buffer contents := by
  have left : Turing.ListBlank.mk ([0] : List Symbol) = Turing.ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  have right : Turing.ListBlank.mk (contents ++ [0]) = Turing.ListBlank.mk contents :=
    Quotient.sound (Or.inr ⟨1, by simp⟩)
  simp only [left, right, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂]

variable {Parameter : Type parameterLevel} [Fintype Parameter]

/-- The Boolean encoded domain uses exactly one binary symbol. -/
theorem encoded_booleans (assignment : Parameter → ℕ) (flag : Bool) :
    encoded (EncodedDomain.booleans (Parameter := Parameter)) assignment flag = buffer [data flag] := by
  simp only [encoded, EncodedDomain.booleans, EncodedDomain.fixed,
    EncodedDomain.ofCodec, EncodedDomain.ArrayEncoding.bits_cast]
  norm_num [EncodedDomain.ArrayEncoding.bits, finTwoEquiv,
    tape, buffer, word, data, List.ofFn_succ]
  cases flag <;> rfl

/-- Bounded naturals retain their little-endian digit word. -/
@[simp] theorem encoded_binaryNaturals_value (parameter : Parameter) (assignment : Parameter → ℕ)
    (value : Fin (2 ^ assignment parameter)) :
    encoded (EncodedDomain.binaryNaturals parameter) assignment value =
      tape (EncodedDomain.ArrayEncoding.bits (BitVec.ofFin value)) := by
  simp only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
    EncodedDomain.ArrayEncoding.bits_cast]

/-- Canonical bounded-natural encodings agree with the arithmetic bit words. -/
theorem encoded_binaryNaturals (parameter : Parameter) (assignment : Parameter → ℕ) (bits : List Bool)
    (sameLength : bits.length = assignment parameter) :
    encoded (EncodedDomain.binaryNaturals parameter) assignment
      (⟨Binary.value bits, by simpa only [sameLength] using Binary.value_lt_pow_length bits⟩ :
        Fin (2 ^ assignment parameter)) = buffer (word bits) := by
  simp only [encoded, EncodedDomain.binaryNaturals, EncodedDomain.ofCodec,
    EncodedDomain.ArrayEncoding.bits_cast]
  change buffer (word (List.ofFn (fun index : Fin (assignment parameter) =>
    (BitVec.ofFin ⟨Binary.value bits, _⟩).getLsbD index.val))) = buffer (word bits)
  rw [← BitVec.ofNat_finVal]
  congr 2
  exact Binary.bits_value bits sameLength


/-- Logical arguments are exactly the values on the read-only argument tapes. -/
abbrev Inputs (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (assignment : Parameter → ℕ) :=
  (name : {name // readOnly name = true}) → (domains name.val).Carrier assignment

/-- Inputs are canonical; output and scratch regions initially contain anything. -/
def Entry (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (assignment : Parameter → ℕ)
    (values : Inputs domains readOnly assignment) (tapes : Tapes (Alphabet TapeName)) : Prop :=
  (∀ name (readOnlyProof : readOnly name = true), tapes name = encoded (domains name) assignment (values ⟨name, readOnlyProof⟩)) ∧
    ∀ name, readOnly name = false → ∃ contents : List Symbol,
      contents.length = (domains name).width assignment ∧ tapes name = buffer contents

-- outputNameLevel: names of public results, distinct from private writable storage.
universe outputNameLevel
variable {OutputName : Type outputNameLevel}

/-- Only declared public result tapes contribute mathematical output values. -/
abbrev Outputs (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (outputTapes : OutputName ↪ TapeName) (assignment : Parameter → ℕ) :=
  (name : OutputName) → (domains (outputTapes name)).Carrier assignment

/-- Public results are canonical on return. Private scratch is not inspected. -/
def Exit (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (outputTapes : OutputName ↪ TapeName) (assignment : Parameter → ℕ)
    (values : Outputs domains outputTapes assignment) (tapes : Tapes (Alphabet TapeName)) : Prop :=
  ∀ name, tapes (outputTapes name) = encoded (domains (outputTapes name)) assignment (values name)

/-- Polynomial execution with canonical public outputs and arbitrary private
scratch contents. Validity is required only when exposed as an output or consumed
as a mathematical input, including a subroutine argument. Scratch has NO independent
validity obligation, even on return; its fixed region and restored head remain required. -/
def Realizes [Fintype TapeName] [Fintype State]
    (domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter)
    (readOnly : TapeName → Bool) (sizeTapes : Parameter ↪ TapeName)
    (outputTapes : OutputName ↪ TapeName)
    (machine : Machine (Alphabet TapeName) State) (entry exit : State)
    (hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop)
    (contract : ∀ assignment, Inputs domains readOnly assignment → Outputs domains outputTapes assignment → Prop) : Prop :=
  (∀ parameter, readOnly (sizeTapes parameter) = true) ∧
    (∀ name, readOnly (outputTapes name) = false) ∧
    (∀ symbols, machine exit symbols = none) ∧
      ∃ bound : MvPolynomial Parameter ℕ,
        ∀ assignment input initial, hypothesis assignment input → Entry domains readOnly assignment input initial →
          (∀ parameter, initial (sizeTapes parameter) = unary (assignment parameter)) →
          ∃ ticks output final, ticks ≤ MvPolynomial.eval assignment bound ∧
            Runs (fun name => (domains name).width assignment) readOnly machine ticks
              entry (fun _ => 0) initial exit (fun _ => 0) final ∧
            contract assignment input output ∧ Exit domains outputTapes assignment output final

/-- Derive an output contract using the mathematical input precondition. -/
theorem Realizes.postconditionWithHypothesis [Fintype TapeName] [Fintype State]
    {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizeTapes : Parameter ↪ TapeName}
    {outputTapes : OutputName ↪ TapeName}
    {machine : Machine (Alphabet TapeName) State} {entry exit : State}
    {hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop}
    {sourceContract targetContract : ∀ assignment, Inputs domains readOnly assignment →
      Outputs domains outputTapes assignment → Prop}
    (realizes : Realizes domains readOnly sizeTapes outputTapes machine entry exit hypothesis sourceContract)
    (implies : ∀ assignment input output, hypothesis assignment input →
      sourceContract assignment input output → targetContract assignment input output) :
    Realizes domains readOnly sizeTapes outputTapes machine entry exit hypothesis targetContract := by
  obtain ⟨sizeReadOnly, outputsWritable, halts, bound, execute⟩ := realizes
  refine ⟨sizeReadOnly, outputsWritable, halts, bound, ?_⟩
  intro assignment input initial valid represented headers
  obtain ⟨ticks, output, final, cost, trace, correct, canonical⟩ :=
    execute assignment input initial valid represented headers
  exact ⟨ticks, output, final, cost, trace, implies assignment input output valid correct, canonical⟩

/-- Apply a mathematical consequence without changing execution evidence. -/
theorem Realizes.postcondition [Fintype TapeName] [Fintype State]
    {domains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    {readOnly : TapeName → Bool} {sizeTapes : Parameter ↪ TapeName}
    {outputTapes : OutputName ↪ TapeName}
    {machine : Machine (Alphabet TapeName) State} {entry exit : State}
    {hypothesis : ∀ assignment, Inputs domains readOnly assignment → Prop}
    {sourceContract targetContract : ∀ assignment, Inputs domains readOnly assignment →
      Outputs domains outputTapes assignment → Prop}
    (realizes : Realizes domains readOnly sizeTapes outputTapes machine entry exit hypothesis sourceContract)
    (implies : ∀ assignment input output, sourceContract assignment input output → targetContract assignment input output) :
    Realizes domains readOnly sizeTapes outputTapes machine entry exit hypothesis targetContract :=
  realizes.postconditionWithHypothesis (fun assignment input output _ correct =>
    implies assignment input output correct)

/-- Reindex mathematical tape carriers without changing the encoded machine
layout. This lets a routine proved on a flat array serve a structured domain. -/
theorem realizes_reindex [Fintype TapeName] [Fintype State]
    {sourceDomains targetDomains : TapeName → EncodedDomain.{parameterLevel, carrierLevel} Parameter}
    (equivalence : ∀ name assignment,
      (targetDomains name).Carrier assignment ≃ (sourceDomains name).Carrier assignment)
    (widthEqual : ∀ name assignment,
      (targetDomains name).width assignment = (sourceDomains name).width assignment)
    (encodingEqual : ∀ name assignment (value : (targetDomains name).Carrier assignment),
      encoded (targetDomains name) assignment value =
        encoded (sourceDomains name) assignment (equivalence name assignment value))
    (readOnly : TapeName → Bool) (sizeTapes : Parameter ↪ TapeName)
    (outputTapes : OutputName ↪ TapeName)
    (machine : Machine (Alphabet TapeName) State) (entry exit : State)
    (targetHypothesis : ∀ assignment, Inputs targetDomains readOnly assignment → Prop)
    (sourceHypothesis : ∀ assignment, Inputs sourceDomains readOnly assignment → Prop)
    (targetContract : ∀ assignment, Inputs targetDomains readOnly assignment →
      Outputs targetDomains outputTapes assignment → Prop)
    (sourceContract : ∀ assignment, Inputs sourceDomains readOnly assignment →
      Outputs sourceDomains outputTapes assignment → Prop)
    (hypothesisMaps : ∀ assignment (input : Inputs targetDomains readOnly assignment),
      targetHypothesis assignment input →
        sourceHypothesis assignment (fun name => equivalence name.val assignment (input name)))
    (contractMaps : ∀ assignment (input : Inputs targetDomains readOnly assignment)
      (output : Outputs sourceDomains outputTapes assignment),
      sourceContract assignment
        (fun name => equivalence name.val assignment (input name)) output →
      targetContract assignment input
        (fun name => (equivalence (outputTapes name) assignment).symm (output name)))
    (sourceRealizes : Realizes sourceDomains readOnly sizeTapes outputTapes machine entry exit
      sourceHypothesis sourceContract) :
    Realizes targetDomains readOnly sizeTapes outputTapes machine entry exit
      targetHypothesis targetContract := by
  obtain ⟨sizeInputsReadOnly, outputsWritable, exits, bound, sourceRuns⟩ := sourceRealizes
  refine ⟨sizeInputsReadOnly, outputsWritable, exits, bound, ?_⟩
  intro assignment input initial validInput targetEntry sizeInput
  let sourceInput : Inputs sourceDomains readOnly assignment :=
    fun name => equivalence name.val assignment (input name)
  have sourceEntry : Entry sourceDomains readOnly assignment sourceInput initial := by
    constructor
    · intro name readOnlyProof
      rw [targetEntry.1 name readOnlyProof]
      exact encodingEqual name assignment (input ⟨name, readOnlyProof⟩)
    · intro name writable
      obtain ⟨contents, length, tapeEq⟩ := targetEntry.2 name writable
      refine ⟨contents, ?_, tapeEq⟩
      simpa only [widthEqual name assignment] using length
  obtain ⟨ticks, sourceOutput, final, cost, trace, correctness, sourceExit⟩ :=
    sourceRuns assignment sourceInput initial (hypothesisMaps assignment input validInput)
      sourceEntry sizeInput
  let targetOutput : Outputs targetDomains outputTapes assignment :=
    fun name => (equivalence (outputTapes name) assignment).symm (sourceOutput name)
  have targetWidths : (fun name => (targetDomains name).width assignment) =
      fun name => (sourceDomains name).width assignment := by
    funext name
    exact widthEqual name assignment
  have targetTrace : Runs (fun name => (targetDomains name).width assignment) readOnly
      machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final := by
    rw [targetWidths]
    exact trace
  refine ⟨ticks, targetOutput, final, cost, targetTrace,
    contractMaps assignment input sourceOutput correctness, ?_⟩
  intro name
  rw [sourceExit name]
  have outputEqual : equivalence (outputTapes name) assignment (targetOutput name) =
      sourceOutput name := by simp [targetOutput]
  have encodedEqual := encodingEqual (outputTapes name) assignment (targetOutput name)
  rw [outputEqual] at encodedEqual
  exact encodedEqual.symm

end Polytime2.CallingConvention
