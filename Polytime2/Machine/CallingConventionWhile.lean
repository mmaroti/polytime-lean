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

import Polytime2.Machine.CallingConvention

/-! # Safe guarded loops over mathematical states

The guard's representation is separate from the loop-state representation.
Private scratch is never required to represent mathematical values.
-/

namespace Polytime2.CallingConvention.Runs

open MultiTape

-- tapeLevel: tape names; guardLevel/bodyLevel: controllers; valueLevel: logical states.
universe tapeLevel guardLevel bodyLevel valueLevel
variable {TapeName : Type tapeLevel} {Guard : Type guardLevel} {Body : Type bodyLevel}
variable {Value : Type valueLevel}

/-- A mathematical decreasing measure bounds iterations. The guard preserves
its logical state; the body returns a smaller state with the required invariant.
`Value` may be a dependent family of mathematical variables. Immutable context
is captured by the representations, so it need not be copied into the state.
Only live variables need encodings; the `Runs` certificate bounds scratch
regions and preserves read-only tapes independently of their contents. -/
theorem whileValues_at (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (guard : Machine (Alphabet TapeName) Guard) (body : Machine (Alphabet TapeName) Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols (Alphabet TapeName) → Bool)
    (representation guardedRepresentation : Value → Tapes (Alphabet TapeName) → Prop)
    (headPosition : Value → TapeName → ℤ)
    (condition : Value → Bool) (measure : Value → ℕ) (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ value initial, representation value initial → ∃ ticks final,
      ticks ≤ guardBound ∧ Runs width readOnly guard ticks guardEntry (headPosition value) initial
        guardExit (headPosition value) final ∧ guardedRepresentation value final)
    (bodyRuns : ∀ value initial, guardedRepresentation value initial → condition value = true →
      ∃ nextValue ticks final, ticks ≤ bodyBound ∧
        Runs width readOnly body ticks bodyEntry (headPosition value) initial bodyExit (headPosition nextValue) final ∧
        representation nextValue final ∧ measure nextValue < measure value)
    (resultCorrect : ∀ value tapes, guardedRepresentation value tapes →
      result (read tapes) = condition value)
    (value : Value) (initial : Tapes (Alphabet TapeName)) (represented : representation value initial) :
    ∃ ticks final terminal, ticks ≤ (measure value + 1) * (guardBound + bodyBound + 2) ∧
      Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry) (headPosition value) initial (.inl guardExit) (headPosition terminal) final ∧
      guardedRepresentation terminal final ∧ condition terminal = false := by
  generalize ranking : measure value = rank
  induction rank using Nat.strong_induction_on generalizing value initial with
  | h rank hypothesis =>
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardedValid⟩ := guardRuns value initial represented
    have liftedGuard := guardTrace.rename Sum.inl
      (target := MultiTape.whileMachine guard body guardEntry bodyEntry result)
      (by intro state symbols next actions transition; simp [MultiTape.whileMachine, transition])
    cases tested : condition value with
    | false =>
      refine ⟨guardTicks, guarded, value, ?_, liftedGuard, guardedValid, tested⟩
      have dominates := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show 1 ≤ rank + 1 by omega)
      simp only [one_mul] at dominates
      omega
    | true =>
      obtain ⟨nextValue, bodyTicks, advanced, bodyCost, bodyTrace, advancedValid, smaller⟩ :=
        bodyRuns value guarded guardedValid tested
      obtain ⟨restTicks, final, terminal, restCost, restTrace, finalValid, stopped⟩ :=
        hypothesis (measure nextValue) (by omega) nextValue advanced advancedValid rfl
      have liftedBody := bodyTrace.rename Sum.inr
        (target := MultiTape.whileMachine guard body guardEntry bodyEntry result)
        (by intro state symbols next actions transition; simp [MultiTape.whileMachine, transition])
      have toBody : Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) 1
          (.inl guardExit) (headPosition value) guarded (.inr bodyEntry) (headPosition value) guarded := by
        apply Runs.next (nextState := Sum.inr bodyEntry) (actions := stationary (read guarded))
          (by simp [MultiTape.whileMachine, guardHalt, resultCorrect value guarded guardedValid, tested])
          (by intro name premise; rfl)
        simpa only [stationary, displacement, add_zero, act_stationary] using
          (Runs.zero (machine := MultiTape.whileMachine guard body guardEntry bodyEntry result)
            (.inr bodyEntry) (headPosition value) guarded)
      have toGuard : Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) 1
          (.inr bodyExit) (headPosition nextValue) advanced (.inl guardEntry) (headPosition nextValue) advanced := by
        apply Runs.next (nextState := Sum.inl guardEntry) (actions := stationary (read advanced))
          (by simp [MultiTape.whileMachine, bodyHalt]) (by intro name premise; rfl)
        simpa only [stationary, displacement, add_zero, act_stationary] using
          (Runs.zero (machine := MultiTape.whileMachine guard body guardEntry bodyEntry result)
            (.inl guardEntry) (headPosition nextValue) advanced)
      refine ⟨guardTicks + (1 + (bodyTicks + (1 + restTicks))), final, terminal, ?_,
        liftedGuard.trans (toBody.trans (liftedBody.trans (toGuard.trans restTrace))), finalValid, stopped⟩
      have dominated := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show measure nextValue + 1 ≤ rank by omega)
      calc
        guardTicks + (1 + (bodyTicks + (1 + restTicks))) ≤
            (guardBound + bodyBound + 2) + rank * (guardBound + bodyBound + 2) := by omega
        _ = (rank + 1) * (guardBound + bodyBound + 2) := by ring

/-- Restoring specialization of `whileValues_at`. -/
theorem whileValues (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (guard : Machine (Alphabet TapeName) Guard) (body : Machine (Alphabet TapeName) Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols (Alphabet TapeName) → Bool)
    (representation guardedRepresentation : Value → Tapes (Alphabet TapeName) → Prop)
    (condition : Value → Bool) (measure : Value → ℕ) (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ value initial, representation value initial → ∃ ticks final,
      ticks ≤ guardBound ∧ Runs width readOnly guard ticks guardEntry (fun _ => 0) initial
        guardExit (fun _ => 0) final ∧ guardedRepresentation value final)
    (bodyRuns : ∀ value initial, guardedRepresentation value initial → condition value = true →
      ∃ nextValue ticks final, ticks ≤ bodyBound ∧
        Runs width readOnly body ticks bodyEntry (fun _ => 0) initial bodyExit (fun _ => 0) final ∧
        representation nextValue final ∧ measure nextValue < measure value)
    (resultCorrect : ∀ value tapes, guardedRepresentation value tapes →
      result (read tapes) = condition value)
    (value : Value) (initial : Tapes (Alphabet TapeName)) (represented : representation value initial) :
    ∃ ticks final terminal, ticks ≤ (measure value + 1) * (guardBound + bodyBound + 2) ∧
      Runs width readOnly (MultiTape.whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry) (fun _ => 0) initial (.inl guardExit) (fun _ => 0) final ∧
      guardedRepresentation terminal final ∧ condition terminal = false :=
  whileValues_at width readOnly guard body guardEntry guardExit bodyEntry bodyExit result
    representation guardedRepresentation (fun _ _ => 0) condition measure guardBound bodyBound
    guardHalt bodyHalt guardRuns bodyRuns resultCorrect value initial represented

/-- Traverse a bounded interval using a caller's live-state representation.
The representation may describe any finite family of variables and immutable
context; scratch needs only the region conditions required by the components. -/
theorem whileRange_at (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (guard : Machine (Alphabet TapeName) Guard) (body : Machine (Alphabet TapeName) Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols (Alphabet TapeName) → Bool)
    (representation guardedRepresentation : ℕ → Tapes (Alphabet TapeName) → Prop)
    (headPosition : ℕ → TapeName → ℤ)
    (start limit guardBound bodyBound : ℕ) (within : start ≤ limit)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ count, start ≤ count → count ≤ limit → ∀ initial,
      representation count initial → ∃ ticks final, ticks ≤ guardBound ∧
        Runs width readOnly guard ticks guardEntry (headPosition count) initial
          guardExit (headPosition count) final ∧ guardedRepresentation count final)
    (bodyRuns : ∀ count, start ≤ count → count < limit → ∀ initial,
      guardedRepresentation count initial → ∃ ticks final, ticks ≤ bodyBound ∧
        Runs width readOnly body ticks bodyEntry (headPosition count) initial
          bodyExit (headPosition (count + 1)) final ∧ representation (count + 1) final)
    (resultCorrect : ∀ count, start ≤ count → count ≤ limit → ∀ tapes,
      guardedRepresentation count tapes → result (read tapes) = decide (count < limit))
    (initial : Tapes (Alphabet TapeName)) (represented : representation start initial) :
    ∃ ticks final, ticks ≤ (limit - start + 1) * (guardBound + bodyBound + 2) + 1 ∧
      Runs width readOnly
        (MultiTape.withExit (MultiTape.whileMachine guard body guardEntry bodyEntry result)) ticks
        (.inl (.inl guardEntry)) (headPosition start) initial (.inr ()) (headPosition limit) final ∧
      guardedRepresentation limit final := by
  let Value := {count : ℕ // start ≤ count ∧ count ≤ limit}
  obtain ⟨ticks, final, terminal, cost, trace, valid, stopped⟩ :=
    whileValues_at width readOnly guard body guardEntry guardExit bodyEntry bodyExit result
      (fun count : Value => representation count.val)
      (fun count : Value => guardedRepresentation count.val)
      (fun count : Value => headPosition count.val)
      (fun count : Value => decide (count.val < limit)) (fun count : Value => limit - count.val)
      guardBound bodyBound guardHalt bodyHalt
      (fun count tapes valid => guardRuns count.val count.property.1 count.property.2 tapes valid)
      (by
        intro count tapes valid active
        have before : count.val < limit := of_decide_eq_true active
        obtain ⟨ticks, final, cost, trace, next⟩ :=
          bodyRuns count.val count.property.1 before tapes valid
        exact ⟨⟨count.val + 1, by omega, by omega⟩, ticks, final, cost, trace, next, by dsimp; omega⟩)
      (fun count tapes valid => resultCorrect count.val count.property.1 count.property.2 tapes valid)
      ⟨start, le_rfl, within⟩ initial represented
  have finished : terminal.val = limit := by
    have upper := terminal.property.2
    have lower := of_decide_eq_false stopped
    omega
  refine ⟨ticks + 1, final, Nat.add_le_add_right cost 1, ?_, ?_⟩
  · simpa only [finished] using trace.withExit_at (by simp [MultiTape.whileMachine, guardHalt,
      resultCorrect terminal.val terminal.property.1 terminal.property.2 final valid, finished])
  · simpa only [finished] using valid

/-- Restoring specialization of `whileRange_at`. -/
theorem whileRange (width : TapeName → ℕ) (readOnly : TapeName → Bool)
    (guard : Machine (Alphabet TapeName) Guard) (body : Machine (Alphabet TapeName) Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols (Alphabet TapeName) → Bool)
    (representation guardedRepresentation : ℕ → Tapes (Alphabet TapeName) → Prop)
    (start limit guardBound bodyBound : ℕ) (within : start ≤ limit)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ count, start ≤ count → count ≤ limit → ∀ initial,
      representation count initial → ∃ ticks final, ticks ≤ guardBound ∧
        Runs width readOnly guard ticks guardEntry (fun _ => 0) initial
          guardExit (fun _ => 0) final ∧ guardedRepresentation count final)
    (bodyRuns : ∀ count, start ≤ count → count < limit → ∀ initial,
      guardedRepresentation count initial → ∃ ticks final, ticks ≤ bodyBound ∧
        Runs width readOnly body ticks bodyEntry (fun _ => 0) initial
          bodyExit (fun _ => 0) final ∧ representation (count + 1) final)
    (resultCorrect : ∀ count, start ≤ count → count ≤ limit → ∀ tapes,
      guardedRepresentation count tapes → result (read tapes) = decide (count < limit))
    (initial : Tapes (Alphabet TapeName)) (represented : representation start initial) :
    ∃ ticks final, ticks ≤ (limit - start + 1) * (guardBound + bodyBound + 2) + 1 ∧
      Runs width readOnly
        (MultiTape.withExit (MultiTape.whileMachine guard body guardEntry bodyEntry result)) ticks
        (.inl (.inl guardEntry)) (fun _ => 0) initial (.inr ()) (fun _ => 0) final ∧
      guardedRepresentation limit final :=
  whileRange_at width readOnly guard body guardEntry guardExit bodyEntry bodyExit result
    representation guardedRepresentation (fun _ _ => 0) start limit guardBound bodyBound within
    guardHalt bodyHalt guardRuns bodyRuns resultCorrect initial represented

end Polytime2.CallingConvention.Runs
