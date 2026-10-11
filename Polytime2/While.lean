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

/-! # Guard-driven loops with polynomial progress certificates

The guard leaves its result under the tape heads. A decreasing measure is
mathematical proof data only: the machine never reads a measure or a fuel bound.
The controller construction uses independent multi-tape execution semantics.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape names; symbolLevel: alphabets; guardLevel, bodyLevel: controllers.
universe tapeLevel symbolLevel guardLevel bodyLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {Guard : Type guardLevel} {Body : Type bodyLevel}

def whileMachine (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry : Guard) (bodyEntry : Body) (result : Symbols Alphabet → Bool) :
    Machine Alphabet (Sum Guard Body)
  | .inl state, symbols => match guard state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => if result symbols then some (.inr bodyEntry, stationary symbols) else none
  | .inr state, symbols => match body state symbols with
    | some (next, actions) => some (.inr next, actions)
    | none => some (.inl guardEntry, stationary symbols)

/-- Guard and body costs include all tape work; each iteration adds two handovers. -/
theorem while_steps (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols Alphabet → Bool) (invariant : Tapes Alphabet → Prop)
    (measure : Tapes Alphabet → ℕ) (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ initial, invariant initial → ∃ ticks final,
      ticks ≤ guardBound ∧ Steps guard ticks (guardEntry, initial) (guardExit, final) ∧
        invariant final ∧ measure final ≤ measure initial)
    (bodyRuns : ∀ initial, invariant initial → result (read initial) = true → ∃ ticks final,
      ticks ≤ bodyBound ∧ Steps body ticks (bodyEntry, initial) (bodyExit, final) ∧
        invariant final ∧ measure final < measure initial)
    (initial : Tapes Alphabet) (valid : invariant initial) :
    ∃ ticks final, ticks ≤ (measure initial + 1) * (guardBound + bodyBound + 2) ∧
      Steps (whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry, initial) (.inl guardExit, final) ∧
      invariant final ∧ result (read final) = false := by
  generalize ranking : measure initial = rank
  induction rank using Nat.strong_induction_on generalizing initial with
  | h rank hypothesis =>
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardedValid, guardMeasure⟩ := guardRuns initial valid
    have liftedGuard := guardTrace.rename Sum.inl
      (target := whileMachine guard body guardEntry bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
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
        (target := whileMachine guard body guardEntry bodyEntry result)
        (by intro state symbols next actions transition; simp [whileMachine, transition])
      have toBody : step (whileMachine guard body guardEntry bodyEntry result)
          (.inl guardExit, guarded) = some (.inr bodyEntry, guarded) := by
        simp [step, whileMachine, guardHalt, tested]
      have toGuard : step (whileMachine guard body guardEntry bodyEntry result)
          (.inr bodyExit, advanced) = some (.inl guardEntry, advanced) := by
        simp [step, whileMachine, bodyHalt]
      have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
      refine ⟨guardTicks + (bodyTicks + (restTicks + 1) + 1), final, ?_, trace, finalValid, stopped⟩
      have dominated := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show measure advanced + 1 ≤ rank by omega)
      calc
        guardTicks + (bodyTicks + (restTicks + 1) + 1) ≤
            (guardBound + bodyBound + 2) + rank * (guardBound + bodyBound + 2) := by omega
        _ = (rank + 1) * (guardBound + bodyBound + 2) := by ring

namespace Realizes

-- parameterLevel: runtime size names.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
variable [∀ name, Fintype (Alphabet name)] [Fintype Guard] [Fintype Body]

/-- A polynomial initial progress bound and certified guard/body imply polynomial runtime. -/
theorem whileLoop (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols Alphabet → Bool)
    (invariant : (Parameter → ℕ) → Tapes Alphabet → Prop)
    (measure : (Parameter → ℕ) → Tapes Alphabet → ℕ)
    (iterations : MvPolynomial Parameter ℕ)
    (guardRealizes : Realizes guard guardEntry guardExit invariant
      (fun assignment initial final => invariant assignment final ∧
        measure assignment final ≤ measure assignment initial))
    (bodyRealizes : Realizes body bodyEntry bodyExit
      (fun assignment tapes => invariant assignment tapes ∧ result (read tapes) = true)
      (fun assignment initial final => invariant assignment final ∧
        measure assignment final < measure assignment initial)) :
    Realizes (withExit (whileMachine guard body guardEntry bodyEntry result))
      (.inl (.inl guardEntry)) (.inr ())
      (fun assignment tapes => invariant assignment tapes ∧
        measure assignment tapes ≤ MvPolynomial.eval assignment iterations)
      (fun assignment _ final => invariant assignment final ∧ result (read final) = false) := by
  obtain ⟨guardHalt, guardBound, guardRuns⟩ := guardRealizes
  obtain ⟨bodyHalt, bodyBound, bodyRuns⟩ := bodyRealizes
  refine ⟨by intro symbols; rfl, (iterations + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro assignment initial valid
  obtain ⟨ticks, final, cost, trace, finalValid, stopped⟩ :=
    while_steps guard body guardEntry guardExit bodyEntry bodyExit result (invariant assignment)
      (measure assignment) (MvPolynomial.eval assignment guardBound) (MvPolynomial.eval assignment bodyBound)
      guardHalt bodyHalt (guardRuns assignment)
      (by intro tapes good active; exact bodyRuns assignment tapes ⟨good, active⟩) initial valid.1
  have halt : step (whileMachine guard body guardEntry bodyEntry result) (.inl guardExit, final) = none := by
    simp [step, whileMachine, guardHalt, stopped]
  refine ⟨ticks + 1, final, ?_, withExit_steps _ trace halt, finalValid, stopped⟩
  · simp only [map_mul, map_add, map_one, map_ofNat]
    exact Nat.add_le_add_right
      (cost.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right valid.2 1))) 1

end Realizes
end Polytime2.MultiTape
