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
import Polytime2.Contracts
import Polytime2.While

/-! # Mathematical guarded loops and searches

Logical invariants and measures are separate from physical scratch. A conserved
answer connects a loop to its mathematical result without supplying loop fuel.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape roles; symbolLevel: symbols; valueLevel: logical states.
-- guardLevel/bodyLevel: component controllers; answerLevel: mathematical results.
universe tapeLevel symbolLevel valueLevel guardLevel bodyLevel answerLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {Value : Type valueLevel} {Answer : Type answerLevel}
variable {Guard : Type guardLevel} {Body : Type bodyLevel}

/-- A guard-driven loop preserves its mathematical answer and stops within a
bound obtained from a decreasing logical measure. -/
theorem search_steps (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols Alphabet → Bool)
    (representation guardedRepresentation : Value → Tapes Alphabet → Prop)
    (condition : Value → Bool) (invariant : Value → Prop)
    (advance : Value → Value) (measure : Value → ℕ) (answer : Value → Answer)
    (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ value initial, invariant value → representation value initial →
      ∃ ticks final, ticks ≤ guardBound ∧
        Steps guard ticks (guardEntry, initial) (guardExit, final) ∧ guardedRepresentation value final)
    (bodyRuns : ∀ value initial, invariant value → condition value = true →
      guardedRepresentation value initial → ∃ ticks final, ticks ≤ bodyBound ∧
        Steps body ticks (bodyEntry, initial) (bodyExit, final) ∧ representation (advance value) final)
    (resultCorrect : ∀ value tapes, guardedRepresentation value tapes → result (read tapes) = condition value)
    (preserves : ∀ value, invariant value → condition value = true → invariant (advance value))
    (decreases : ∀ value, invariant value → condition value = true → measure (advance value) < measure value)
    (conserves : ∀ value, invariant value → condition value = true → answer (advance value) = answer value)
    (value : Value) (initial : Tapes Alphabet) (valid : invariant value)
    (represented : representation value initial) :
    ∃ ticks final terminal, ticks ≤ (measure value + 1) * (guardBound + bodyBound + 2) ∧
      Steps (whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry, initial) (.inl guardExit, final) ∧
      guardedRepresentation terminal final ∧ invariant terminal ∧
      condition terminal = false ∧ answer terminal = answer value := by
  generalize ranking : measure value = remaining
  induction remaining using Nat.strong_induction_on generalizing value initial with
  | h remaining hypothesis =>
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardEncoded⟩ :=
      guardRuns value initial valid represented
    have liftedGuard := guardTrace.rename Sum.inl
      (target := whileMachine guard body guardEntry bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    have tested := resultCorrect value guarded guardEncoded
    cases active : condition value with
    | false =>
      refine ⟨guardTicks, guarded, value, ?_, liftedGuard, guardEncoded, valid, active, rfl⟩
      have dominates := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show 1 ≤ remaining + 1 by omega)
      simp only [one_mul] at dominates
      omega
    | true =>
      obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, bodyEncoded⟩ :=
        bodyRuns value guarded valid active guardEncoded
      have smaller : measure (advance value) < remaining := by
        have progress := decreases value valid active
        omega
      obtain ⟨restTicks, final, terminal, restCost, restTrace, finalEncoded,
        finalValid, stopped, sameAnswer⟩ :=
        hypothesis (measure (advance value)) smaller (advance value) advanced
          (preserves value valid active) bodyEncoded rfl
      have liftedBody := bodyTrace.rename Sum.inr
        (target := whileMachine guard body guardEntry bodyEntry result)
        (by intro state symbols next actions transition; simp [whileMachine, transition])
      have toBody : step (whileMachine guard body guardEntry bodyEntry result)
          (.inl guardExit, guarded) = some (.inr bodyEntry, guarded) := by
        simp [step, whileMachine, guardHalt, tested, active]
      have toGuard : step (whileMachine guard body guardEntry bodyEntry result)
          (.inr bodyExit, advanced) = some (.inl guardEntry, advanced) := by
        simp [step, whileMachine, bodyHalt]
      refine ⟨guardTicks + (bodyTicks + (restTicks + 1) + 1), final, terminal, ?_,
        liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace))),
        finalEncoded, finalValid, stopped, sameAnswer.trans (conserves value valid active)⟩
      have dominated := Nat.mul_le_mul_right (guardBound + bodyBound + 2)
        (show measure (advance value) + 1 ≤ remaining by omega)
      calc
        guardTicks + (bodyTicks + (restTicks + 1) + 1) ≤
            (guardBound + bodyBound + 2) + remaining * (guardBound + bodyBound + 2) := by omega
        _ = (remaining + 1) * (guardBound + bodyBound + 2) := by ring

namespace Computes

-- parameterLevel: size names; familyLevel: logical state families.
-- outputLevel: mathematical result families.
universe parameterLevel familyLevel outputLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
variable [∀ name, Fintype (Alphabet name)] [Fintype Guard] [Fintype Body]
variable {Family : (Parameter → ℕ) → Type familyLevel}
variable {Output : (Parameter → ℕ) → Type outputLevel}

/-- Mathematical while rule. Users supply invariants, decreasing measures and
terminal correctness; polynomial costs and handovers remain internal. -/
theorem whileLoop
    {guard : Machine Alphabet Guard} {body : Machine Alphabet Body}
    {guardEntry guardExit : Guard} {bodyEntry bodyExit : Body}
    (result : Symbols Alphabet → Bool)
    (representation guardedRepresentation : ∀ assignment, Family assignment → Tapes Alphabet → Prop)
    (outputRepresentation : ∀ assignment, Output assignment → Tapes Alphabet → Prop)
    (condition : ∀ assignment, Family assignment → Bool)
    (invariant : ∀ assignment, Family assignment → Prop)
    (advance : ∀ assignment, Family assignment → Family assignment)
    (measure : ∀ assignment, Family assignment → ℕ)
    (answer : ∀ assignment, Family assignment → Output assignment)
    (guardCertificate : Computes guard guardEntry guardExit representation guardedRepresentation invariant
      (fun _ value => value))
    (bodyCertificate : Computes body bodyEntry bodyExit guardedRepresentation representation
      (fun assignment value => invariant assignment value ∧ condition assignment value = true) advance)
    (resultCorrect : ∀ assignment value tapes, guardedRepresentation assignment value tapes →
      result (read tapes) = condition assignment value)
    (preserves : ∀ assignment value, invariant assignment value → condition assignment value = true →
      invariant assignment (advance assignment value))
    (decreases : ∀ assignment value, invariant assignment value → condition assignment value = true →
      measure assignment (advance assignment value) < measure assignment value)
    (conserves : ∀ assignment value, invariant assignment value → condition assignment value = true →
      answer assignment (advance assignment value) = answer assignment value)
    (terminalCorrect : ∀ assignment value tapes, invariant assignment value → condition assignment value = false →
      guardedRepresentation assignment value tapes → outputRepresentation assignment (answer assignment value) tapes)
    (bounded : ∃ capacity : MvPolynomial Parameter ℕ, ∀ assignment value,
      invariant assignment value → measure assignment value ≤ MvPolynomial.eval assignment capacity) :
    Computes (withExit (whileMachine guard body guardEntry bodyEntry result))
      (.inl (.inl guardEntry)) (.inr ()) representation outputRepresentation invariant answer := by
  obtain ⟨guardHalt, guardBound, guardRuns⟩ := guardCertificate
  obtain ⟨bodyHalt, bodyBound, bodyRuns⟩ := bodyCertificate
  obtain ⟨capacity, capacityBound⟩ := bounded
  refine ⟨by intro symbols; rfl, (capacity + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro assignment value initial valid represented
  obtain ⟨ticks, final, terminal, cost, trace, encoded, finalValid, stopped, sameAnswer⟩ :=
    search_steps guard body guardEntry guardExit bodyEntry bodyExit result
      (representation assignment) (guardedRepresentation assignment) (condition assignment)
      (invariant assignment) (advance assignment) (measure assignment) (answer assignment)
      (MvPolynomial.eval assignment guardBound) (MvPolynomial.eval assignment bodyBound)
      guardHalt bodyHalt (guardRuns assignment)
      (by intro value tapes good active encoding; exact bodyRuns assignment value tapes ⟨good, active⟩ encoding)
      (resultCorrect assignment) (preserves assignment) (decreases assignment) (conserves assignment)
      value initial valid represented
  have halt : step (whileMachine guard body guardEntry bodyEntry result) (.inl guardExit, final) = none := by
    simp [step, whileMachine, guardHalt, resultCorrect _ _ _ encoded, stopped]
  refine ⟨ticks + 1, final, ?_, withExit_steps _ trace halt, ?_⟩
  · have capacityCost := Nat.mul_le_mul_right
      (MvPolynomial.eval assignment guardBound + MvPolynomial.eval assignment bodyBound + 2)
      (Nat.add_le_add_right (capacityBound assignment value valid) 1)
    simp only [map_add, map_mul, map_one, map_ofNat]
    omega
  · rw [← sameAnswer]
    exact terminalCorrect assignment terminal final finalValid stopped encoded

/-- Early-stopping search: a bounded index advances once per active iteration.
The conserved answer may describe a first match, a sentinel, or another result. -/
theorem search
    {guard : Machine Alphabet Guard} {body : Machine Alphabet Body}
    {guardEntry guardExit : Guard} {bodyEntry bodyExit : Body}
    (result : Symbols Alphabet → Bool)
    (representation guardedRepresentation : ∀ assignment, Family assignment → Tapes Alphabet → Prop)
    (outputRepresentation : ∀ assignment, Output assignment → Tapes Alphabet → Prop)
    (length : (Parameter → ℕ) → ℕ) (index : ∀ assignment, Family assignment → ℕ)
    (condition : ∀ assignment, Family assignment → Bool)
    (invariant : ∀ assignment, Family assignment → Prop)
    (advance : ∀ assignment, Family assignment → Family assignment)
    (answer : ∀ assignment, Family assignment → Output assignment)
    (guardCertificate : Computes guard guardEntry guardExit representation guardedRepresentation invariant
      (fun _ value => value))
    (bodyCertificate : Computes body bodyEntry bodyExit guardedRepresentation representation
      (fun assignment value => invariant assignment value ∧ condition assignment value = true) advance)
    (resultCorrect : ∀ assignment value tapes, guardedRepresentation assignment value tapes →
      result (read tapes) = condition assignment value)
    (continues : ∀ assignment value, invariant assignment value → condition assignment value = true →
      index assignment value < length assignment)
    (preserves : ∀ assignment value, invariant assignment value → condition assignment value = true →
      invariant assignment (advance assignment value))
    (advances : ∀ assignment value, invariant assignment value → condition assignment value = true →
      index assignment (advance assignment value) = index assignment value + 1)
    (conserves : ∀ assignment value, invariant assignment value → condition assignment value = true →
      answer assignment (advance assignment value) = answer assignment value)
    (terminalCorrect : ∀ assignment value tapes, invariant assignment value → condition assignment value = false →
      guardedRepresentation assignment value tapes → outputRepresentation assignment (answer assignment value) tapes)
    (bounded : ∃ capacity : MvPolynomial Parameter ℕ,
      ∀ assignment, length assignment ≤ MvPolynomial.eval assignment capacity) :
    Computes (withExit (whileMachine guard body guardEntry bodyEntry result))
      (.inl (.inl guardEntry)) (.inr ()) representation outputRepresentation invariant answer := by
  apply whileLoop result representation guardedRepresentation outputRepresentation condition invariant advance
    (fun assignment value => length assignment - index assignment value) answer
    guardCertificate bodyCertificate resultCorrect preserves
  · intro assignment value good active
    have inside := continues assignment value good active
    have progress := advances assignment value good active
    omega
  · exact conserves
  · exact terminalCorrect
  · obtain ⟨capacity, capacityBound⟩ := bounded
    exact ⟨capacity, fun assignment value _ => (Nat.sub_le _ _).trans (capacityBound assignment)⟩

end Computes
end Polytime2.MultiTape
