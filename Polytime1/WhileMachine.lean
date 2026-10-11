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

import Polytime1.TupleMachine

/-! # Certified guarded loops on finite tape controllers

The guard leaves its Boolean result at the head. A true guard hands the tape
to the body; the body returns to the guard. A false guard halts. Bounds belong
to the proof, and are never used as a runtime stopping condition.
-/

namespace Polytime1.WhileMachine

-- guardLevel and bodyLevel: the two finite controller carriers.
-- valueLevel: mathematical loop states represented by the tape.
universe guardLevel bodyLevel valueLevel

open TupleMachine (Symbol data)
variable {Guard : Type guardLevel} {Body : Type bodyLevel}
variable [Inhabited Guard] [Inhabited Body]

/-- One write transports control at each true-guard/body boundary. -/
def machine (guard : Turing.TM0.Machine Symbol Guard) (body : Turing.TM0.Machine Symbol Body)
    (guardEntry : Guard) (bodyEntry : Body) : Turing.TM0.Machine Symbol (Sum Guard Body)
  | .inl state, symbol => match guard state symbol with
    | some (next, action) => some (.inl next, action)
    | none => if symbol = data false then none else some (.inr bodyEntry, .write symbol)
  | .inr state, symbol => match body state symbol with
    | some (next, action) => some (.inr next, action)
    | none => some (.inl guardEntry, .write symbol)

/-- A mathematical invariant and a polynomially bounded iteration proof can
be combined with concrete guard/body tape traces. No execution obligation is
imposed on mathematical states outside the invariant. -/
theorem realizes {Value : Type valueLevel}
    (guard : Turing.TM0.Machine Symbol Guard) (body : Turing.TM0.Machine Symbol Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (entryTape resultTape : Value → Turing.Tape Symbol)
    (condition : Value → Bool) (advance : Value → Value) (invariant : Value → Prop)
    (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbol, guard guardExit symbol = none)
    (bodyHalt : ∀ symbol, body bodyExit symbol = none)
    (resultBit : ∀ value, invariant value → (resultTape value).head = data (condition value))
    (preserves : ∀ value, invariant value → condition value = true → invariant (advance value))
    (guardRuns : ∀ value, invariant value → ∃ ticks, ticks ≤ guardBound ∧
      Tape.Steps guard ticks ⟨guardEntry, entryTape value⟩ ⟨guardExit, resultTape value⟩)
    (bodyRuns : ∀ value, invariant value → condition value = true → ∃ ticks, ticks ≤ bodyBound ∧
      Tape.Steps body ticks ⟨bodyEntry, resultTape value⟩ ⟨bodyExit, entryTape (advance value)⟩)
    (initial : Value) (valid : invariant initial) (iterations : ℕ)
    (running : ∀ index < iterations, condition (advance^[index] initial) = true)
    (stops : condition (advance^[iterations] initial) = false) :
    ∃ ticks, ticks ≤ (iterations + 1) * (guardBound + bodyBound + 2) ∧
      Tape.Steps (machine guard body guardEntry bodyEntry) ticks
        ⟨.inl guardEntry, entryTape initial⟩
        ⟨.inl guardExit, resultTape (advance^[iterations] initial)⟩ ∧
      Turing.TM0.step (machine guard body guardEntry bodyEntry)
        ⟨.inl guardExit, resultTape (advance^[iterations] initial)⟩ = none := by
  induction iterations generalizing initial with
  | zero =>
    obtain ⟨ticks, bounded, trace⟩ := guardRuns initial valid
    have lifted := trace.rename Sum.inl (targetMachine := machine guard body guardEntry bodyEntry)
      (by intro state symbol next action transition; simp [machine, transition])
    refine ⟨ticks, by omega, lifted, ?_⟩
    simp only [Function.iterate_zero, id_eq] at stops ⊢
    simp [Turing.TM0.step, machine, guardHalt, resultBit initial valid, stops]
  | succ iterations hypothesis =>
    have firstTrue : condition initial = true := by simpa using running 0 (by omega)
    have nextValid := preserves initial valid firstTrue
    have nextRunning : ∀ index < iterations, condition (advance^[index] (advance initial)) = true := by
      intro index earlier
      simpa only [Function.iterate_succ_apply] using running (index + 1) (by omega)
    have nextStops : condition (advance^[iterations] (advance initial)) = false := by
      simpa only [Function.iterate_succ_apply] using stops
    obtain ⟨guardTicks, guardCost, guardTrace⟩ := guardRuns initial valid
    obtain ⟨bodyTicks, bodyCost, bodyTrace⟩ := bodyRuns initial valid firstTrue
    have liftedGuard := guardTrace.rename Sum.inl
      (targetMachine := machine guard body guardEntry bodyEntry)
      (by intro state symbol next action transition; simp [machine, transition])
    have liftedBody := bodyTrace.rename Sum.inr
      (targetMachine := machine guard body guardEntry bodyEntry)
      (by intro state symbol next action transition; simp [machine, transition])
    have toBody : Turing.TM0.step (machine guard body guardEntry bodyEntry)
        ⟨.inl guardExit, resultTape initial⟩ = some ⟨.inr bodyEntry, resultTape initial⟩ := by
      have different : (resultTape initial).head ≠ data false := by
        rw [resultBit initial valid, firstTrue]
        decide
      simp [Turing.TM0.step, machine, guardHalt, different, Turing.Tape.write_self]
    have toGuard : Turing.TM0.step (machine guard body guardEntry bodyEntry)
        ⟨.inr bodyExit, entryTape (advance initial)⟩ = some ⟨.inl guardEntry, entryTape (advance initial)⟩ := by
      simp [Turing.TM0.step, machine, bodyHalt, Turing.Tape.write_self]
    obtain ⟨restTicks, restCost, restTrace, halt⟩ := hypothesis (advance initial) nextValid nextRunning nextStops
    have trace := liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace)))
    refine ⟨guardTicks + ((bodyTicks + (restTicks + 1)) + 1), ?_, ?_, ?_⟩
    · nlinarith
    · simpa only [Function.iterate_succ_apply] using trace
    · simpa only [Function.iterate_succ_apply] using halt

/-- Relational loop execution leaves scratch choices in the representation.
A decreasing mathematical measure proves termination; it is never runtime fuel. -/
theorem realizes_relation {Value : Type valueLevel}
    (guard : Turing.TM0.Machine Symbol Guard) (body : Turing.TM0.Machine Symbol Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (entryRepresentation resultRepresentation : Value → Turing.Tape Symbol → Prop)
    (condition : Value → Bool) (invariant : Value → Prop) (measure : Value → ℕ)
    (relation : Value → Value → Prop)
    (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbol, guard guardExit symbol = none)
    (bodyHalt : ∀ symbol, body bodyExit symbol = none)
    (resultBit : ∀ value tape, resultRepresentation value tape → tape.head = data (condition value))
    (guardRuns : ∀ value initial, invariant value → entryRepresentation value initial →
      ∃ ticks result, ticks ≤ guardBound ∧
        Tape.Steps guard ticks ⟨guardEntry, initial⟩ ⟨guardExit, result⟩ ∧ resultRepresentation value result)
    (bodyRuns : ∀ value initial, invariant value → condition value = true → resultRepresentation value initial →
      ∃ next final ticks, ticks ≤ bodyBound ∧
        Tape.Steps body ticks ⟨bodyEntry, initial⟩ ⟨bodyExit, final⟩ ∧
        relation value next ∧ invariant next ∧ measure next < measure value ∧ entryRepresentation next final)
    (initial : Value) (initialTape : Turing.Tape Symbol)
    (valid : invariant initial) (represented : entryRepresentation initial initialTape) :
    ∃ final finalTape ticks, ticks ≤ (measure initial + 1) * (guardBound + bodyBound + 2) ∧
      Relation.ReflTransGen relation initial final ∧ invariant final ∧ condition final = false ∧ resultRepresentation final finalTape ∧
      Tape.Steps (machine guard body guardEntry bodyEntry) ticks
        ⟨.inl guardEntry, initialTape⟩ ⟨.inl guardExit, finalTape⟩ ∧
      Turing.TM0.step (machine guard body guardEntry bodyEntry) ⟨.inl guardExit, finalTape⟩ = none := by
  generalize remaining : measure initial = amount
  induction amount using Nat.strong_induction_on generalizing initial initialTape with
  | h amount hypothesis =>
    obtain ⟨guardTicks, result, guardCost, guardTrace, resultRepresented⟩ :=
      guardRuns initial initialTape valid represented
    have liftedGuard := guardTrace.rename Sum.inl (targetMachine := machine guard body guardEntry bodyEntry)
      (by intro state symbol next action transition; simp [machine, transition])
    cases active : condition initial with
    | false =>
      refine ⟨initial, result, guardTicks, by nlinarith, .refl, valid, active, resultRepresented, liftedGuard, ?_⟩
      simp [Turing.TM0.step, machine, guardHalt, resultBit initial result resultRepresented, active]
    | true =>
      obtain ⟨next, nextTape, bodyTicks, bodyCost, bodyTrace, related, nextValid, decreased, nextRepresented⟩ :=
        bodyRuns initial result valid active resultRepresented
      obtain ⟨final, finalTape, restTicks, restCost, reached, finalValid, stopped, finalRepresented, restTrace, halt⟩ :=
        hypothesis (measure next) (by omega) next nextTape nextValid nextRepresented rfl
      have liftedBody := bodyTrace.rename Sum.inr (targetMachine := machine guard body guardEntry bodyEntry)
        (by intro state symbol next action transition; simp [machine, transition])
      have toBody : Turing.TM0.step (machine guard body guardEntry bodyEntry)
          ⟨.inl guardExit, result⟩ = some ⟨.inr bodyEntry, result⟩ := by
        have different : result.head ≠ data false := by
          rw [resultBit initial result resultRepresented, active]
          decide
        simp [Turing.TM0.step, machine, guardHalt, different, Turing.Tape.write_self]
      have toGuard : Turing.TM0.step (machine guard body guardEntry bodyEntry)
          ⟨.inr bodyExit, nextTape⟩ = some ⟨.inl guardEntry, nextTape⟩ := by
        simp [Turing.TM0.step, machine, bodyHalt, Turing.Tape.write_self]
      refine ⟨final, finalTape, guardTicks + ((bodyTicks + (restTicks + 1)) + 1), ?_,
        reached.head related, finalValid, stopped, finalRepresented,
        liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace))), halt⟩
      nlinarith

end Polytime1.WhileMachine
