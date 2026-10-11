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

import Polytime.Realization
import Polytime.WhileMachine

/-! # Guarded loops over mathematical representation relations

The guard and body have ordinary contracts. Users prove invariant preservation,
a decreasing mathematical measure, and a qualitative polynomial bound on that
measure. Controller handovers and guard/body polynomial bounds stay internal.
-/

namespace Polytime.Realization.Realizes

open TupleMachine (Symbol data)

-- environmentLevel: caller context; valueLevel: mathematical loop states.
universe environmentLevel valueLevel

variable {ctx : SizeContext}
variable {Environment : SizeAssignment ctx → Type environmentLevel}
variable {Value : SizeAssignment ctx → Type valueLevel}

noncomputable section GuardedLoops

/-- The guard stops when false; the measure is proof data, never loop fuel.
The resulting representation retains the false result bit for an explicit
consumer or output adapter. Scratch remains existential in representations. -/
theorem whileLoop
    (entryRepresentation guardedRepresentation :
      ∀ assignment, Environment assignment → Value assignment → Turing.Tape Symbol → Prop)
    (condition : ∀ assignment, Value assignment → Bool)
    (invariant : ∀ assignment, Value assignment → Prop)
    (step : ∀ assignment, Value assignment → Value assignment → Prop)
    (measure : ∀ assignment, Value assignment → ℕ)
    (guard : Realizes entryRepresentation guardedRepresentation invariant (fun _ initial final => final = initial))
    (body : Realizes guardedRepresentation entryRepresentation
      (fun assignment value => invariant assignment value ∧ condition assignment value = true) step)
    (resultBit : ∀ assignment environment value tape,
      guardedRepresentation assignment environment value tape → tape.head = data (condition assignment value))
    (preserves : ∀ assignment initial final,
      invariant assignment initial → condition assignment initial = true → step assignment initial final →
        invariant assignment final)
    (decreases : ∀ assignment initial final,
      invariant assignment initial → condition assignment initial = true → step assignment initial final →
        measure assignment final < measure assignment initial)
    (bounded : ∃ bound : SizePolynomial ctx, ∀ assignment value,
      invariant assignment value → measure assignment value ≤ bound.eval assignment) :
    Realizes entryRepresentation guardedRepresentation invariant
      (fun assignment initial final => Relation.ReflTransGen (step assignment) initial final ∧
        invariant assignment final ∧ condition assignment final = false) := by
  obtain ⟨Guard, guardFinite, guardInhabited, guardEntry, guardExit, guardMachine, guardBound, guardHalt, guardRuns⟩ := guard
  obtain ⟨Body, bodyFinite, bodyInhabited, bodyEntry, bodyExit, bodyMachine, bodyBound, bodyHalt, bodyRuns⟩ := body
  obtain ⟨iterationBound, iterations⟩ := bounded
  let guardControllerFinite : Fintype Guard := guardFinite
  let bodyControllerFinite : Fintype Body := bodyFinite
  let guardControllerInhabited : Inhabited Guard := guardInhabited
  let bodyControllerInhabited : Inhabited Body := bodyInhabited
  let loop := WhileMachine.machine guardMachine bodyMachine guardEntry bodyEntry
  let idle : Turing.TM0.Machine Symbol Unit := fun _ _ => none
  refine ⟨Sum (Sum Guard Body) Unit, inferInstance, inferInstance, .inl (.inl guardEntry), .inr (),
    Tape.sequence loop idle (), (iterationBound + 1) * (guardBound + bodyBound + SizePolynomial.constant 2) + 1, ?_, ?_⟩
  · intro symbol; rfl
  · intro assignment environment initial initialTape valid represented
    have guards : ∀ value tape, invariant assignment value → entryRepresentation assignment environment value tape →
        ∃ ticks result, ticks ≤ guardBound.eval assignment ∧
          Tape.Steps guardMachine ticks ⟨guardEntry, tape⟩ ⟨guardExit, result⟩ ∧
          guardedRepresentation assignment environment value result := by
      intro value tape good encoded
      obtain ⟨next, result, ticks, cost, trace, equal, resultEncoded⟩ :=
        guardRuns assignment environment value tape good encoded
      subst next
      exact ⟨ticks, result, cost, trace, resultEncoded⟩
    have bodies : ∀ value tape, invariant assignment value → condition assignment value = true →
        guardedRepresentation assignment environment value tape →
        ∃ next result ticks, ticks ≤ bodyBound.eval assignment ∧
          Tape.Steps bodyMachine ticks ⟨bodyEntry, tape⟩ ⟨bodyExit, result⟩ ∧
          step assignment value next ∧ invariant assignment next ∧ measure assignment next < measure assignment value ∧
          entryRepresentation assignment environment next result := by
      intro value tape good active encoded
      obtain ⟨next, result, ticks, cost, trace, correct, resultEncoded⟩ :=
        bodyRuns assignment environment value tape ⟨good, active⟩ encoded
      exact ⟨next, result, ticks, cost, trace, correct, preserves _ _ _ good active correct,
        decreases _ _ _ good active correct, resultEncoded⟩
    obtain ⟨final, finalTape, ticks, cost, reached, finalValid, stopped, finalEncoded, trace, halted⟩ :=
      WhileMachine.realizes_relation guardMachine bodyMachine guardEntry guardExit bodyEntry bodyExit
        (entryRepresentation assignment environment) (guardedRepresentation assignment environment)
        (condition assignment) (invariant assignment) (measure assignment) (step assignment)
        (guardBound.eval assignment) (bodyBound.eval assignment) guardHalt bodyHalt
        (resultBit assignment environment) guards bodies initial initialTape valid represented
    refine ⟨final, finalTape, ticks + 1, ?_,
      Tape.sequence_steps_of_halt () trace halted (.zero ⟨(), finalTape⟩), ⟨reached, finalValid, stopped⟩, finalEncoded⟩
    have capacity := Nat.mul_le_mul_right (guardBound.eval assignment + bodyBound.eval assignment + 2)
      (Nat.succ_le_succ (iterations assignment initial valid))
    simp only [Nat.succ_eq_add_one] at capacity
    simp only [SizePolynomial.eval_add, SizePolynomial.eval_mul, SizePolynomial.eval_one, SizePolynomial.eval_constant]
    omega

/-- Search with a bounded increasing index. The guard may stop early; no
iteration formula, chosen terminal index, or runtime polynomial is required. -/
theorem search
    (entryRepresentation guardedRepresentation :
      ∀ assignment, Environment assignment → Value assignment → Turing.Tape Symbol → Prop)
    (length : SizeExpression ctx)
    (index : ∀ assignment, Value assignment → ℕ)
    (condition : ∀ assignment, Value assignment → Bool)
    (invariant : ∀ assignment, Value assignment → Prop)
    (step : ∀ assignment, Value assignment → Value assignment → Prop)
    (guard : Realizes entryRepresentation guardedRepresentation invariant (fun _ initial final => final = initial))
    (body : Realizes guardedRepresentation entryRepresentation
      (fun assignment value => invariant assignment value ∧ condition assignment value = true) step)
    (resultBit : ∀ assignment environment value tape,
      guardedRepresentation assignment environment value tape → tape.head = data (condition assignment value))
    (continues : ∀ assignment value,
      invariant assignment value → condition assignment value = true → index assignment value < length.eval assignment)
    (preserves : ∀ assignment initial final,
      invariant assignment initial → condition assignment initial = true → step assignment initial final → invariant assignment final)
    (advances : ∀ assignment initial final,
      invariant assignment initial → condition assignment initial = true → step assignment initial final →
        index assignment final = index assignment initial + 1) :
    Realizes entryRepresentation guardedRepresentation invariant
      (fun assignment initial final => Relation.ReflTransGen (step assignment) initial final ∧
        invariant assignment final ∧ condition assignment final = false) := by
  apply whileLoop entryRepresentation guardedRepresentation condition invariant step
    (fun assignment value => length.eval assignment - index assignment value) guard body resultBit preserves
  · intro assignment initial final valid active relation
    have before := continues assignment initial valid active
    have progress := advances assignment initial final valid active relation
    omega
  · refine ⟨length.polynomial, ?_⟩
    intro assignment value _
    rw [← length.eval_eq]
    exact Nat.sub_le _ _

/-- Traverse up to a declared capacity. Users prove the mathematical step;
index progress and polynomial iteration bounds follow from this rule. -/
theorem traversal
    (entryRepresentation guardedRepresentation :
      ∀ assignment, Environment assignment → Value assignment → Turing.Tape Symbol → Prop)
    (length : SizeExpression ctx)
    (index : ∀ assignment, Value assignment → ℕ)
    (invariant : ∀ assignment, Value assignment → Prop)
    (step : ∀ assignment, Value assignment → Value assignment → Prop)
    (guard : Realizes entryRepresentation guardedRepresentation invariant (fun _ initial final => final = initial))
    (body : Realizes guardedRepresentation entryRepresentation
      (fun assignment value => invariant assignment value ∧ decide (index assignment value < length.eval assignment) = true) step)
    (resultBit : ∀ assignment environment value tape,
      guardedRepresentation assignment environment value tape →
        tape.head = data (decide (index assignment value < length.eval assignment)))
    (indexBound : ∀ assignment value, invariant assignment value → index assignment value ≤ length.eval assignment)
    (preserves : ∀ assignment initial final,
      invariant assignment initial → index assignment initial < length.eval assignment →
        step assignment initial final → invariant assignment final)
    (advances : ∀ assignment initial final,
      invariant assignment initial → index assignment initial < length.eval assignment →
        step assignment initial final → index assignment final = index assignment initial + 1) :
    Realizes entryRepresentation guardedRepresentation invariant
      (fun assignment initial final => Relation.ReflTransGen (step assignment) initial final ∧
        invariant assignment final ∧ index assignment final = length.eval assignment) := by
  have loop := search entryRepresentation guardedRepresentation length index
    (fun assignment value => decide (index assignment value < length.eval assignment))
    invariant step guard body resultBit
    (by intro assignment value _ active; exact of_decide_eq_true active)
    (by
      intro assignment initial final valid active relation
      exact preserves assignment initial final valid (of_decide_eq_true active) relation)
    (by
      intro assignment initial final valid active relation
      exact advances assignment initial final valid (of_decide_eq_true active) relation)
  exact loop.consequence (by intros; assumption) (by
    intro assignment initial final _ finished
    obtain ⟨reached, valid, stopped⟩ := finished
    have upper := indexBound assignment final valid
    have lower := of_decide_eq_false stopped
    exact ⟨reached, valid, by omega⟩)

/-- A bounded deterministic traversal is a mathematical fold. The iteration
count follows from index progress, including a nonzero initial index. -/
theorem fold
    (entryRepresentation guardedRepresentation :
      ∀ assignment, Environment assignment → Value assignment → Turing.Tape Symbol → Prop)
    (length : SizeExpression ctx)
    (index : ∀ assignment, Value assignment → ℕ)
    (invariant : ∀ assignment, Value assignment → Prop)
    (advance : ∀ assignment, Value assignment → Value assignment)
    (guard : Realizes entryRepresentation guardedRepresentation invariant (fun _ initial final => final = initial))
    (body : Realizes guardedRepresentation entryRepresentation
      (fun assignment value => invariant assignment value ∧ decide (index assignment value < length.eval assignment) = true)
      (fun assignment initial final => final = advance assignment initial))
    (resultBit : ∀ assignment environment value tape,
      guardedRepresentation assignment environment value tape →
        tape.head = data (decide (index assignment value < length.eval assignment)))
    (indexBound : ∀ assignment value, invariant assignment value → index assignment value ≤ length.eval assignment)
    (preserves : ∀ assignment value, invariant assignment value → index assignment value < length.eval assignment →
      invariant assignment (advance assignment value))
    (advances : ∀ assignment value, invariant assignment value → index assignment value < length.eval assignment →
      index assignment (advance assignment value) = index assignment value + 1) :
    Realizes entryRepresentation guardedRepresentation invariant
      (fun assignment initial final =>
        final = (advance assignment)^[length.eval assignment - index assignment initial] initial ∧
        invariant assignment final ∧ index assignment final = length.eval assignment) := by
  let step assignment initial final := final = advance assignment initial ∧
    invariant assignment initial ∧ index assignment initial < length.eval assignment
  have strengthened : Realizes guardedRepresentation entryRepresentation
      (fun assignment value => invariant assignment value ∧ decide (index assignment value < length.eval assignment) = true) step :=
    body.consequence (by intros; assumption) (by
      intro assignment initial final valid equal
      exact ⟨equal, valid.1, of_decide_eq_true valid.2⟩)
  have loop := traversal entryRepresentation guardedRepresentation length index invariant step guard strengthened
    resultBit indexBound
    (by
      intro assignment initial final valid active relation
      rw [relation.1]
      exact preserves assignment initial valid active)
    (by
      intro assignment initial final valid active relation
      rw [relation.1]
      exact advances assignment initial valid active)
  apply loop.consequence (by intros; assumption)
  intro assignment initial final _ finished
  obtain ⟨reached, valid, stopped⟩ := finished
  have counted : ∀ before after, Relation.ReflTransGen (step assignment) before after →
      ∃ count, after = (advance assignment)^[count] before ∧ index assignment after = index assignment before + count := by
    intro before after reached
    induction reached with
    | refl => exact ⟨0, rfl, by simp⟩
    | @tail middle after _ relation hypothesis =>
      obtain ⟨count, equal, position⟩ := hypothesis
      refine ⟨count + 1, ?_, ?_⟩
      · rw [relation.1, equal, Function.iterate_succ_apply']
      · have progress := advances assignment middle relation.2.1 relation.2.2
        rw [relation.1, progress, position]
        omega
  obtain ⟨count, equal, position⟩ := counted initial final reached
  have countEqual : count = length.eval assignment - index assignment initial := by omega
  exact ⟨by simpa only [countEqual] using equal, valid, stopped⟩

end GuardedLoops
end Polytime.Realization.Realizes
