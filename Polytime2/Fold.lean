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

import Polytime2.Contracts
import Polytime2.While

/-! # Certified mathematical folds

A traversal advances a bounded logical index once per iteration. The logical
state excludes physical scratch. Guard costs, controller handovers, and the
polynomial runtime witness are handled by the library.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape roles; symbolLevel: alphabets; valueLevel: logical states.
-- guardLevel and bodyLevel: the finite component controller carriers.
universe tapeLevel symbolLevel valueLevel guardLevel bodyLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {Value : Type valueLevel} {Guard : Type guardLevel} {Body : Type bodyLevel}

/-- A guarded traversal realizes the corresponding mathematical iterate.
The two representation relations may existentially quantify unrelated scratch. -/
theorem fold_steps (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry guardExit : Guard) (bodyEntry bodyExit : Body)
    (result : Symbols Alphabet → Bool)
    (representation guardedRepresentation : Value → Tapes Alphabet → Prop)
    (length : ℕ) (index : Value → ℕ) (invariant : Value → Prop) (advance : Value → Value)
    (guardBound bodyBound : ℕ)
    (guardHalt : ∀ symbols, guard guardExit symbols = none)
    (bodyHalt : ∀ symbols, body bodyExit symbols = none)
    (guardRuns : ∀ value initial, invariant value → representation value initial →
      ∃ ticks final, ticks ≤ guardBound ∧
        Steps guard ticks (guardEntry, initial) (guardExit, final) ∧ guardedRepresentation value final)
    (bodyRuns : ∀ value initial, invariant value → index value < length →
      guardedRepresentation value initial → ∃ ticks final, ticks ≤ bodyBound ∧
        Steps body ticks (bodyEntry, initial) (bodyExit, final) ∧ representation (advance value) final)
    (resultCorrect : ∀ value tapes, guardedRepresentation value tapes →
      result (read tapes) = decide (index value < length))
    (indexBound : ∀ value, invariant value → index value ≤ length)
    (preserves : ∀ value, invariant value → index value < length → invariant (advance value))
    (advances : ∀ value, invariant value → index value < length → index (advance value) = index value + 1)
    (value : Value) (initial : Tapes Alphabet) (valid : invariant value) (represented : representation value initial) :
    ∃ ticks final, ticks ≤ (length - index value + 1) * (guardBound + bodyBound + 2) ∧
      Steps (whileMachine guard body guardEntry bodyEntry result) ticks
        (.inl guardEntry, initial) (.inl guardExit, final) ∧
      guardedRepresentation (advance^[length - index value] value) final ∧
      invariant (advance^[length - index value] value) ∧
      index (advance^[length - index value] value) = length := by
  generalize ranking : length - index value = remaining
  induction remaining using Nat.strong_induction_on generalizing value initial with
  | h remaining hypothesis =>
    obtain ⟨guardTicks, guarded, guardCost, guardTrace, guardEncoded⟩ :=
      guardRuns value initial valid represented
    have liftedGuard := guardTrace.rename Sum.inl
      (target := whileMachine guard body guardEntry bodyEntry result)
      (by intro state symbols next actions transition; simp [whileMachine, transition])
    have tested := resultCorrect value guarded guardEncoded
    by_cases active : index value < length
    · obtain ⟨bodyTicks, advanced, bodyCost, bodyTrace, bodyEncoded⟩ :=
        bodyRuns value guarded valid active guardEncoded
      have progress := advances value valid active
      have smaller : length - index (advance value) < remaining := by omega
      obtain ⟨restTicks, final, restCost, restTrace, finalEncoded, finalValid, finalIndex⟩ :=
        hypothesis (length - index (advance value)) smaller (advance value) advanced
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
      have count : remaining = (length - index (advance value)) + 1 := by omega
      have iterated : advance^[remaining] value =
          advance^[length - index (advance value)] (advance value) := by
        rw [count, Function.iterate_succ_apply]
      refine ⟨guardTicks + (bodyTicks + (restTicks + 1) + 1), final, ?_,
        liftedGuard.trans (.next toBody (liftedBody.trans (.next toGuard restTrace))),
        by simpa only [iterated] using finalEncoded,
        by simpa only [iterated] using finalValid,
        by simpa only [iterated] using finalIndex⟩
      rw [count]
      nlinarith
    · have stopped : index value = length := by have bounded := indexBound value valid; omega
      have empty : length - index value = 0 := by omega
      simp only [← ranking, empty, Function.iterate_zero, id_eq, zero_add, one_mul]
      refine ⟨guardTicks, guarded, ?_, liftedGuard, guardEncoded, valid, stopped⟩
      simpa using guardCost.trans (by omega : guardBound ≤ guardBound + bodyBound + 2)

namespace Computes

-- parameterLevel: runtime size names; familyLevel: mathematical state families.
universe parameterLevel familyLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
variable [∀ name, Fintype (Alphabet name)] [Fintype Guard] [Fintype Body]
variable {Family : (Parameter → ℕ) → Type familyLevel}

/-- Polynomially bounded traversal, with no user-visible total runtime polynomial. -/
theorem fold
    {guard : Machine Alphabet Guard} {body : Machine Alphabet Body}
    {guardEntry guardExit : Guard} {bodyEntry bodyExit : Body}
    (result : Symbols Alphabet → Bool)
    (representation guardedRepresentation : ∀ assignment, Family assignment → Tapes Alphabet → Prop)
    (length : (Parameter → ℕ) → ℕ) (index : ∀ assignment, Family assignment → ℕ)
    (invariant : ∀ assignment, Family assignment → Prop)
    (advance : ∀ assignment, Family assignment → Family assignment)
    (guardCertificate : Computes guard guardEntry guardExit representation guardedRepresentation invariant
      (fun _ value => value))
    (bodyCertificate : Computes body bodyEntry bodyExit guardedRepresentation representation
      (fun assignment value => invariant assignment value ∧ index assignment value < length assignment) advance)
    (resultCorrect : ∀ assignment value tapes, guardedRepresentation assignment value tapes →
      result (read tapes) = decide (index assignment value < length assignment))
    (indexBound : ∀ assignment value, invariant assignment value → index assignment value ≤ length assignment)
    (preserves : ∀ assignment value, invariant assignment value → index assignment value < length assignment →
      invariant assignment (advance assignment value))
    (advances : ∀ assignment value, invariant assignment value → index assignment value < length assignment →
      index assignment (advance assignment value) = index assignment value + 1)
    (bounded : ∃ capacity : MvPolynomial Parameter ℕ,
      ∀ assignment, length assignment ≤ MvPolynomial.eval assignment capacity) :
    Computes (withExit (whileMachine guard body guardEntry bodyEntry result))
      (.inl (.inl guardEntry)) (.inr ()) representation
      (fun assignment value tapes => guardedRepresentation assignment value tapes ∧
        invariant assignment value ∧ index assignment value = length assignment)
      invariant (fun assignment value => (advance assignment)^[length assignment - index assignment value] value) := by
  obtain ⟨guardHalt, guardBound, guardRuns⟩ := guardCertificate
  obtain ⟨bodyHalt, bodyBound, bodyRuns⟩ := bodyCertificate
  obtain ⟨capacity, capacityBound⟩ := bounded
  refine ⟨by intro symbols; rfl, (capacity + 1) * (guardBound + bodyBound + 2) + 1, ?_⟩
  intro assignment value initial valid represented
  obtain ⟨ticks, final, cost, trace, encoded, finalValid, finalIndex⟩ :=
    fold_steps guard body guardEntry guardExit bodyEntry bodyExit result
      (representation assignment) (guardedRepresentation assignment) (length assignment)
      (index assignment) (invariant assignment) (advance assignment)
      (MvPolynomial.eval assignment guardBound) (MvPolynomial.eval assignment bodyBound)
      guardHalt bodyHalt (guardRuns assignment)
      (by intro value tapes good active encoding; exact bodyRuns assignment value tapes ⟨good, active⟩ encoding)
      (resultCorrect assignment) (indexBound assignment) (preserves assignment) (advances assignment)
      value initial valid represented
  have stopped : result (read final) = false := by rw [resultCorrect _ _ _ encoded, finalIndex]; simp
  have halt : step (whileMachine guard body guardEntry bodyEntry result) (.inl guardExit, final) = none := by
    simp [step, whileMachine, guardHalt, stopped]
  refine ⟨ticks + 1, final, ?_, withExit_steps _ trace halt, encoded, finalValid, finalIndex⟩
  have capacityCost := Nat.mul_le_mul_right
    (MvPolynomial.eval assignment guardBound + MvPolynomial.eval assignment bodyBound + 2)
    (show length assignment - index assignment value + 1 ≤ MvPolynomial.eval assignment capacity + 1 by
      have boundedLength := capacityBound assignment; omega)
  simp only [map_add, map_mul, map_one, map_ofNat]
  omega

end Computes
end Polytime2.MultiTape
