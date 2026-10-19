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

import Polytime2.Machine.CallingConventionWhile
import Polytime2.Arithmetic.CounterOperations

/-! # Mathematical while loops behind existential certificates -/

namespace Polytime2.Computation.Realizable

open MultiTape CallingConvention

variable {Parameter : Type} [Fintype Parameter]

/-- Realize a mathematical answer by a guard-driven loop. The answer is
conserved by each step and equals the state when the guard is false. Callers
supply only mathematical proofs and an existential polynomial measure bound. -/
theorem whileLoop
    (domain : EncodedDomain Parameter)
    (invariant : ∀ sizes, domain.Carrier sizes → Prop)
    (condition : ∀ sizes, domain.Carrier sizes → Bool)
    (advance : ∀ sizes, {value : domain.Carrier sizes //
      invariant sizes value ∧ condition sizes value = true} → domain.Carrier sizes)
    (answer : ∀ sizes, {value : domain.Carrier sizes // invariant sizes value} → domain.Carrier sizes)
    (measure : ∀ sizes, domain.Carrier sizes → ℕ)
    (guardRealizable : (Computation.unaryMap domain EncodedDomain.booleans invariant
      (fun sizes value => condition sizes value.val)).Realizable)
    (bodyRealizable : (Computation.unaryMap domain domain
      (fun sizes value => invariant sizes value ∧ condition sizes value = true) advance).Realizable)
    (preserves : ∀ sizes value, invariant sizes (advance sizes value))
    (decreases : ∀ sizes value, measure sizes (advance sizes value) < measure sizes value.val)
    (conserves : ∀ sizes value,
      answer sizes ⟨advance sizes value, preserves sizes value⟩ =
        answer sizes ⟨value.val, value.property.1⟩)
    (terminal : ∀ sizes value, condition sizes value.val = false → answer sizes value = value.val)
    (bounded : ∃ bound : MvPolynomial Parameter ℕ,
      ∀ sizes value, invariant sizes value → measure sizes value ≤ MvPolynomial.eval sizes bound) :
    (Computation.unaryMap domain domain invariant answer).Realizable := by
  classical
  let computation := Computation.unaryMap domain domain invariant answer
  let guard := Computation.unaryMap domain EncodedDomain.booleans invariant
    (fun sizes value => condition sizes value.val)
  let body := Computation.unaryMap domain domain
    (fun sizes value => invariant sizes value ∧ condition sizes value = true) advance
  let copying := Computation.copy domain
  obtain ⟨GuardScratch, finiteGuardScratch, guardScratch, GuardState, finiteGuardState,
    guardMachine, guardEntry, guardExit, guardCertificate⟩ := guardRealizable
  obtain ⟨BodyScratch, finiteBodyScratch, bodyScratch, BodyState, finiteBodyState,
    bodyMachine, bodyEntry, bodyExit, bodyCertificate⟩ := bodyRealizable
  obtain ⟨CopyScratch, finiteCopyScratch, copyScratch, CopyState, finiteCopyState,
    copyMachine, copyEntry, copyExit, copyCertificate⟩ := Computation.copy_realizable domain
  let guardScratchFiniteInstance : Fintype GuardScratch := finiteGuardScratch
  let bodyScratchFiniteInstance : Fintype BodyScratch := finiteBodyScratch
  let copyScratchFiniteInstance : Fintype CopyScratch := finiteCopyScratch
  let guardStateFiniteInstance : Fintype GuardState := finiteGuardState
  let bodyStateFiniteInstance : Fintype BodyState := finiteBodyState
  let copyStateFiniteInstance : Fintype CopyState := finiteCopyState
  let Scratch := GuardScratch ⊕ (BodyScratch ⊕ (CopyScratch ⊕ (Unit ⊕ Unit)))
  let scratchDomains : Scratch → EncodedDomain Parameter :=
    Sum.elim guardScratch (Sum.elim bodyScratch (Sum.elim copyScratch
      (Sum.elim (fun _ => EncodedDomain.booleans) (fun _ => domain))))
  let flagTape : Internal.TapeName computation Scratch := Internal.scratchTape computation
    (.inr (.inr (.inr (.inl ()))))
  let nextTape : Internal.TapeName computation Scratch := Internal.scratchTape computation
    (.inr (.inr (.inr (.inr ()))))
  let guardWiring : Internal.TapeName guard GuardScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => Internal.outputTape computation
      | .inr (.inr (.inl _)) => flagTape
      | .inr (.inr (.inr scratch)) => Internal.scratchTape computation (.inl scratch)), by
      intro first second equal
      dsimp only [Scratch, flagTape, Internal.outputTape, Internal.scratchTape] at equal
      rcases first with parameter | argument | result | scratch <;>
        rcases second with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let bodyWiring : Internal.TapeName body BodyScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => Internal.outputTape computation
      | .inr (.inr (.inl _)) => nextTape
      | .inr (.inr (.inr scratch)) => Internal.scratchTape computation (.inr (.inl scratch))), by
      intro first second equal
      dsimp only [Scratch, nextTape, Internal.outputTape, Internal.scratchTape] at equal
      rcases first with parameter | argument | result | scratch <;>
        rcases second with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let copyWiring : Internal.TapeName copying CopyScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => Internal.inputTape computation ()
      | .inr (.inr (.inl _)) => Internal.outputTape computation
      | .inr (.inr (.inr scratch)) => Internal.scratchTape computation (.inr (.inr (.inl scratch)))), by
      intro first second equal
      dsimp only [Scratch, Internal.inputTape, Internal.outputTape, Internal.scratchTape] at equal
      rcases first with parameter | argument | result | scratch <;>
        rcases second with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let commitWiring : Internal.TapeName copying CopyScratch ↪ Internal.TapeName computation Scratch :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => nextTape
      | .inr (.inr (.inl _)) => Internal.outputTape computation
      | .inr (.inr (.inr scratch)) => Internal.scratchTape computation (.inr (.inr (.inl scratch)))), by
      intro first second equal
      dsimp only [Scratch, nextTape, Internal.outputTape, Internal.scratchTape] at equal
      rcases first with parameter | argument | result | scratch <;>
        rcases second with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]⟩
  let wiredGuard := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch)) guardWiring guardMachine
  let wiredBody := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch)) bodyWiring bodyMachine
  let wiredCopy := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch)) copyWiring copyMachine
  let wiredCommit := MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Scratch)) commitWiring copyMachine
  let completeBody := MultiTape.sequence wiredBody wiredCommit copyEntry
  let result : Symbols (Alphabet (Internal.TapeName computation Scratch)) → Bool :=
    fun symbols => decide (symbols flagTape = Binary.data true)
  let loop := MultiTape.whileMachine wiredGuard completeBody guardEntry (.inl bodyEntry) result
  let wrappedLoop := MultiTape.withExit loop
  refine ⟨Scratch, inferInstance, scratchDomains, _, inferInstance,
    MultiTape.sequence wiredCopy wrappedLoop (.inl (.inl guardEntry)),
    .inl copyEntry, .inr (.inr ()), ?_⟩
  obtain ⟨guardBound, guardRuns⟩ := Internal.wiredRuns guardScratch guardMachine guardEntry guardExit guardCertificate guardWiring
  obtain ⟨bodyBound, bodyRuns⟩ := Internal.wiredRuns bodyScratch bodyMachine bodyEntry bodyExit bodyCertificate bodyWiring
  obtain ⟨copyBound, copyRuns⟩ := Internal.wiredRuns copyScratch copyMachine copyEntry copyExit copyCertificate copyWiring
  obtain ⟨commitBound, commitRuns⟩ := Internal.wiredRuns copyScratch copyMachine copyEntry copyExit copyCertificate commitWiring
  obtain ⟨measureBound, measureFits⟩ := bounded
  have guardHalt : ∀ symbols, wiredGuard guardExit symbols = none := by
    intro symbols; simp [wiredGuard, MultiTape.wire, guardCertificate.2.2.1]
  have bodyHalt : ∀ symbols, wiredBody bodyExit symbols = none := by
    intro symbols; simp [wiredBody, MultiTape.wire, bodyCertificate.2.2.1]
  have copyHalt : ∀ symbols, wiredCopy copyExit symbols = none := by
    intro symbols; simp [wiredCopy, MultiTape.wire, copyCertificate.2.2.1]
  have commitHalt : ∀ symbols, wiredCommit copyExit symbols = none := by
    intro symbols; simp [wiredCommit, MultiTape.wire, copyCertificate.2.2.1]
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; rfl),
    copyBound + (measureBound + 1) * (guardBound + bodyBound + commitBound + 3) + 2, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let initialValue : {value : domain.Carrier sizes // invariant sizes value} := ⟨arguments (), valid⟩
  let width := fun name => (Internal.domains computation scratchDomains name).width sizes
  let readonly : Internal.TapeName computation Scratch → Bool := Internal.readOnly computation
  have guardWidths : ∀ name, width (guardWiring name) = (Internal.domains guard guardScratch name).width sizes := by
    intro name; rcases name with parameter | argument | resultName | scratch <;> rfl
  have bodyWidths : ∀ name, width (bodyWiring name) = (Internal.domains body bodyScratch name).width sizes := by
    intro name; rcases name with parameter | argument | resultName | scratch <;> rfl
  have copyWidths : ∀ name, width (copyWiring name) = (Internal.domains copying copyScratch name).width sizes := by
    intro name; rcases name with parameter | argument | resultName | scratch <;> rfl
  have commitWidths : ∀ name, width (commitWiring name) = (Internal.domains copying copyScratch name).width sizes := by
    intro name; rcases name with parameter | argument | resultName | scratch <;> rfl
  let representation (value : {value : domain.Carrier sizes // invariant sizes value})
      (tapes : Tapes (Alphabet (Internal.TapeName computation Scratch))) : Prop :=
    (∀ name, Region (width name) 0 (tapes name)) ∧
    (∀ parameter, tapes (.inl parameter) = unary (sizes parameter)) ∧
    tapes (Internal.outputTape computation) = encoded domain sizes value.val ∧
    answer sizes value = answer sizes initialValue
  let guardedRepresentation (value : {value : domain.Carrier sizes // invariant sizes value})
      (tapes : Tapes (Alphabet (Internal.TapeName computation Scratch))) : Prop :=
    representation value tapes ∧ tapes flagTape = encoded EncodedDomain.booleans sizes (condition sizes value.val)
  obtain ⟨copyTicks, prepared, copyCost, copyTrace, copied, copyOutside, copyImmutable⟩ :=
    copyRuns sizes (fun _ => initialValue.val) True.intro width readonly initial copyWidths
      (by intro name premise; rcases name with parameter | argument | resultName | scratch <;>
        first | rfl | contradiction) headers
      (by intro name; cases name; exact represented.1 (Internal.inputTape computation ()) rfl)
      (fun name => represented.region (copyWiring name))
  have preparedValid : representation initialValue prepared :=
    ⟨(fun name => copyTrace.region name (represented.region name)),
      (fun parameter => (copyTrace.readOnly_tape (.inl parameter) rfl).trans (headers parameter)), copied, rfl⟩
  have guardedRuns : ∀ value tapes, representation value tapes → ∃ ticks final,
      ticks ≤ MvPolynomial.eval sizes guardBound ∧
      Runs width readonly wiredGuard ticks guardEntry (fun _ => 0) tapes guardExit (fun _ => 0) final ∧
      guardedRepresentation value final := by
    intro value tapes good
    obtain ⟨ticks, final, cost, trace, correct, outside, immutable⟩ :=
      guardRuns sizes (fun _ => value.val) value.property width readonly tapes guardWidths
        (by intro name premise; rcases name with parameter | argument | resultName | scratch <;>
          first | rfl | contradiction) good.2.1
        (by intro name; cases name; exact good.2.2.1) (fun name => good.1 (guardWiring name))
    refine ⟨ticks, final, cost, trace, ?_⟩
    exact ⟨⟨(fun name => trace.region name (good.1 name)),
      (fun parameter => (trace.readOnly_tape (.inl parameter) rfl).trans (good.2.1 parameter)),
      (immutable (Internal.inputTape guard ()) rfl).trans good.2.2.1, good.2.2.2⟩, correct⟩
  have advancedRuns : ∀ value tapes, guardedRepresentation value tapes → condition sizes value.val = true →
      ∃ nextValue ticks final, ticks ≤ MvPolynomial.eval sizes (bodyBound + commitBound + 1) ∧
        Runs width readonly completeBody ticks (.inl bodyEntry) (fun _ => 0) tapes (.inr copyExit) (fun _ => 0) final ∧
        representation nextValue final ∧ measure sizes nextValue.val < measure sizes value.val := by
    intro value tapes good running
    let next := advance sizes ⟨value.val, value.property, running⟩
    let nextValue : {value : domain.Carrier sizes // invariant sizes value} :=
      ⟨next, preserves sizes ⟨value.val, value.property, running⟩⟩
    obtain ⟨bodyTicks, intermediate, bodyCost, bodyTrace, updated, bodyOutside, bodyImmutable⟩ :=
      bodyRuns sizes (fun _ => value.val) ⟨value.property, running⟩ width readonly tapes bodyWidths
        (by intro name premise; rcases name with parameter | argument | resultName | scratch <;>
          first | rfl | contradiction) good.1.2.1
        (by intro name; cases name; exact good.1.2.2.1) (fun name => good.1.1 (bodyWiring name))
    obtain ⟨commitTicks, final, commitCost, commitTrace, committed, commitOutside, commitImmutable⟩ :=
      commitRuns sizes (fun _ => next) True.intro width readonly intermediate commitWidths
        (by intro name premise; rcases name with parameter | argument | resultName | scratch <;>
          first | rfl | contradiction)
        (fun parameter => (bodyTrace.readOnly_tape (.inl parameter) rfl).trans (good.1.2.1 parameter))
        (by intro name; cases name; exact updated)
        (fun name => bodyTrace.region (commitWiring name) (good.1.1 (commitWiring name)))
    have trace := bodyTrace.sequence wiredCommit copyEntry bodyHalt commitTrace
    refine ⟨nextValue, bodyTicks + commitTicks + 1, final, ?_, trace, ?_, decreases sizes _⟩
    · simp only [map_add, map_one]; omega
    · exact ⟨(fun name => trace.region name (good.1.1 name)),
        (fun parameter => (trace.readOnly_tape (.inl parameter) rfl).trans (good.1.2.1 parameter)),
        committed, (conserves sizes ⟨value.val, value.property, running⟩).trans good.1.2.2.2⟩
  have resultCorrect : ∀ value tapes, guardedRepresentation value tapes → result (read tapes) = condition sizes value.val := by
    intro value tapes good
    change decide ((tapes flagTape).head = Binary.data true) = _
    rw [good.2, encoded_booleans]
    cases condition sizes value.val <;> rfl
  obtain ⟨loopTicks, final, terminalValue, loopCost, loopTrace, finalValid, stopped⟩ :=
    Runs.whileValues width readonly wiredGuard completeBody guardEntry guardExit
      (.inl bodyEntry) (.inr copyExit) result representation guardedRepresentation
      (fun value => condition sizes value.val) (fun value => measure sizes value.val)
      (MvPolynomial.eval sizes guardBound) (MvPolynomial.eval sizes (bodyBound + commitBound + 1))
      guardHalt (by intro symbols; simp [completeBody, MultiTape.sequence, commitHalt])
      guardedRuns advancedRuns resultCorrect initialValue prepared preparedValid
  have wrappedTrace := loopTrace.withExit_at (by
    have finished := (resultCorrect terminalValue final finalValid).trans stopped
    simp [MultiTape.whileMachine, guardHalt, finished])
  have complete := copyTrace.sequence wrappedLoop (.inl (.inl guardEntry)) copyHalt wrappedTrace
  have resultEqual : terminalValue.val = answer sizes initialValue :=
    (terminal sizes terminalValue stopped).symm.trans finalValid.1.2.2.2
  refine ⟨copyTicks + (loopTicks + 1) + 1,
    (fun _ => answer sizes initialValue), final, ?_, complete, ⟨valid, rfl⟩, ?_⟩
  · have dominated := Nat.mul_le_mul_right
      (MvPolynomial.eval sizes guardBound + MvPolynomial.eval sizes (bodyBound + commitBound + 1) + 2)
      (Nat.add_le_add_right (measureFits sizes initialValue.val initialValue.property) 1)
    simp only [map_add, map_mul, map_one, map_ofNat, Nat.add_assoc, Nat.reduceAdd] at dominated loopCost ⊢
    omega
  · intro name; cases name
    exact finalValid.1.2.2.1.trans (congrArg (encoded domain sizes) resultEqual)

end Polytime2.Computation.Realizable
