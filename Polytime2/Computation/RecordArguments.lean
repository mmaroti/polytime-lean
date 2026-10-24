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

import Polytime2.Computation.Dependent
import Polytime2.Machine.Pipeline

/-! # Packing any finite argument family into one mathematical record

A fixed pipeline projects each argument using the ordinary certified record
operations, then invokes the consumer. No argument arity or writable contents
are supplied by the caller as hidden preparation assumptions.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- A single record tape supplies the original mathematical argument family. -/
noncomputable def withRecordArgument (computation : Computation Parameter InputName) : Computation Parameter Unit where
  inputDomains _ := EncodedDomain.namedRecord computation.inputDomains
  outputDomain := computation.outputDomain
  precondition sizes arguments := computation.precondition sizes (arguments ())
  compute sizes arguments := computation.compute sizes ⟨arguments.val (), arguments.property⟩

/-- Supply every callee argument by a certified computation on one shared
context. The common precondition guarantees that the callee may be invoked. -/
def onResults {ContextName : Type} [Fintype ContextName]
    (computation : Computation Parameter InputName)
    (context : ContextName → EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → Prop)
    (results : ∀ name sizes, {arguments // allowed sizes arguments} →
      (computation.inputDomains name).Carrier sizes)
    (valid : ∀ sizes arguments, computation.precondition sizes
      (fun name => results name sizes arguments)) : Computation Parameter ContextName where
  inputDomains := context
  outputDomain := computation.outputDomain
  precondition := allowed
  compute sizes arguments := computation.compute sizes
    ⟨(fun name => results name sizes arguments), valid sizes arguments⟩

namespace Realizable

open MultiTape CallingConvention Internal

/-- Select one immutable argument under any mathematical precondition. -/
theorem argument (inputs : InputName → EncodedDomain Parameter) (name : InputName)
    (allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop) :
    (Computation.mk inputs (inputs name) allowed (fun _ arguments => arguments.val name)).Realizable := by
  have selected := (copy_realizable (inputs name)).withArguments inputs
    ⟨(fun _ : Unit => name), by intro first second equal; cases first; cases second; rfl⟩
    (by intro singleton; cases singleton; rfl)
  exact selected.withSpecification allowed (fun _ arguments => arguments.val name)
    (by intros; trivial) (by intros; rfl)

/-- The generic record adapter includes all argument extraction and preserves
its public input, including for an empty argument family. -/
theorem withRecordArgument {computation : Computation Parameter InputName}
    (realizable : computation.Realizable) : computation.withRecordArgument.Realizable := by
  classical
  obtain ⟨SourceScratch, sourceScratchFinite, sourceScratchDomains, SourceState, sourceStateFinite,
    source, sourceEntry, sourceExit, sourceCertificate⟩ := realizable
  let _sourceScratchFinite := sourceScratchFinite
  let _sourceStateFinite := sourceStateFinite
  choose ProjectionScratch projectionScratchFinite projectionScratchDomains ProjectionState projectionStateFinite
    project projectionEntry projectionExit projectionCertificate using
      (fun name => namedRecordProjection_realizable computation.inputDomains name)
  let _ : ∀ name, Fintype (ProjectionScratch name) := projectionScratchFinite
  let _ : ∀ name, Fintype (ProjectionState name) := projectionStateFinite
  let target := computation.withRecordArgument
  let Scratch := (Σ name, ProjectionScratch name) ⊕ (InputName ⊕ SourceScratch)
  let scratch : Scratch → EncodedDomain Parameter :=
    Sum.elim (fun name => projectionScratchDomains name.1 name.2)
      (Sum.elim computation.inputDomains sourceScratchDomains)
  let argumentTape (name : InputName) : TapeName target Scratch := scratchTape target (.inr (.inl name))
  let projectionWiring (name : InputName) :
      TapeName (namedRecordProjection computation.inputDomains name) (ProjectionScratch name) ↪ TapeName target Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => .inl parameter
      | .inr (.inl _) => inputTape target ()
      | .inr (.inr (.inl _)) => argumentTape name
      | .inr (.inr (.inr temporary)) => scratchTape target (.inl ⟨name, temporary⟩)), by
      intro first second equal
      rcases first with parameter | argument | result | temporary <;>
        rcases second with parameter' | argument' | result' | temporary'
      all_goals first
        | (cases argument; cases argument'; rfl)
        | (cases result; cases result'; rfl)
        | (dsimp only [argumentTape, inputTape, scratchTape] at equal; cases equal <;> rfl)⟩
  let sourceWiring : TapeName computation SourceScratch ↪ TapeName target Scratch :=
    ⟨(fun role => match role with
      | .inl parameter => .inl parameter
      | .inr (.inl name) => argumentTape name
      | .inr (.inr (.inl _)) => outputTape target
      | .inr (.inr (.inr temporary)) => scratchTape target (.inr (.inr temporary))), by
      intro first second equal
      rcases first with parameter | argument | result | temporary <;>
        rcases second with parameter' | argument' | result' | temporary'
      all_goals first
        | (cases result; cases result'; rfl)
        | (dsimp only [argumentTape, outputTape, scratchTape] at equal; cases equal <;> rfl)⟩
  choose projectionBound executeProjection using (fun name => Internal.wiredRuns
    (projectionScratchDomains name) (project name) (projectionEntry name) (projectionExit name)
    (projectionCertificate name) (projectionWiring name))
  obtain ⟨sourceBound, executeSource⟩ := Internal.wiredRuns sourceScratchDomains source sourceEntry sourceExit
    sourceCertificate sourceWiring
  let enumeration := Fintype.equivFin InputName
  let components : ∀ index : Fin (Fintype.card InputName),
      Machine (Alphabet (TapeName target Scratch)) (ProjectionState (enumeration.symm index)) :=
    fun index => MultiTape.wire (projectionWiring (enumeration.symm index)) (project (enumeration.symm index))
  let entries (index : Fin (Fintype.card InputName)) := projectionEntry (enumeration.symm index)
  let exits (index : Fin (Fintype.card InputName)) := projectionExit (enumeration.symm index)
  let prepare := Pipeline.machine components entries
  let call : Machine (Alphabet (TapeName target Scratch)) SourceState := MultiTape.wire sourceWiring source
  let algorithm := MultiTape.sequence prepare call sourceEntry
  refine ⟨Scratch, inferInstance, scratch, _, inferInstance, algorithm,
    .inl (Pipeline.position entries 0), .inr sourceExit, ?_⟩
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
    Fintype.card InputName * ((∑ name, projectionBound name) + 1) + sourceBound + 1, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.sequence, call, MultiTape.wire, sourceCertificate.2.2.1]
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments target scratch sizes input
  let width := fun name => (Internal.domains target scratch name).width sizes
  let readonly : TapeName target Scratch → Bool := Internal.readOnly target
  let representation (stage : Fin (Fintype.card InputName + 1)) (tapes : Tapes (Alphabet (TapeName target Scratch))) : Prop :=
    (∀ parameter, tapes (.inl parameter) = unary (sizes parameter)) ∧
    tapes (inputTape target ()) = encoded (target.inputDomains ()) sizes (arguments ()) ∧
    (∀ name, Region (width name) 0 (tapes name)) ∧
    ∀ name, (enumeration name).val < stage.val →
      tapes (argumentTape name) = encoded (computation.inputDomains name) sizes (arguments () name)
  have initialRepresentation : representation 0 initial := by
    refine ⟨headers, represented.1 (inputTape target ()) rfl, represented.region, ?_⟩
    intro name before; exact False.elim (Nat.not_lt_zero _ before)
  have prepared := Pipeline.runs width readonly components entries exits representation
    (MvPolynomial.eval sizes (∑ name, projectionBound name))
    (by intro index symbols; simp [components, exits, MultiTape.wire, (projectionCertificate _).2.2.1])
    (by
      intro index tapes good
      let name := enumeration.symm index
      obtain ⟨sameHeaders, sameInput, regions, previous⟩ := good
      obtain ⟨ticks, final, cost, trace, correct, outside, preserved⟩ := executeProjection name sizes
        (fun _ => arguments ()) trivial width readonly tapes
        (by rintro (parameter | argument | result | temporary) <;> rfl)
        (by rintro (parameter | argument | result | temporary) premise <;> first | rfl | contradiction)
        sameHeaders (fun _ => sameInput) (fun role => regions (projectionWiring name role))
      refine ⟨ticks, final, ?_, trace, ?_⟩
      · simpa only [map_sum] using cost.trans
          (Finset.single_le_sum (fun other _ => Nat.zero_le (MvPolynomial.eval sizes (projectionBound other)))
            (Finset.mem_univ name))
      · refine ⟨?_, ?_, (fun role => trace.region role (regions role)), ?_⟩
        · intro parameter
          exact (trace.readOnly_tape (.inl parameter) rfl).trans (sameHeaders parameter)
        · exact (trace.readOnly_tape (inputTape target ()) rfl).trans sameInput
        · intro other before
          by_cases current : other = name
          · subst other
            exact correct
          · have earlier : (enumeration other).val < index.val := by
              have different : (enumeration other).val ≠ index.val := by
                intro equal
                exact current (enumeration.injective (Fin.ext (by simpa [name] using equal)))
              change (enumeration other).val < index.val + 1 at before
              omega
            refine (outside (argumentTape other) ?_).trans (previous other earlier)
            rintro ⟨role, equal⟩
            let label : TapeName target Scratch → Option InputName
              | .inr (.inr (.inr (.inr (.inl name)))) => some name
              | _ => none
            have selected := congrArg label equal
            rcases role with parameter | argument | result | temporary
            · change (none : Option InputName) = some other at selected
              contradiction
            · change (none : Option InputName) = some other at selected
              contradiction
            · change some name = some other at selected
              exact current (Option.some.inj selected).symm
            · change (none : Option InputName) = some other at selected
              contradiction)

    initial initialRepresentation
  obtain ⟨prepareTicks, middle, prepareCost, prepareTrace, ready⟩ := prepared
  obtain ⟨sourceTicks, final, sourceCost, sourceTrace, correct, outside, preserved⟩ := executeSource sizes
    (arguments ()) valid width readonly middle
    (by rintro (parameter | argument | result | temporary) <;> rfl)
    (by rintro (parameter | argument | result | temporary) premise <;> first | rfl | contradiction)
    ready.1 (fun name => ready.2.2.2 name (enumeration name).isLt)
    (fun role => ready.2.2.1 (sourceWiring role))
  have combined := prepareTrace.sequence call sourceEntry (by intro symbols; rfl) sourceTrace
  refine ⟨prepareTicks + (sourceTicks + 1), (fun _ => target.compute sizes ⟨arguments, valid⟩), final,
    ?_, (by simpa only [Nat.add_assoc] using combined), ⟨valid, rfl⟩, ?_⟩
  · simp only [map_add, map_mul, map_natCast, Nat.cast_id, map_one]
    omega
  · intro name; cases name
    exact correct

/-- Finite argument preparation uses ordinary record construction and the
record-argument adapter; implementation witnesses remain private. -/
theorem onResults {ContextName : Type} [Fintype ContextName]
    {computation : Computation Parameter InputName} (realizable : computation.Realizable)
    (context : ContextName → EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → Prop)
    (results : ∀ name sizes, {arguments // allowed sizes arguments} →
      (computation.inputDomains name).Carrier sizes)
    (valid : ∀ sizes arguments, computation.precondition sizes
      (fun name => results name sizes arguments))
    (producers : ∀ name,
      (Computation.mk context (computation.inputDomains name) allowed (results name)).Realizable) :
    (computation.onResults context allowed results valid).Realizable := by
  have named := Realizable.namedRecordOutputs context computation.inputDomains allowed results producers
  exact named.followedBy realizable.withRecordArgument rfl (by
    intro sizes arguments premise
    exact valid sizes ⟨arguments, premise⟩)

/-- Select any static family of context arguments, including repeated names.
The caller proves the callee's admissibility on exactly the selected values. -/
theorem onArguments {ContextName : Type} [Fintype ContextName]
    {computation : Computation Parameter InputName} (realizable : computation.Realizable)
    (context : ContextName → EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → Prop)
    (selection : InputName → ContextName)
    (domainEqual : ∀ name, context (selection name) = computation.inputDomains name)
    (valid : ∀ sizes (arguments : {arguments // allowed sizes arguments}), computation.precondition sizes
      (fun name => domainEqual name ▸ arguments.val (selection name))) :
    (computation.onResults context allowed
      (fun name _ arguments => domainEqual name ▸ arguments.val (selection name)) valid).Realizable := by
  rcases computation with ⟨domains, output, permitted, values⟩
  have domainsEqual : domains = fun name => context (selection name) :=
    funext (fun name => (domainEqual name).symm)
  subst domains
  apply realizable.onResults context allowed _ valid
  intro name
  exact argument context (selection name) allowed

end Realizable
end Polytime2.Computation
