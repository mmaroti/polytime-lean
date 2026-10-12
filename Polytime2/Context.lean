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

/-! # Mathematical contracts with preserved caller context

The context is ghost data shared by both representations, not a machine input.
These contracts reuse `Computes` on pairs, so its composition rules still apply.
-/

namespace Polytime2.MultiTape

-- parameterLevel: size names; tapeLevel: tape roles; symbolLevel: tape symbols.
-- stateLevel: controllers; contextLevel: caller data; inputLevel/outputLevel: values.
universe parameterLevel tapeLevel symbolLevel stateLevel contextLevel inputLevel outputLevel

variable {Parameter : Type parameterLevel} [Fintype Parameter]
variable {TapeName : Type tapeLevel} [Fintype TapeName]
variable {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)] [∀ name, Fintype (Alphabet name)]
variable {State : Type stateLevel} [Fintype State]
variable {Context : (Parameter → ℕ) → Type contextLevel}
variable {Input : (Parameter → ℕ) → Type inputLevel}
variable {Output : (Parameter → ℕ) → Type outputLevel}

/-- Both representations refer to exactly the same caller context. -/
abbrev ComputesWithContext (machine : Machine Alphabet State) (entry exit : State)
    (inputRepresentation : ∀ assignment, Context assignment → Input assignment → Tapes Alphabet → Prop)
    (outputRepresentation : ∀ assignment, Context assignment → Output assignment → Tapes Alphabet → Prop)
    (hypothesis : ∀ assignment, Input assignment → Prop)
    (compute : ∀ assignment, Input assignment → Output assignment) : Prop :=
  Computes (Input := fun assignment => Context assignment × Input assignment)
    (Output := fun assignment => Context assignment × Output assignment) machine entry exit
    (fun assignment value => inputRepresentation assignment value.1 value.2)
    (fun assignment value => outputRepresentation assignment value.1 value.2)
    (fun assignment value => hypothesis assignment value.2)
    (fun assignment value => (value.1, compute assignment value.2))

namespace Computes

-- sourceLevel: a component's tape roles.
universe sourceLevel

/-- Lift a component contract while retaining caller tapes and their heads
outside its wiring. The polynomial is independent of the caller's contents. -/
theorem wireWithContext {Source : Type sourceLevel} [Fintype Source]
    (wiring : Source ↪ TapeName)
    {component : Machine (fun name => Alphabet (wiring name)) State} {entry exit : State}
    {inputRepresentation : ∀ assignment, Input assignment → Tapes (fun name => Alphabet (wiring name)) → Prop}
    {outputRepresentation : ∀ assignment, Output assignment → Tapes (fun name => Alphabet (wiring name)) → Prop}
    {hypothesis : ∀ assignment, Input assignment → Prop}
    {compute : ∀ assignment, Input assignment → Output assignment}
    (certificate : Computes component entry exit inputRepresentation outputRepresentation hypothesis compute) :
    ComputesWithContext (Context := fun _ => Tapes Alphabet)
      (MultiTape.wire wiring component) entry exit
      (fun assignment caller value tapes =>
        inputRepresentation assignment value (fun name => tapes (wiring name)) ∧
        ∀ name, name ∉ Set.range wiring → tapes name = caller name)
      (fun assignment caller value tapes =>
        outputRepresentation assignment value (fun name => tapes (wiring name)) ∧
        ∀ name, name ∉ Set.range wiring → tapes name = caller name)
      hypothesis compute := by
  obtain ⟨halt, bound, runs⟩ := certificate
  refine ⟨by intro symbols; simp [MultiTape.wire, halt], bound, ?_⟩
  intro assignment value initial valid represented
  obtain ⟨ticks, final, cost, trace, encoded⟩ := runs assignment value.2 _ valid represented.1
  refine ⟨ticks, install wiring final initial, cost,
    wire_steps wiring _ trace initial (by intro name; rfl), ?_, ?_⟩
  · simpa only [install_at] using encoded
  · intro name outside
    rw [install_outside wiring final initial name outside]
    exact represented.2 name outside

end Computes

namespace ComputesWithContext

-- middleLevel: intermediate values; firstLevel/secondLevel: component controllers.
universe middleLevel firstLevel secondLevel

/-- Composition shares one caller context, with no context-dependent cost. -/
theorem sequence
    {Middle : (Parameter → ℕ) → Type middleLevel}
    {First : Type firstLevel} [Fintype First] {Second : Type secondLevel} [Fintype Second]
    {first : Machine Alphabet First} {second : Machine Alphabet Second}
    {firstEntry firstExit : First} {secondEntry secondExit : Second}
    {inputRepresentation : ∀ assignment, Context assignment → Input assignment → Tapes Alphabet → Prop}
    {middleRepresentation : ∀ assignment, Context assignment → Middle assignment → Tapes Alphabet → Prop}
    {outputRepresentation : ∀ assignment, Context assignment → Output assignment → Tapes Alphabet → Prop}
    {firstHypothesis : ∀ assignment, Input assignment → Prop}
    {secondHypothesis : ∀ assignment, Middle assignment → Prop}
    {firstMap : ∀ assignment, Input assignment → Middle assignment}
    {secondMap : ∀ assignment, Middle assignment → Output assignment}
    (firstCertificate : ComputesWithContext first firstEntry firstExit
      inputRepresentation middleRepresentation firstHypothesis firstMap)
    (secondCertificate : ComputesWithContext second secondEntry secondExit
      middleRepresentation outputRepresentation secondHypothesis secondMap)
    (compatible : ∀ assignment value,
      firstHypothesis assignment value → secondHypothesis assignment (firstMap assignment value)) :
    ComputesWithContext (MultiTape.sequence first second secondEntry) (.inl firstEntry) (.inr secondExit)
      inputRepresentation outputRepresentation firstHypothesis
      (fun assignment value => secondMap assignment (firstMap assignment value)) := by
  exact Computes.sequence firstCertificate secondCertificate
    (fun assignment value good => compatible assignment value.2 good)

end ComputesWithContext
end Polytime2.MultiTape
