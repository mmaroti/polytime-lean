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

import Polytime2.Computation.Realizable

/-! # Reuse computations in larger mathematical argument contexts -/

namespace Polytime2.Computation.Realizable

open MultiTape CallingConvention

-- carrierLevel: mathematical values; context and implementation names use Type.
universe carrierLevel
variable {Parameter InputName ContextName : Type}
variable [Fintype Parameter] [Fintype InputName] [Fintype ContextName]

/-- Unused mathematical arguments need no tape copies or validity obligations
beyond the public input convention. Selection is static and injective. -/
theorem withArguments {computation : Computation.{carrierLevel} Parameter InputName}
    (realizable : computation.Realizable)
    (contextDomains : ContextName → EncodedDomain.{0, carrierLevel} Parameter)
    (selection : InputName ↪ ContextName)
    (domainEqual : ∀ name, contextDomains (selection name) = computation.inputDomains name) :
    (computation.withArguments contextDomains selection domainEqual).Realizable := by
  classical
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    machine, entry, exit, certificate⟩ := realizable
  let scratchFiniteInstance : Fintype ScratchName := finiteScratch
  let stateFiniteInstance : Fintype State := finiteStates
  let extended := computation.withArguments contextDomains selection domainEqual
  let wiring : Internal.TapeName computation ScratchName ↪ Internal.TapeName extended ScratchName :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr (.inl argument) => .inr (.inl (selection argument))
      | .inr (.inr localName) => .inr (.inr localName)), by
      intro first second equal
      rcases first with parameter | argument | result | scratch <;>
        rcases second with parameter' | argument' | result' | scratch' <;>
        simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
          selection.injective.eq_iff]⟩
  refine ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    MultiTape.wire (Alphabet := Alphabet (Internal.TapeName extended ScratchName)) wiring machine,
    entry, exit, ?_⟩
  obtain ⟨bound, execute⟩ := Internal.wiredRuns scratchDomains machine entry exit certificate wiring
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [MultiTape.wire, certificate.2.2.1]), bound, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments extended scratchDomains sizes input
  let selected : computation.Arguments sizes :=
    fun name => domainEqual name ▸ arguments (selection name)
  have widths : ∀ name,
      (Internal.domains extended scratchDomains (wiring name)).width sizes =
        (Internal.domains computation scratchDomains name).width sizes := by
    intro name
    rcases name with parameter | argument | result | scratch
    · rfl
    · exact congrArg (fun domain => domain.width sizes) (domainEqual argument)
    · rfl
    · rfl
  have encoding (source target : EncodedDomain.{0, carrierLevel} Parameter)
      (equal : source = target) (value : source.Carrier sizes) :
      encoded source sizes value = encoded target sizes (equal ▸ value) := by
    cases equal
    rfl
  obtain ⟨ticks, final, cost, trace, correct, outside, immutable⟩ := execute sizes selected valid
    (fun name => (Internal.domains extended scratchDomains name).width sizes)
    (Internal.readOnly extended) initial widths
    (by intro name readonly; rcases name with parameter | argument | result | scratch <;>
      first | rfl | contradiction) headers
    (by
      intro name
      exact (represented.1 (Internal.inputTape extended (selection name)) rfl).trans
        (encoding _ _ (domainEqual name) (arguments (selection name))))
    (fun name => represented.region (wiring name))
  refine ⟨ticks, (fun _ => extended.compute sizes ⟨arguments, valid⟩), final,
    cost, trace, ⟨valid, rfl⟩, ?_⟩
  intro name
  cases name
  exact correct

end Polytime2.Computation.Realizable
