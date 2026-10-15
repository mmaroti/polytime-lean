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
import Polytime2.StandardBinaryScan

/-! # Packaging existing unary routines without exposing their tape names -/

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

-- carrierLevel: mathematical values represented by the existing unary routine.
universe carrierLevel
variable {Parameter : Type} [Fintype Parameter]

/-- The existing size/input/output convention has no private scratch. -/
theorem ofUnaryRealizes (computation : Computation.{carrierLevel} Parameter Unit)
    {State : Type} [Fintype State]
    (machine : Machine (Alphabet (Parameter ⊕ Bool)) State) (entry exit : State)
    (certificate : CallingConvention.Realizes
      (StandardBinaryScan.domains (computation.inputDomains ()) computation.outputDomain)
      StandardTerminatedCopy.readOnly StandardTerminatedCopy.sizeTapes machine entry exit
      (fun sizes input => computation.precondition sizes (fun _ => input ⟨.inr false, rfl⟩))
      (fun sizes input output => ∃ valid : computation.precondition sizes
          (fun _ => input ⟨.inr false, rfl⟩),
        output ⟨.inr true, rfl⟩ = computation.compute sizes
          ⟨(fun _ => input ⟨.inr false, rfl⟩), valid⟩)) : computation.Realizable := by
  classical
  let wiring : Parameter ⊕ Bool ↪ Internal.TapeName computation Empty :=
    ⟨(fun name => match name with
      | .inl parameter => .inl parameter
      | .inr false => Internal.inputTape computation ()
      | .inr true => (Internal.outputTape computation)), by
      intro first second equal
      rcases first with parameter | flag <;> rcases second with parameter' | flag'
      · simpa using equal
      · cases flag' <;> cases equal
      · cases flag <;> cases equal
      · cases flag <;> cases flag' <;> first | rfl | cases equal⟩
  let scratchDomains : Empty → EncodedDomain.{0, carrierLevel} Parameter := Empty.elim
  refine ⟨Empty, inferInstance, scratchDomains, State, inferInstance,
    MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Empty)) wiring machine,
    entry, exit, ?_⟩
  obtain ⟨bound, execute⟩ := certificate.wired_runs wiring
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [MultiTape.wire, certificate.2.1]), bound, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let localInput : Inputs
      (StandardBinaryScan.domains (computation.inputDomains ()) computation.outputDomain)
      StandardTerminatedCopy.readOnly sizes := fun name => match name with
    | ⟨.inl _, _⟩ => PUnit.unit
    | ⟨.inr false, _⟩ => arguments ()
    | ⟨.inr true, impossible⟩ => False.elim (Bool.noConfusion impossible)
  have sameArguments : (fun _ : Unit => localInput ⟨.inr false, rfl⟩) = arguments := by
    funext name
    cases name
    rfl
  obtain ⟨ticks, localOutput, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes localInput
      (fun name => (Internal.domains computation scratchDomains name).width sizes)
      (Internal.readOnly computation) initial
      (by intro name; rcases name with parameter | flag; rfl; cases flag <;> rfl)
      (by intro name readonly; rcases name with parameter | flag; rfl; cases flag <;> first | rfl | contradiction)
      (by simpa only [sameArguments] using valid)
      (by
        intro name readonly
        rcases name with parameter | flag
        · exact (headers parameter).trans (encoded_unary parameter sizes).symm
        · cases flag
          · exact represented.1 (Internal.inputTape computation ()) rfl
          · contradiction)
      (by intro name writable; exact represented.region (wiring name)) headers
  obtain ⟨good, result⟩ := correct
  have outputValue : localOutput ⟨.inr true, rfl⟩ = computation.compute sizes ⟨arguments, valid⟩ := by
    simpa only [sameArguments] using result
  let output : Outputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes :=
    fun name => match name with
      | ⟨.inl _, impossible⟩ => False.elim (Bool.noConfusion impossible)
      | ⟨.inr (.inl _), impossible⟩ => False.elim (Bool.noConfusion impossible)
      | ⟨.inr (.inr (.inl _)), _⟩ => computation.compute sizes ⟨arguments, valid⟩
      | ⟨.inr (.inr (.inr scratch)), _⟩ => Empty.elim scratch
  refine ⟨ticks, output, final, cost, trace, ⟨valid, rfl⟩, ?_⟩
  intro name writable
  rcases name with parameter | argument | resultName | scratch
  · contradiction
  · contradiction
  · cases resultName
    exact (canonical (.inr true) rfl).trans (congrArg (encoded computation.outputDomain sizes) outputValue)
  · exact Empty.elim scratch

end Polytime2.Computation.Realizable.Internal
