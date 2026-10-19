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
import Polytime2.Encoding.SizeSubstitution

/-! # Executing a realized computation at polynomially bounded computed sizes

Private tapes may reserve larger polynomial capacities than the callee uses.
The live regions must be prepared with blank surroundings before the call.
The resulting execution certificate hides the callee's runtime polynomial.
-/

namespace Polytime2.Computation.Realizable.Internal

open MultiTape CallingConvention

universe carrierLevel
variable {Parameter CallerParameter InputName : Type}
variable [Fintype Parameter] [Fintype InputName]
variable {computation : Computation.{carrierLevel} Parameter InputName}

/-- Polynomial majorization and region enlargement let a fixed machine run at
input-dependent sizes inside a caller's fixed polynomial capacities. -/
theorem boundedWiredRuns {ScratchName State TargetTape : Type}
    [Fintype ScratchName] [Fintype State]
    (scratchDomains : ScratchName → EncodedDomain.{0, carrierLevel} Parameter)
    (machine : Machine (Alphabet (TapeName computation ScratchName)) State)
    (entry exit : State)
    (certificate : CallingConvention.Realizes (domains computation scratchDomains)
      (readOnly computation) (sizeTapes computation ScratchName)
      (outputTapes computation ScratchName) machine entry exit
      (fun sizes input => computation.precondition sizes
        (arguments computation scratchDomains sizes input))
      (resultCorrect computation scratchDomains))
    (wiring : TapeName computation ScratchName ↪ TargetTape)
    (sizeBounds : Parameter → MvPolynomial CallerParameter ℕ) :
    ∃ bound : MvPolynomial CallerParameter ℕ,
      ∀ (callerSizes : CallerParameter → ℕ) (computedSizes : Parameter → ℕ)
        (_bounded : ∀ parameter, computedSizes parameter ≤ MvPolynomial.eval callerSizes (sizeBounds parameter))
        (input : computation.Arguments computedSizes)
        (valid : computation.precondition computedSizes input)
        (width : TargetTape → ℕ) (immutable : TargetTape → Bool)
        (initial : Tapes (Alphabet TargetTape)),
        (∀ name, (domains computation scratchDomains name).width computedSizes ≤ width (wiring name)) →
        (∀ name, immutable (wiring name) = true → readOnly computation name = true) →
        (∀ parameter, initial (wiring (.inl parameter)) = unary (computedSizes parameter)) →
        (∀ name, initial (wiring (inputTape computation name)) =
          encoded (computation.inputDomains name) computedSizes (input name)) →
        (∀ name, Region ((domains computation scratchDomains name).width computedSizes) 0
          (initial (wiring name))) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval callerSizes bound ∧
          Runs width immutable (MultiTape.wire wiring machine) ticks entry (fun _ => 0)
            initial exit (fun _ => 0) final ∧
          final (wiring (outputTape computation)) = encoded computation.outputDomain computedSizes
            (computation.compute computedSizes ⟨input, valid⟩) ∧
          (∀ name, name ∉ Set.range wiring → final name = initial name) ∧
          (∀ name, readOnly computation name = true → final (wiring name) = initial (wiring name)) := by
  obtain ⟨bound, execute⟩ := runs scratchDomains machine entry exit certificate
  refine ⟨SizeSubstitution.polynomial sizeBounds bound, ?_⟩
  intro callerSizes computedSizes bounded input valid width immutable initial fits readonly headers inputs regions
  obtain ⟨ticks, localFinal, cost, trace, correct⟩ := execute computedSizes input valid
    (fun name => initial (wiring name)) headers inputs regions
  have enlarged := trace.regions (fun name => width (wiring name)) (fun _ => 0)
    (by
      intro name writable
      constructor
      · omega
      · simp only [zero_add]
        exact_mod_cast fits name)
  simp only [add_zero] at enlarged
  obtain ⟨final, lifted, located, outside, preserved⟩ :=
    enlarged.wire_restoring wiring width immutable (fun _ => rfl) readonly initial (fun _ => rfl)
  exact ⟨ticks, final, cost.trans (SizeSubstitution.eval_le sizeBounds bound callerSizes computedSizes bounded),
    lifted, (located _).trans correct, outside, preserved⟩

end Polytime2.Computation.Realizable.Internal
