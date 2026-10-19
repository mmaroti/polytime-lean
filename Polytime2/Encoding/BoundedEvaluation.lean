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

import Polytime2.Encoding.PolynomialEvaluator
import Polytime2.Encoding.SizeSubstitution

/-! # Polynomial evaluation at bounded computed assignments

The existing evaluator also runs on privately prepared unary sizes. Its live
regions and runtime are majorized by caller polynomials, while the output is
the exact value at the computed assignment, including zero.
-/

namespace Polytime2.PolynomialEvaluator

open MultiTape CallingConvention

variable {Parameter CallerParameter : Type} [Fintype Parameter]

/-- One finite evaluator works at every polynomially bounded runtime assignment
inside larger caller capacities; no runtime bound or scratch is public. -/
theorem computable_bounded (polynomial : MvPolynomial Parameter ℕ)
    (sizeBounds : Parameter → MvPolynomial CallerParameter ℕ) :
    ∃ (Scratch : Type) (_finiteScratch : Fintype Scratch) (role : Scratch → Parameter)
      (State : Type) (_finiteState : Fintype State)
      (machine : Machine (Alphabet (TapeName Parameter Scratch)) State)
      (entry exit : State) (bound : MvPolynomial CallerParameter ℕ),
      (∀ symbols, machine exit symbols = none) ∧
      ∀ {TargetTape : Type} (wiring : TapeName Parameter Scratch ↪ TargetTape)
        (callerSizes : CallerParameter → ℕ) (computedSizes : Parameter → ℕ)
        (_bounded : ∀ parameter, computedSizes parameter ≤ MvPolynomial.eval callerSizes (sizeBounds parameter))
        (width : TargetTape → ℕ) (immutable : TargetTape → Bool)
        (initial : Tapes (Alphabet TargetTape)),
        (∀ name, widths role computedSizes (MvPolynomial.eval computedSizes polynomial) name ≤ width (wiring name)) →
        (∀ name, immutable (wiring name) = true → readOnly name = true) →
        (∀ parameter, initial (wiring (.inl parameter)) = unary (computedSizes parameter)) →
        (∀ name, Region (widths role computedSizes (MvPolynomial.eval computedSizes polynomial) name) 0
          (initial (wiring name))) →
        ∃ ticks final, ticks ≤ MvPolynomial.eval callerSizes bound ∧
          Runs width immutable (MultiTape.wire wiring machine) ticks entry (fun _ => 0)
            initial exit (fun _ => 0) final ∧
          (∀ name, final (wiring name) = result role computedSizes (MvPolynomial.eval computedSizes polynomial) name) ∧
          (∀ name, name ∉ Set.range wiring → final name = initial name) := by
  obtain ⟨Scratch, finiteScratch, role, State, finiteState, machine, entry, exit, bound, halt, evaluate⟩ :=
    computable polynomial
  let _scratchFinite := finiteScratch
  let _stateFinite := finiteState
  refine ⟨Scratch, finiteScratch, role, State, finiteState, machine, entry, exit,
    SizeSubstitution.polynomial sizeBounds bound, halt, ?_⟩
  intro TargetTape wiring callerSizes computedSizes bounded width immutable initial fits readonly headers regions
  obtain ⟨ticks, cost, trace⟩ := evaluate computedSizes (fun name => initial (wiring name)) headers regions
  have enlarged := trace.regions (fun name => width (wiring name)) (fun _ => 0) (by
    intro name writable
    constructor
    · omega
    · simp only [zero_add]
      exact_mod_cast fits name)
  simp only [add_zero] at enlarged
  obtain ⟨final, lifted, located, outside, preserved⟩ :=
    enlarged.wire_restoring wiring width immutable (fun _ => rfl) readonly initial (fun _ => rfl)
  exact ⟨ticks, final, cost.trans (SizeSubstitution.eval_le sizeBounds bound callerSizes computedSizes bounded),
    lifted, located, outside⟩

end Polytime2.PolynomialEvaluator
