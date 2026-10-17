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

/-! # Reusing specialization-fixed computations alongside runtime sizes -/

namespace Polytime2.Computation

universe carrierLevel
variable {Parameter InputName : Type} [Fintype Parameter] [Fintype InputName]

/-- Runtime sizes do not affect a specialization-fixed computation. -/
noncomputable def withConstantSizes (computation : Computation.{carrierLevel} Empty InputName) :
    Computation Parameter InputName where
  inputDomains name := (computation.inputDomains name).constant
  outputDomain := computation.outputDomain.constant
  precondition _ := computation.precondition Empty.elim
  compute _ := computation.compute Empty.elim

open MultiTape CallingConvention in
/-- The fixed machine leaves the additional size tapes untouched. -/
theorem Realizable.withConstantSizes {computation : Computation.{carrierLevel} Empty InputName}
    (realizable : computation.Realizable) :
    (computation.withConstantSizes (Parameter := Parameter)).Realizable := by
  classical
  obtain ⟨ScratchName, finiteScratch, scratchDomains, State, finiteStates,
    machine, entry, exit, certificate⟩ := realizable
  let scratchFiniteInstance : Fintype ScratchName := finiteScratch
  let stateFiniteInstance : Fintype State := finiteStates
  let target := computation.withConstantSizes (Parameter := Parameter)
  let scratch : ScratchName → EncodedDomain Parameter := fun name => (scratchDomains name).constant
  let wiring : Internal.TapeName computation ScratchName ↪ Internal.TapeName target ScratchName :=
    ⟨(fun | .inl empty => nomatch empty | .inr name => .inr name), by
      intro first second equal
      rcases first with empty | first
      · exact Empty.elim empty
      rcases second with empty | second
      · exact Empty.elim empty
      exact congrArg Sum.inr (Sum.inr.inj equal)⟩
  obtain ⟨bound, execute⟩ := Internal.wiredRuns scratchDomains machine entry exit certificate wiring
  refine ⟨ScratchName, finiteScratch, scratch, State, finiteStates,
    MultiTape.wire wiring machine, entry, exit, ?_⟩
  refine ⟨(by intro parameter; rfl), (by intro name; rfl),
    (by intro symbols; simp [MultiTape.wire, certificate.2.2.1]),
    MvPolynomial.C (MvPolynomial.eval Empty.elim bound), ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments target scratch sizes input
  obtain ⟨ticks, final, cost, trace, correct, outside, immutable⟩ :=
    execute Empty.elim arguments valid
      (fun name => (Internal.domains target scratch name).width sizes)
      (Internal.readOnly target) initial
      (by
        intro name
        rcases name with empty | argument | result | privateTape
        · exact Empty.elim empty
        all_goals
          change MvPolynomial.eval sizes (MvPolynomial.C _) = _
          rw [MvPolynomial.eval_C]
          rfl)
      (by
        intro name readonly
        rcases name with empty | argument | result | privateTape
        · exact Empty.elim empty
        · rfl
        · contradiction
        · contradiction)
      (by intro empty; exact Empty.elim empty)
      (by
        intro name
        exact (represented.1 (Internal.inputTape target name) rfl).trans
          (encoded_constant (computation.inputDomains name) sizes _))
      (fun name => represented.region (wiring name))
  refine ⟨ticks, (fun _ => target.compute sizes ⟨arguments, valid⟩), final,
    (by simpa using cost), trace, ⟨valid, rfl⟩, ?_⟩
  intro name
  cases name
  exact correct.trans (encoded_constant computation.outputDomain sizes _).symm

end Polytime2.Computation
