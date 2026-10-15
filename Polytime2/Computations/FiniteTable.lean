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
import Polytime2.StandardFiniteTable

/-! # Two separate mathematical arguments implemented by a fixed finite table -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

-- carrierLevel: arbitrary mathematical carriers of specialization-fixed domains.
universe carrierLevel

/-- False and true name the two arguments, whose carrier types may differ. -/
def finiteTable (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, firstDomain.Carrier sizes → secondDomain.Carrier sizes →
      outputDomain.Carrier sizes) : Computation Empty Bool where
  inputDomains | false => firstDomain | true => secondDomain
  outputDomain := outputDomain
  precondition _ _ := True
  compute sizes arguments := operation sizes (arguments.val false) (arguments.val true)

/-- The existing finite-table machine certifies a public binary computation. -/
theorem finiteTable_realizable
    (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ sizes, firstDomain.Carrier sizes → secondDomain.Carrier sizes →
      outputDomain.Carrier sizes) : (finiteTable firstDomain secondDomain outputDomain operation).Realizable := by
  classical
  let computation := finiteTable firstDomain secondDomain outputDomain operation
  let scratchDomains : Empty → EncodedDomain.{0, carrierLevel} Empty := Empty.elim
  let wiring : Fin 3 ↪ Internal.TapeName computation Empty :=
    ⟨(fun name => match name.val with
      | 0 => Internal.inputTape computation false
      | 1 => Internal.inputTape computation true
      | _ => (Internal.outputTape computation)), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
  refine ⟨Empty, inferInstance, scratchDomains,
    StandardFiniteTable.State (firstDomain.width Empty.elim)
      (secondDomain.width Empty.elim) (outputDomain.width Empty.elim), inferInstance,
    MultiTape.wire (Alphabet := Alphabet (Internal.TapeName computation Empty)) wiring
      (StandardFiniteTable.algorithm firstDomain secondDomain outputDomain operation),
    StandardFiniteTable.entry, StandardFiniteTable.exit, ?_⟩
  have certificate := StandardFiniteTable.contract firstDomain secondDomain outputDomain operation
  obtain ⟨bound, execute⟩ := certificate.wired_runs wiring
  refine ⟨(by intro parameter; cases parameter),
    (by intro symbols; simp [MultiTape.wire, certificate.2.1]), bound, ?_⟩
  intro sizes input initial valid represented headers
  let arguments := Internal.arguments computation scratchDomains sizes input
  let localInput : Inputs (StandardFiniteTable.domains firstDomain secondDomain outputDomain)
      StandardFiniteTable.readOnly sizes
    | ⟨0, _⟩ => arguments false
    | ⟨1, _⟩ => arguments true
    | ⟨2, impossible⟩ => False.elim (Bool.noConfusion impossible)
  obtain ⟨ticks, localOutput, final, cost, trace, correct, canonical, outside, immutable⟩ :=
    execute sizes localInput
      (fun name => (Internal.domains computation scratchDomains name).width sizes)
      (Internal.readOnly computation) initial
      (by intro name; fin_cases name <;> rfl)
      (by intro name readonly; fin_cases name <;> first | rfl | contradiction)
      True.intro
      (by
        intro name readonly
        fin_cases name
        · exact represented.1 (Internal.inputTape computation false) rfl
        · exact represented.1 (Internal.inputTape computation true) rfl
        · contradiction)
      (by intro name writable; exact represented.region (wiring name))
      (by intro parameter; cases parameter)
  let output : Outputs (Internal.domains computation scratchDomains) (Internal.readOnly computation) sizes :=
    fun name => match name with
      | ⟨.inl parameter, _⟩ => Empty.elim parameter
      | ⟨.inr (.inl _), impossible⟩ => False.elim (Bool.noConfusion impossible)
      | ⟨.inr (.inr (.inl _)), _⟩ => operation sizes (arguments false) (arguments true)
      | ⟨.inr (.inr (.inr scratch)), _⟩ => Empty.elim scratch
  refine ⟨ticks, output, final, cost, trace, ⟨True.intro, rfl⟩, ?_⟩
  intro name writable
  rcases name with parameter | argument | resultName | scratch
  · exact Empty.elim parameter
  · contradiction
  · cases resultName
    exact (canonical 2 rfl).trans (congrArg (encoded outputDomain sizes) correct)
  · exact Empty.elim scratch

end Polytime2.Computation
