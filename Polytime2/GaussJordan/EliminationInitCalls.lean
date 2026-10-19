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

import Polytime2.GaussJordan.EliminationSeed
import Polytime2.Primitives.Initialization

/-! # Unary column-limit reading -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

def columnLimitWiring : Sum Bool Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl false => sizeTape 2 | .inl true => sizeTape 0
    | .inr false => limitTape | .inr true => differenceTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> first | rfl | exact absurd equal (by decide)⟩

noncomputable def readColumns : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire columnLimitWiring StandardSizeRead.algorithm

@[simp] theorem readColumns_halt (symbols : Symbols Alphabet) :
    readColumns StandardSizeRead.exit symbols = none := rfl

omit [Field Scalar] in
theorem readColumns_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (fits : sizes 2 < 2 ^ sizes 0),
      (∀ parameter, initial (sizeTape parameter) = unary (sizes parameter)) →
      Region (sizes 0) 0 (initial limitTape) → Region (sizes 0) 0 (initial differenceTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly readColumns ticks
          StandardSizeRead.entry (fun _ => 0) initial StandardSizeRead.exit (fun _ => 0) final ∧
        final limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes ⟨sizes 2, fits⟩ ∧
        (∃ value : Fin (2 ^ sizes 0), final differenceTape = encoded (EncodedDomain.binaryNaturals 0) sizes value) ∧
        (∀ name, name ≠ limitTape → name ≠ differenceTape → final name = initial name) := by
  refine ⟨4 * MvPolynomial.X 0 + MvPolynomial.X 2 * (4 * MvPolynomial.X 0 + 8) + 11, ?_⟩
  intro sizes initial fits headers limitRegion scratchRegion
  let localSizes : Bool → ℕ := fun name => if name then sizes 0 else sizes 2
  obtain ⟨final, trace, resultEq, scratchEq, outside⟩ :=
    Initialization.readSize_runs columnLimitWiring 2 0 sizes
      (fun name => (domains enumeration name).width sizes) readOnly initial
      (by
        intro name
        fin_cases name
        · change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = (EncodedDomain.unary.{0, 0} true).width localSizes
          simp [EncodedDomain.unary, EncodedDomain.ofCodec, localSizes]
        · change (EncodedDomain.unary.{0, 0} (2 : Fin 3)).width sizes = (EncodedDomain.unary.{0, 0} false).width localSizes
          simp [EncodedDomain.unary, EncodedDomain.ofCodec, localSizes]
        · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals true).width localSizes
          simp [localSizes]
        · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals true).width localSizes
          simp [localSizes])
      (by intro name premise; fin_cases name <;> first | rfl | contradiction)
      (by intro name; cases name <;> exact headers _) fits limitRegion scratchRegion
  refine ⟨_, final, ?_, trace, resultEq, scratchEq, outside⟩
  simp [localSizes]

end Polytime2.StandardGaussJordanElimination
