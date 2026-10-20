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

import Polytime2.Arithmetic.BoundedTraversal
import Polytime2.GaussJordan.Elimination

/-! # Safe calls in the outer elimination controller -/

namespace Polytime2.StandardGaussJordanElimination

open MultiTape CallingConvention StandardMatrixRows

variable {Scalar : Type} [Field Scalar] {cardinality : ℕ}

omit [Field Scalar] in
theorem guard_runs (enumeration : Scalar ≃ Fin cardinality) :
    ∃ bound : MvPolynomial (Fin 3) ℕ, ∀ (sizes : Fin 3 → ℕ) (initial : Tapes Alphabet)
      (columnIndex limit : Fin (2 ^ sizes 0)),
      initial (sizeTape 0) = unary (sizes 0) →
      initial columnTape = encoded (EncodedDomain.binaryNaturals 0) sizes columnIndex →
      initial limitTape = encoded (EncodedDomain.binaryNaturals 0) sizes limit →
      Region (sizes 0) 0 (initial differenceTape) → Region 1 0 (initial guardTape) →
      ∃ ticks final, ticks ≤ MvPolynomial.eval sizes bound ∧
        Runs (fun name => (domains enumeration name).width sizes) readOnly guard ticks
          BinarySubtraction.entry (fun _ => 0) initial BinarySubtraction.exit (fun _ => 0) final ∧
        final guardTape = encoded EncodedDomain.booleans sizes (decide (columnIndex.val < limit.val)) ∧
        (∀ name, name ≠ differenceTape → name ≠ guardTape → final name = initial name) := by
  exact BinaryTraversal.comparison_runs 0 (fun sizes name => (domains enumeration name).width sizes)
    readOnly guardWiring
    (by
      intro sizes name
      fin_cases name
      · change (EncodedDomain.unary.{0, 0} (0 : Fin 3)).width sizes = (EncodedDomain.unary.{0, 0} ()).width _
        simp [EncodedDomain.unary, EncodedDomain.ofCodec]
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.binaryNaturals (0 : Fin 3)).width sizes = (EncodedDomain.binaryNaturals ()).width _
        simp
      · change (EncodedDomain.booleans (Parameter := Fin 3)).width sizes = (EncodedDomain.booleans (Parameter := Unit)).width _
        simp [EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.ofCodec])
    (by intro name premise; fin_cases name <;> first | rfl | contradiction)

end Polytime2.StandardGaussJordanElimination
