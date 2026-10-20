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

import Polytime2.Arithmetic.DivisionOperations

/-! # Remainder as a projection of certified binary division

The public remainder interface keeps its original width and positive-divisor
precondition. Its realization shares the quotient-and-remainder implementation.
-/

namespace Polytime2.Computation

/-- Remainder at the operands' original width requires only a positive divisor. -/
noncomputable def binaryRemainder : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition _ arguments := 0 < (arguments true).val
  compute _ arguments := ⟨(arguments.val false).val % (arguments.val true).val,
    lt_trans (Nat.mod_lt _ arguments.property) (arguments.val true).isLt⟩

theorem binaryRemainder_realizable : binaryRemainder.Realizable := by
  have projected := binaryDivision_realizable.followedBy
    (pairProjection_realizable (EncodedDomain.binaryNaturals ())
      (EncodedDomain.binaryNaturals ()) true) rfl (by intros; trivial)
  exact projected.withSpecification binaryRemainder.precondition binaryRemainder.compute
    (by intros; assumption) (by intros; rfl)

end Polytime2.Computation
