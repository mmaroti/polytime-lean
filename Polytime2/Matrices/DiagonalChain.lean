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

import Polytime2.Matrices.NaturalDiagonalSearch
import Polytime2.Arrays.AllTrue

/-! # Certified stopping guard for diagonal cleanup

Test the adjacent divisibility chain on a bounded natural diagonal. The search
and this guard share the same certified flags, and therefore agree on stopping,
including empty and singleton arrays.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Decide whether the natural diagonal is an adjacent divisibility chain. -/
noncomputable def naturalDiagonalIsChain (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (naturalDiagonalDivisibilityFlags length width).followedBy (arrayAllTrue length) rfl (by intros; trivial)

theorem naturalDiagonalIsChain_realizable (length width : MvPolynomial Parameter ℕ) :
    (naturalDiagonalIsChain length width).Realizable :=
  (naturalDiagonalDivisibilityFlags_realizable length width).followedBy (arrayAllTrue_realizable length) rfl
    (by intros; trivial)

/-- The guard expresses exactly the mathematical stopping condition. -/
theorem naturalDiagonalIsChain_correct (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    (naturalDiagonalIsChain length width).compute sizes ⟨(fun _ => values), trivial⟩ = true ↔
      IntegerMatrix.diagonalDivisibilityChain (fun index => (values index).val) := by
  change (arrayAllTrue length).compute sizes
    ⟨(fun _ => (naturalDiagonalDivisibilityFlags length width).compute sizes ⟨(fun _ => values), trivial⟩), trivial⟩ = true ↔ _
  rw [arrayAllTrue_correct, naturalDiagonalDivisibilityFlags_spec]
  exact ArraySearch.adjacentFlags_all (fun first second : ℕ => first ∣ second) (fun index => (values index).val)

/-- The Boolean guard stops exactly when the optional search has no repair. -/
theorem naturalDiagonalIsChain_search (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : ((binaryNaturalsOfWidth width).arrayOfLength length).Carrier sizes) :
    (naturalDiagonalIsChain length width).compute sizes ⟨(fun _ => values), trivial⟩ = true ↔
      (naturalDiagonalSearch length width).compute sizes ⟨(fun _ => values), trivial⟩ = none :=
  (naturalDiagonalIsChain_correct length width sizes values).trans
    (IntegerMatrix.diagonalViolation_none _).symm |>.trans (naturalDiagonalSearch_none length width sizes values).symm

end Polytime2.Computation
