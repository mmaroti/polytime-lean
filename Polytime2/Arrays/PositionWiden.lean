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

import Polytime2.Arrays.Indices
import Polytime2.Arithmetic.WidthOperations

/-! # Widening finite coordinates without changing their mathematical value

A coordinate in `Fin length` can be used in the larger interval
`Fin (length + extra)`. The runtime appends high zero bits, using the existing
canonical coordinate encodings and zero-extension certificate.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Enlarge a coordinate's bound and encoding width while retaining its ordinary value. -/
noncomputable def arrayPositionWiden (length extra : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (arrayPosition length) (arrayPosition (length + extra)) (fun sizes index =>
    ⟨index.val, index.isLt.trans_le (by simp only [map_add]; omega)⟩)

theorem arrayPositionWiden_realizable (length extra : MvPolynomial Parameter ℕ) :
    (arrayPositionWiden length extra).Realizable := by
  apply zeroExtendEncoding_realizable (arrayPosition length) (arrayPosition (length + extra)) extra
  · intro sizes
    change MvPolynomial.eval sizes (length + extra + 1) =
      MvPolynomial.eval sizes (length + 1) + MvPolynomial.eval sizes extra
    simp only [map_add, map_one]
    omega
  · intro sizes index
    let target : (arrayPosition (length + extra)).Carrier sizes :=
      ⟨index.val, index.isLt.trans_le (by simp only [map_add]; omega)⟩
    let first := ((arrayPosition length).encode sizes index).toFin
    let second := ((arrayPosition (length + extra)).encode sizes target).toFin
    have same : second.val = first.val := by
      simp [first, second, target, arrayPosition, boundedIndexOfWidth]
    have fits : (arrayPosition length).width sizes ≤ (arrayPosition (length + extra)).width sizes := by
      change MvPolynomial.eval sizes (length + 1) ≤ MvPolynomial.eval sizes (length + extra + 1)
      simp only [map_add, map_one]
      omega
    have difference : (arrayPosition (length + extra)).width sizes - (arrayPosition length).width sizes =
        MvPolynomial.eval sizes extra := by
      change MvPolynomial.eval sizes (length + extra + 1) - MvPolynomial.eval sizes (length + 1) = _
      simp only [map_add, map_one]
      omega
    simpa only [first, second, BitVec.ofFin_toFin, difference] using bits_ofFin_widen first second same fits

/-- Widening retains the numeric coordinate, rather than introducing a new position. -/
theorem arrayPositionWiden_value (length extra : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (index : (arrayPosition length).Carrier sizes) :
    ((arrayPositionWiden length extra).compute sizes ⟨(fun _ => index), trivial⟩).val = index.val := rfl

end Polytime2.Computation
