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

import Polytime2.Arrays.Transform
import Polytime2.Computation.Constant
import Polytime2.Primitives.FiniteOperations
import Polytime2.TM0.Computation

/-! # Array transformations with runtime widths and empty carriers -/

namespace Polytime2.Examples.Transform

open _root_.Polytime2.Computation

/-- Different runtime input and output widths, with an immutable context tape. -/
noncomputable def zeroWords : Computation (Fin 2) (Unit ⊕ Unit) :=
  arrayTransform (fun _ : Unit => EncodedDomain.bitVectors (MvPolynomial.X 0))
    (EncodedDomain.bitVectors (MvPolynomial.X 0)) (EncodedDomain.bitVectors (MvPolynomial.X 1))
    (MvPolynomial.X 0 + MvPolynomial.X 1) (fun sizes _ _ => BitVec.ofNat (MvPolynomial.eval sizes (MvPolynomial.X 1)) 0)

theorem zeroWords_realizable : zeroWords.Realizable := by
  apply arrayTransform_realizable
  exact (zeroBits_realizable (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ)).withArguments
    (arrayTransformStep (fun _ : Unit => EncodedDomain.bitVectors (MvPolynomial.X 0))
      (EncodedDomain.bitVectors (MvPolynomial.X 0)) (EncodedDomain.bitVectors (MvPolynomial.X 1))
      (fun sizes _ _ => BitVec.ofNat (MvPolynomial.eval sizes (MvPolynomial.X 1)) 0)).inputDomains
    ⟨Empty.elim, by intro impossible; exact impossible.elim⟩ (by intro impossible; exact impossible.elim)

theorem zeroWords_tm0 : zeroWords.TM0Realizable := zeroWords_realizable.tm0

/-- The collector needs no default element, even for a genuinely empty domain.
At zero length there is a valid empty input and output array. -/
noncomputable def emptyElements : Computation (Fin 2) (Empty ⊕ Unit) :=
  let domain := (EncodedDomain.fixed (Equiv.refl (Fin 0))).constant
  arrayTransform Empty.elim domain domain (MvPolynomial.X 0) (fun _ _ value => value)

theorem emptyElements_realizable : emptyElements.Realizable := by
  let domain : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 0))
  have copied := (finiteOperation_realizable (fun _ : Unit => domain) domain
    (fun values => values ())).withConstantSizes (Parameter := Fin 2)
  apply arrayTransform_realizable
  exact copied.withArguments
    (arrayTransformStep Empty.elim domain.constant domain.constant (fun _ _ value => value)).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name; rfl)

theorem emptyElements_tm0 : emptyElements.TM0Realizable := emptyElements_realizable.tm0

end Polytime2.Examples.Transform
