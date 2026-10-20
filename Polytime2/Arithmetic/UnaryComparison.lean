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

import Polytime2.Arithmetic.BitComparison

/-! # Recognizing the full-capacity unary sentinel -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- The full-capacity unary value is the all-accepted sentinel of a flag scan. -/
noncomputable def boundedUnaryIsFull (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := boundedUnary capacity
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := decide ((arguments.val ()).val = MvPolynomial.eval sizes capacity)

theorem boundedUnaryIsFull_realizable (capacity : MvPolynomial Parameter ℕ) :
    (boundedUnaryIsFull capacity).Realizable := by
  let computation := boundedUnaryIsFull capacity
  let domain := boundedUnary capacity
  have maximum := (polynomialUnarySize_realizable capacity).followedBy (encode_realizable domain)
    rfl (by intros; trivial)
  have compared := (bitsEqual_realizable capacity).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => if choice then domain.encode sizes (Fin.last _) else domain.encode sizes (arguments.val ()))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact encode_realizable domain
      · exact maximum.onResults computation.inputDomains computation.precondition
          (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim))
  exact compared.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    apply Bool.eq_iff_iff.mpr
    change decide (domain.encode sizes (arguments ()) = domain.encode sizes (Fin.last _)) = true ↔
      decide ((arguments ()).val = MvPolynomial.eval sizes capacity) = true
    simp only [decide_eq_true_eq]
    constructor
    · intro equal
      have decoded := congrArg (domain.decode sizes) equal
      have same : arguments () = Fin.last (MvPolynomial.eval sizes capacity) :=
        Option.some.inj (by simpa only [domain.decode_encode] using decoded)
      exact congrArg Fin.val same
    · intro equal
      exact congrArg (domain.encode sizes) (Fin.ext equal))

end Polytime2.Computation
