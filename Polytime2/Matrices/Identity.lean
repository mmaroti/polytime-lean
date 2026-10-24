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

import Polytime2.Matrices.Tabulate
import Polytime2.Encoding.IntegerMatrices
import Polytime2.Computation.Equality
import Polytime2.Arithmetic.SignedConstruction

/-! # Runtime integer identity matrices

The input is only the mathematical dimension. The result is the ordinary
integer identity matrix with fixed magnitude width one. Position enumeration,
comparison, tabulation, and canonical output construction are certified by
composition, including dimension zero.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Construct the integer identity at the runtime dimension, with no input values. -/
noncomputable def integerIdentity (rows : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := integerMatrices rows rows 1
  precondition _ _ := True
  compute _ _ := ⟨1, by intro row column; by_cases same : row = column <;> simp [Matrix.one_apply, same]⟩

set_option backward.isDefEq.respectTransparency false in
theorem integerIdentity_realizable (rows : MvPolynomial Parameter ℕ) : (integerIdentity rows).Realizable := by
  classical
  let operation sizes (_arguments : ∀ name : Empty, (Empty.elim name : EncodedDomain Parameter).Carrier sizes) (row column : Fin (MvPolynomial.eval sizes rows)) :
      (binaryIntegers (1 : MvPolynomial Parameter ℕ)).Carrier sizes :=
    ⟨if row = column then 1 else 0, by split_ifs <;> norm_num⟩
  let step := matrixTabulateStep (Context := Empty) Empty.elim (binaryIntegers 1) rows rows operation
  have compared := (elementsEqual_realizable (arrayPosition rows)).withArguments step.inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name <;> rfl)
  let scalar (flags : Unit → Bool) : {value : ℤ // value.natAbs < 2} :=
    if flags () then ⟨1, by decide⟩ else ⟨0, by decide⟩
  have computed := compared.followedBy (Realizable.Internal.integerBooleanOperation_realizable scalar)
    rfl (by intros; trivial)
  have ready : step.Realizable := by
    apply computed.withSpecification (fun _ _ => True) step.compute (by intros; trivial)
    intro sizes arguments valid
    apply Subtype.ext
    by_cases same : arguments (.inr false) = arguments (.inr true)
    all_goals simp [Computation.followedBy, Computation.withArguments, elementsEqual,
      Realizable.Internal.integerBooleanOperation, scalar, step, matrixTabulateStep, operation, same]
  have tabulated := matrixTabulate_realizable (Context := Empty) Empty.elim (binaryIntegers 1) rows rows operation ready
  have result := tabulated.reindexOutput (integerMatrices rows rows 1).Carrier
    (fun sizes => IntegerMatrix.entryBoundEquiv (2 ^ MvPolynomial.eval sizes (1 : MvPolynomial Parameter ℕ)))
  apply result.withSpecification (fun _ _ => True) (integerIdentity rows).compute (by intros; trivial)
  intro sizes arguments valid
  apply Subtype.ext
  funext row column
  dsimp only [Computation.reinterpretOutput, matrixTabulate]
  erw [IntegerMatrix.entryBoundEquiv_symm_apply]

end Polytime2.Computation
