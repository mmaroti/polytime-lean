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
import Polytime2.Arrays.PackingTransport

/-! # Array transformation at a named size parameter -/

namespace Polytime2.Computation

open EncodedDomain ArrayPacking

variable {Parameter : Type} [Fintype Parameter]

/-- The named-size form has the direct mathematical array carrier. -/
noncomputable def mapArrayAtParameter (source target : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter Unit where
  inputDomains _ := source.array parameter
  outputDomain := target.array parameter
  precondition _ _ := True
  compute sizes arguments := fun index => operation sizes (arguments.val () index)

private theorem namedArray_bits (element : EncodedDomain.{0, 0} Parameter) (parameter : Parameter)
    (sizes : Parameter → ℕ) (values : Fin (sizes parameter) → element.Carrier sizes) :
    ArrayEncoding.bits ((element.array parameter).encode sizes values) =
      ArrayEncoding.bits ((element.arrayOfLength (MvPolynomial.X parameter)).encode sizes
        ((Equiv.arrowCongr (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl _)) values)) := by
  simp only [EncodedDomain.array, arrayOfLength, ofCodec, ArrayEncoding.bits_cast,
    ArrayEncoding.bits_encode]
  exact congrArg List.flatten
    (List.ofFn_congr (MvPolynomial.eval_X parameter).symm
      (fun position => ArrayEncoding.bits (element.encode sizes (values position))))

/-- Lift a total certified element operation at a named length, retaining any
fixed finite family of immutable context tapes. -/
noncomputable def arrayTransformAtParameter {Context : Type} [Fintype Context]
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (source target : EncodedDomain.{0, 0} Parameter) (parameter : Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Unit) where
  inputDomains := Sum.elim context (fun _ => source.array parameter)
  outputDomain := target.array parameter
  precondition _ _ := True
  compute sizes arguments := fun position => operation sizes
    (fun name => arguments.val (.inl name)) (arguments.val (.inr ()) position)

theorem arrayTransformAtParameter_realizable {Context : Type} [Fintype Context]
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (source target : EncodedDomain.{0, 0} Parameter) (parameter : Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) → source.Carrier sizes → target.Carrier sizes)
    (step : (arrayTransformStep context source target operation).Realizable) :
    (arrayTransformAtParameter context source target parameter operation).Realizable := by
  let computation := arrayTransformAtParameter context source target parameter operation
  let sourceEquiv (sizes : Parameter → ℕ) := Equiv.arrowCongr
    (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl (source.Carrier sizes))
  let targetEquiv (sizes : Parameter → ℕ) := Equiv.arrowCongr
    (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl (target.Carrier sizes))
  let argumentsEquiv (name : Context ⊕ Unit) sizes :
      (computation.inputDomains name).Carrier sizes ≃
        ((arrayTransform context source target (MvPolynomial.X parameter) operation).inputDomains name).Carrier sizes :=
    match name with
    | .inl _ => Equiv.refl _
    | .inr _ => sourceEquiv sizes
  have presented := (arrayTransform_realizable context source target (MvPolynomial.X parameter) operation step).reindexDomains
    computation.inputDomains computation.outputDomain argumentsEquiv targetEquiv
    (by rintro (name | name) sizes; rfl; simp [computation, arrayTransformAtParameter, arrayTransform,
      EncodedDomain.array, arrayOfLength, ofCodec])
    (by intros; simp [computation, arrayTransformAtParameter, arrayTransform, EncodedDomain.array, arrayOfLength, ofCodec])
    (by
      rintro (name | name) sizes value
      · rfl
      · apply bits_injective
        rw [ArrayEncoding.bits_cast]
        exact namedArray_bits source parameter sizes value)
    (by intro sizes value; apply bits_injective; rw [ArrayEncoding.bits_cast]; exact namedArray_bits target parameter sizes value)
  exact presented.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    funext position
    rfl)

theorem mapArrayAtParameter_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (step : (unaryMap source target (fun _ _ => True) (fun sizes value => operation sizes value.val)).Realizable) :
    (mapArrayAtParameter source target parameter operation).Realizable := by
  let computation := mapArrayAtParameter source target parameter operation
  let sourceEquiv (sizes : Parameter → ℕ) := Equiv.arrowCongr
    (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl (source.Carrier sizes))
  let targetEquiv (sizes : Parameter → ℕ) := Equiv.arrowCongr
    (finCongr (MvPolynomial.eval_X (f := sizes) parameter).symm) (Equiv.refl (target.Carrier sizes))
  have presented := (mapArray_realizable source target (MvPolynomial.X parameter) operation step).reindexDomains
    computation.inputDomains computation.outputDomain (fun _ sizes => sourceEquiv sizes) targetEquiv
    (by intros; simp [computation, mapArrayAtParameter, mapArray, EncodedDomain.array,
      EncodedDomain.arrayOfLength, EncodedDomain.ofCodec])
    (by intros; simp [computation, mapArrayAtParameter, mapArray, EncodedDomain.array,
      EncodedDomain.arrayOfLength, EncodedDomain.ofCodec])
    (by intro name sizes value; apply bits_injective; rw [ArrayEncoding.bits_cast]; exact namedArray_bits source parameter sizes value)
    (by intro sizes value; apply bits_injective; rw [ArrayEncoding.bits_cast]; exact namedArray_bits target parameter sizes value)
  exact presented.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    funext position
    rfl)

end Polytime2.Computation
