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

/-! # Array transformation at a named size parameter -/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- The named-size form has the direct mathematical array carrier. -/
noncomputable def mapArrayAtParameter (source target : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter Unit where
  inputDomains _ := source.array parameter
  outputDomain := target.array parameter
  precondition _ _ := True
  compute sizes arguments := fun index => operation sizes (arguments.val () index)

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
  let inputMap (name : Context ⊕ Unit) sizes :
      ((arrayTransformAtParameter context source target parameter operation).inputDomains name).Carrier sizes →
        ((arrayTransform context source target (MvPolynomial.X parameter) operation).inputDomains name).Carrier sizes :=
    match name with
    | .inl _ => id
    | .inr _ => arrayParameterEquiv source parameter sizes
  apply (arrayTransform_realizable context source target (MvPolynomial.X parameter) operation step).withEncoding
    (target := arrayTransformAtParameter context source target parameter operation) inputMap
    (by rintro (name | name) sizes <;> rfl)
    (arrayParameter_width target parameter)
    (by
      rintro (name | name) sizes value
      · rfl
      · exact congrArg CallingConvention.tape (array_X_encode_bits source parameter sizes value))
    (by intros; trivial)
  intro sizes arguments
  exact congrArg CallingConvention.tape (array_X_encode_bits target parameter sizes _)

theorem mapArrayAtParameter_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (step : (unaryMap source target (fun _ _ => True) (fun sizes value => operation sizes value.val)).Realizable) :
    (mapArrayAtParameter source target parameter operation).Realizable := by
  apply (mapArray_realizable source target (MvPolynomial.X parameter) operation step).withEncoding
    (target := mapArrayAtParameter source target parameter operation)
    (fun _ sizes => arrayParameterEquiv source parameter sizes)
    (by intros; rfl) (arrayParameter_width target parameter)
    (fun _ sizes value => congrArg CallingConvention.tape (array_X_encode_bits source parameter sizes value))
    (by intros; trivial)
  intro sizes arguments
  exact congrArg CallingConvention.tape (array_X_encode_bits target parameter sizes _)

end Polytime2.Computation
