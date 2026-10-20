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
      EncodedDomain.width])
    (by intros; simp [computation, arrayTransformAtParameter, arrayTransform, EncodedDomain.width])
    (by
      rintro (name | name) sizes value
      · rfl
      · exact array_X_encode_bits source parameter sizes value)
    (by intro sizes value; exact array_X_encode_bits target parameter sizes value)
  exact presented.withSpecification computation.precondition computation.compute (by intros; trivial) (by
    intro sizes arguments valid
    funext position
    rfl)

theorem mapArrayAtParameter_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (step : (unaryMap source target (fun _ _ => True) (fun sizes value => operation sizes value.val)).Realizable) :
    (mapArrayAtParameter source target parameter operation).Realizable := by
  have selected := step.withArguments
    (arrayTransformStep Empty.elim source target (fun sizes _ value => operation sizes value)).inputDomains
    ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name; rfl)
  have mapped := arrayTransformAtParameter_realizable Empty.elim source target parameter
    (fun sizes _ value => operation sizes value) selected
  exact mapped.withArguments (mapArrayAtParameter source target parameter operation).inputDomains
    ⟨Sum.elim Empty.elim id, by
      rintro (impossible | first) (impossible' | second) equal
      all_goals first | exact impossible.elim | exact impossible'.elim | exact congrArg Sum.inr equal⟩
    (by rintro (impossible | name); exact impossible.elim; cases name; rfl)

end Polytime2.Computation
