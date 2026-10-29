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

import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.Operations
import Polytime2.Computation.Conditional

/-! # Combining runtime arrays pointwise

A certified scalar operation with immutable context lifts to arrays of the
same mathematical length. Their element types and widths may differ. The
realization prepares positions and reuses array lookup and tabulation.
-/

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- Combine a finite family of arrays pointwise, retaining immutable context. -/
noncomputable def arrayZip {Argument : Type} [Fintype Argument]
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (elements : Argument → EncodedDomain.{0, 0} Parameter) (target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (∀ name, (elements name).Carrier sizes) → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Argument) where
  inputDomains := Sum.elim context (fun name => (elements name).arrayOfLength length)
  outputDomain := target.arrayOfLength length
  precondition _ _ := True
  compute sizes arguments index := operation sizes (fun name => arguments.val (.inl name))
    (fun name => arguments.val (.inr name) index)

theorem arrayZip_realizable {Argument : Type} [Fintype Argument]
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (elements : Argument → EncodedDomain.{0, 0} Parameter) (target : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (∀ name, (elements name).Carrier sizes) → target.Carrier sizes)
    (step : (Computation.mk (Sum.elim context elements) target (fun _ _ => True)
      (fun sizes arguments => operation sizes (fun name => arguments.val (.inl name))
        (fun name => arguments.val (.inr name)))).Realizable) :
    (arrayZip context elements target length operation).Realizable := by
  let computation := arrayZip context elements target length operation
  let tabulateOperation sizes (arguments : computation.Arguments sizes) index :=
    computation.compute sizes ⟨arguments, trivial⟩ index
  let tabulateStep := arrayTransformStep computation.inputDomains (EncodedDomain.arrayPosition length)
    target tabulateOperation
  have entry (name : Argument) := (Realizable.Internal.arrayLookupWithIndex_realizable
    (elements name) (EncodedDomain.arrayPosition length) (fun _ index => index.val)
    (EncodedDomain.arrayPosition_value length) length).onArguments tabulateStep.inputDomains (fun _ _ => True)
      (fun choice => match choice with | false => .inr () | true => .inl (.inr name))
      (by intro choice; cases choice <;> rfl) (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  have tabulateReady : tabulateStep.Realizable := step.onResults tabulateStep.inputDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | .inl original => arguments.val (.inl (.inl original))
      | .inr name => arguments.val (.inl (.inr name)) (arguments.val (.inr ())))
    (by intros; trivial) (by
      intro name
      cases name with
      | inl original => exact Realizable.argument tabulateStep.inputDomains (.inl (.inl original)) (fun _ _ => True)
      | inr name => exact entry name)
  exact arrayTabulate_realizable computation.inputDomains target length tabulateOperation tabulateReady

noncomputable def arrayZipWithStep (context : Context → EncodedDomain.{0, 0} Parameter)
    (first second target : EncodedDomain.{0, 0} Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      first.Carrier sizes → second.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun choice => if choice then second else first)
  outputDomain := target
  precondition _ _ := True
  compute sizes arguments := operation sizes (fun name => arguments.val (.inl name))
    (arguments.val (.inr false)) (arguments.val (.inr true))

/-- Combine corresponding entries while retaining ordinary mathematical arrays. -/
noncomputable def arrayZipWith (context : Context → EncodedDomain.{0, 0} Parameter)
    (first second target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      first.Carrier sizes → second.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun choice => (if choice then second else first).arrayOfLength length)
  outputDomain := target.arrayOfLength length
  precondition _ _ := True
  compute sizes arguments index := operation sizes (fun name => arguments.val (.inl name))
    (arguments.val (.inr false) index) (arguments.val (.inr true) index)

theorem arrayZipWith_realizable (context : Context → EncodedDomain.{0, 0} Parameter)
    (first second target : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      first.Carrier sizes → second.Carrier sizes → target.Carrier sizes)
    (step : (arrayZipWithStep context first second target operation).Realizable) :
    (arrayZipWith context first second target length operation).Realizable := by
  exact arrayZip_realizable context (fun choice : Bool => if choice then second else first) target length
    (fun sizes values entries => operation sizes values (entries false) (entries true)) step

/-- Lift a certified total binary computation pointwise. Argument preparation
is proved here rather than by unfolding the scalar answer at each caller. -/
theorem Realizable.zipWith
    {inputs : Bool → EncodedDomain Parameter} {output : EncodedDomain Parameter}
    {value : ∀ sizes, {arguments : ∀ name, (inputs name).Carrier sizes // True} → output.Carrier sizes}
    (ready : (Computation.mk inputs output (fun _ _ => True) value).Realizable)
    (length : MvPolynomial Parameter ℕ) :
    (arrayZipWith (Empty.elim : Empty → EncodedDomain Parameter) (inputs false) (inputs true) output length
      (fun sizes _ first second => value sizes
        ⟨(fun choice => match choice with | false => first | true => second), trivial⟩)).Realizable := by
  apply arrayZipWith_realizable
  let step := arrayZipWithStep (Empty.elim : Empty → EncodedDomain Parameter)
    (inputs false) (inputs true) output
    (fun sizes _ first second => value sizes
      ⟨(fun choice => match choice with | false => first | true => second), trivial⟩)
  apply ready.onResults step.inputDomains step.precondition
    (fun choice _ arguments => match choice with
      | false => arguments.val (.inr false)
      | true => arguments.val (.inr true)) (by intros; trivial)
  intro choice
  cases choice
  · exact Realizable.argument step.inputDomains (.inr false) step.precondition
  · exact Realizable.argument step.inputDomains (.inr true) step.precondition

/-- Named-size zip retains the direct mathematical `Fin (sizes parameter)`
carrier while reusing the polynomial-length zip implementation. -/
noncomputable def arrayZipWithAtParameter
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (first second target : EncodedDomain.{0, 0} Parameter) (parameter : Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      first.Carrier sizes → second.Carrier sizes → target.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun choice => (if choice then second else first).array parameter)
  outputDomain := target.array parameter
  precondition _ _ := True
  compute sizes arguments index := operation sizes (fun name => arguments.val (.inl name))
    (arguments.val (.inr false) index) (arguments.val (.inr true) index)

theorem arrayZipWithAtParameter_realizable
    (context : Context → EncodedDomain.{0, 0} Parameter)
    (first second target : EncodedDomain.{0, 0} Parameter) (parameter : Parameter)
    (operation : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      first.Carrier sizes → second.Carrier sizes → target.Carrier sizes)
    (step : (arrayZipWithStep context first second target operation).Realizable) :
    (arrayZipWithAtParameter context first second target parameter operation).Realizable := by
  let inputMap (name : Context ⊕ Bool) sizes :
      ((arrayZipWithAtParameter context first second target parameter operation).inputDomains name).Carrier sizes →
        ((arrayZipWith context first second target (MvPolynomial.X parameter) operation).inputDomains name).Carrier sizes :=
    match name with
    | .inl _ => id
    | .inr choice => EncodedDomain.arrayParameterEquiv (if choice then second else first) parameter sizes
  have prepared := (arrayZipWith_realizable context first second target (MvPolynomial.X parameter)
    operation step).reinterpretInputs
      (arrayZipWithAtParameter context first second target parameter operation).inputDomains inputMap
      (by rintro (name | choice) sizes <;> rfl)
      (by
        rintro (name | choice) sizes value
        · rfl
        · exact EncodedDomain.array_X_encode_bits (if choice then second else first) parameter sizes value)
      (fun _ _ => True) (by intros; trivial)
  exact prepared.reinterpretOutput (target.array parameter)
    (fun sizes => (EncodedDomain.arrayParameterEquiv target parameter sizes).symm)
    (EncodedDomain.arrayParameter_width target parameter)
    (fun sizes value => EncodedDomain.array_X_encode_bits target parameter sizes _)

end Polytime2.Computation
