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

/-! # Combining two runtime arrays pointwise

A certified scalar operation with immutable context lifts to two arrays of the
same mathematical length. Their element types and widths may differ. The
realization prepares positions and reuses array lookup and tabulation.
-/

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

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
  let computation := arrayZipWith context first second target length operation
  let tabulateOperation sizes (arguments : computation.Arguments sizes) index :=
    computation.compute sizes ⟨arguments, trivial⟩ index
  let tabulateStep := arrayTransformStep computation.inputDomains (EncodedDomain.arrayPosition length)
    target tabulateOperation
  have entry (choice : Bool) := (Realizable.Internal.arrayLookupWithIndex_realizable
    (if choice then second else first) (EncodedDomain.arrayPosition length) (fun _ index => index.val)
    (EncodedDomain.arrayPosition_value length) length).onArguments tabulateStep.inputDomains (fun _ _ => True)
      (fun name => match name with
      | false => (.inr ())
      | true => (.inl (.inr choice))) (by intro name; cases name <;> rfl) (by intro sizes arguments; exact (arguments.val (.inr ())).isLt)
  have tabulateReady : tabulateStep.Realizable := step.onResults tabulateStep.inputDomains (fun _ _ => True)
    (fun name _ arguments => match name with
      | .inl original => arguments.val (.inl (.inl original))
      | .inr false => arguments.val (.inl (.inr false)) (arguments.val (.inr ()))
      | .inr true => arguments.val (.inl (.inr true)) (arguments.val (.inr ())))
    (by intros; trivial) (by
      intro name
      cases name with
      | inl original => exact Realizable.argument tabulateStep.inputDomains (.inl (.inl original)) (fun _ _ => True)
      | inr choice => cases choice; exact entry false; exact entry true)
  exact arrayTabulate_realizable computation.inputDomains target length tabulateOperation tabulateReady

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

end Polytime2.Computation
