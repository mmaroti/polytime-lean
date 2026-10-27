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

import Polytime2.Arrays.FoldContract
import Polytime2.Arithmetic.BitComparison
import Polytime2.Computation.RecordArguments

/-! # Testing every Boolean array entry

Fold conjunction over the array with initial value true. This total predicate
includes empty arrays and supplies a mathematical guard for bounded controllers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Return true exactly when every entry of the Boolean array is true. -/
noncomputable def arrayAllTrue (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (booleans.arrayOfLength length) booleans (fun _ _ => True)
    (fun _ values => (List.ofFn values.val).all id)

private theorem fold_and_all (flags : List Bool) (initial : Bool) :
    flags.foldl (· && ·) initial = (initial && flags.all id) := by
  induction flags generalizing initial with
  | nil => simp
  | cons flag flags hypothesis => simp [hypothesis, Bool.and_assoc]

theorem arrayAllTrue_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayAllTrue length).Realizable := by
  let computation := arrayAllTrue length
  let context : Empty → EncodedDomain Parameter := Empty.elim
  let update (_sizes : Parameter → ℕ) (_context : ∀ name, (context name).Carrier _sizes)
      (accumulator flag : Bool) := accumulator && flag
  have step : (arrayFoldStep context booleans booleans (fun _ _ _ _ => True) update).Realizable := by
    have ready := (booleanOperation_realizable (Parameter := Parameter)
      (fun arguments : Bool → Bool => arguments false && arguments true)).withArguments
        (arrayFoldStep context booleans booleans (fun _ _ _ _ => True) update).inputDomains
        ⟨Sum.inr, Sum.inr_injective⟩ (by intro name; cases name <;> rfl)
    exact ready.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)
  have folded := arrayFold_total_realizable context booleans booleans length update step
  let results (name : Empty ⊕ Bool) (sizes : Parameter → ℕ)
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((arrayFold context booleans booleans length (fun _ _ _ _ => True) update).inputDomains name).Carrier sizes :=
    match name with
    | .inl impossible => nomatch impossible
    | .inr false => true
    | .inr true => arguments.val ()
  have complete := folded.onResults computation.inputDomains computation.precondition results
    (by intros; trivial) (by
      intro name
      rcases name with impossible | flag
      · exact impossible.elim
      · cases flag
        · exact ((booleanOperation_realizable (Parameter := Parameter) (fun _ : Empty → Bool => true)).onResults
            computation.inputDomains computation.precondition (fun impossible => impossible.elim)
            (by intros; trivial) (fun impossible => impossible.elim))
        · exact Realizable.argument computation.inputDomains () computation.precondition)
  apply complete.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  change Unit → (Fin (MvPolynomial.eval sizes length) → Bool) at arguments
  change ArrayFold.prefixValue (fun accumulator flag => accumulator && flag) (arguments ()) true
    (MvPolynomial.eval sizes length) = (List.ofFn (arguments ())).all id
  have taken : (List.ofFn (arguments ())).take (MvPolynomial.eval sizes length) =
      List.ofFn (arguments ()) := List.take_of_length_le (by simp)
  dsimp only [ArrayFold.prefixValue]
  rw [taken]
  simpa using fold_and_all (List.ofFn (arguments ())) true

/-- The executable guard has the ordinary universal mathematical specification. -/
theorem arrayAllTrue_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    (arrayAllTrue length).compute sizes ⟨(fun _ => flags), trivial⟩ = true ↔ ∀ index, flags index = true := by
  change (List.ofFn flags).all id = true ↔ _
  simp

/-- Named-size conjunction uses ordinary coordinates in the public carrier. -/
noncomputable def arrayAllTrueAtParameter (parameter : Parameter) : Computation Parameter Unit :=
  (arrayAllTrue (MvPolynomial.X parameter)).reinterpretInputs
    (fun _ => booleans.array parameter)
    (fun _ sizes => arrayParameterEquiv booleans parameter sizes)
    (fun _ _ => True) (by intros; trivial)

theorem arrayAllTrueAtParameter_realizable (parameter : Parameter) :
    (arrayAllTrueAtParameter parameter).Realizable := by
  exact (arrayAllTrue_realizable (MvPolynomial.X parameter)).reinterpretInputs
    (fun _ => booleans.array parameter)
    (fun _ sizes => arrayParameterEquiv booleans parameter sizes)
    (by intros; rfl) (by intro name sizes value; exact array_X_encode_bits booleans parameter sizes value)
    (fun _ _ => True) (by intros; trivial)

theorem arrayAllTrueAtParameter_correct (parameter : Parameter) (sizes : Parameter → ℕ)
    (flags : Fin (sizes parameter) → Bool) :
    (arrayAllTrueAtParameter parameter).compute sizes ⟨(fun _ => flags), trivial⟩ = true ↔
      ∀ index, flags index = true := by
  change (arrayAllTrue (MvPolynomial.X parameter)).compute sizes
    ⟨(fun _ => arrayParameterEquiv booleans parameter sizes flags), trivial⟩ = true ↔ _
  rw [arrayAllTrue_correct]
  change (∀ index, flags ((finCongr (MvPolynomial.eval_X (f := sizes) parameter)) index) = true) ↔ _
  exact ((finCongr (MvPolynomial.eval_X (f := sizes) parameter)).surjective.forall
    (p := fun index => flags index = true)).symm

end Polytime2.Computation
