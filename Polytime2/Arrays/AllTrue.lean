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

import Polytime2.Arrays.Contains
import Polytime2.Arithmetic.BitComparison
import Polytime2.Computation.RecordArguments

/-! # Testing every Boolean array entry

Test that false is absent from the array. This total predicate includes empty
arrays and supplies a mathematical guard for bounded controllers.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Return true exactly when every entry of the Boolean array is true. -/
noncomputable def arrayAllTrue (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (booleans.arrayOfLength length) booleans (fun _ _ => True)
    (fun _ values => (List.ofFn values.val).all id)

theorem arrayAllTrue_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayAllTrue length).Realizable := by
  let inputs := (arrayAllTrue length).inputDomains
  have absent := (arrayContains_realizable booleans length).onResults inputs (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => arguments.val () | true => false) (by intros; trivial) (by
      intro choice; cases choice
      · exact Realizable.argument inputs () (fun _ _ => True)
      · exact (booleanOperation_realizable (fun _ : Empty → Bool => false)).onResults inputs
          (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty))
  have complete := absent.followedBy
    (booleanOperation_realizable (fun values : Unit → Bool => !values ())) rfl (by intros; trivial)
  apply complete.withSpecification (fun _ _ => True) (arrayAllTrue length).compute (by intros; trivial)
  intro sizes arguments valid
  classical
  change Unit → (Fin (MvPolynomial.eval sizes length) → Bool) at arguments
  apply Bool.eq_iff_iff.mpr
  simp [followedBy, onResults, arrayContains, arrayAllTrue, unaryMap, booleanOperation,
    decide_eq_false_iff_not, List.all_eq_true]
  exact forall_congr' (fun _ => (Bool.not_eq_false _).to_iff)

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
