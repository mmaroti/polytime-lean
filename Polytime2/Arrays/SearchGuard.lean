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

import Polytime2.Arrays.FindFalse
import Polytime2.Arrays.Indices
import Polytime2.Computation.Equality
import Polytime2.Computation.RecordArguments
import Polytime2.Computation.Conditional

/-! # Discriminating optional array-search results

Test whether a search returned no coordinate. Canonical equality compares the
result with the absent value constructed by searching an all-true array. The
implementation reuses existing realizations and works at length zero.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def absent (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := arraySearchResult length
  precondition _ _ := True
  compute _ _ := none

private theorem absent_realizable (length : MvPolynomial Parameter ℕ) : (absent length).Realizable := by
  have searched := (arrayTrue_realizable length).followedBy (arrayFindFalse_realizable length) rfl (by intros; trivial)
  apply searched.withSpecification (fun _ _ => True) (absent length).compute (by intros; trivial)
  intro sizes arguments valid
  exact (arrayFindFalse_none length sizes (fun _ => true)).mpr (by intros; rfl)

/-- Decide whether an optional coordinate is absent, without exposing its sentinel encoding. -/
noncomputable def arraySearchIsNone (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arraySearchResult length) booleans (fun _ _ => True) (fun _ value => value.val.isNone)

/-- Equality with the canonical absent result realizes the optional-result guard. -/
theorem arraySearchIsNone_realizable (length : MvPolynomial Parameter ℕ) :
    (arraySearchIsNone length).Realizable := by
  classical
  let computation := arraySearchIsNone length
  have missing := (absent_realizable length).onResults computation.inputDomains computation.precondition
    (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  have compared := (elementsEqual_realizable (arraySearchResult length)).onResults
    computation.inputDomains computation.precondition
    (fun choice _ arguments => match choice with | false => arguments.val () | true => none)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains () computation.precondition
      · exact missing)
  apply compared.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  change decide (arguments () = none) = (arguments ()).isNone
  cases arguments () <;> simp

/-- The guard accepts exactly the absent mathematical result. -/
theorem arraySearchIsNone_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (result : Option (Fin (MvPolynomial.eval sizes length))) :
    (arraySearchIsNone length).compute sizes ⟨(fun _ => result), trivial⟩ = true ↔ result = none := by
  change result.isNone = true ↔ result = none
  cases result <;> simp

end Polytime2.Computation
