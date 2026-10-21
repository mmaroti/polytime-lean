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

import Polytime2.Computation.Variants

/-! # Mathematical sums through the existing variant codec -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

namespace SumEncoding

noncomputable abbrev alternatives (left right : EncodedDomain.{0, 0} Parameter) : Fin 2 → EncodedDomain.{0, 0} Parameter :=
  fun | 0 => left | 1 => right

noncomputable def equivalence (left right : EncodedDomain.{0, 0} Parameter) (sizes : Parameter → ℕ) :
    (left.Carrier sizes ⊕ right.Carrier sizes) ≃ (variant 2 (alternatives left right)).Carrier sizes where
  toFun | .inl value => ⟨0, value⟩ | .inr value => ⟨1, value⟩
  invFun value := match value with | ⟨0, value⟩ => .inl value | ⟨1, value⟩ => .inr value
  left_inv value := by cases value <;> rfl
  right_inv value := by rcases value with ⟨tag, value⟩; fin_cases tag <;> rfl

end SumEncoding

/-- Ordinary alternatives, with the canonical discriminator and inactive zeros
of the existing variant codec. -/
noncomputable def sum (left right : EncodedDomain.{0, 0} Parameter) : EncodedDomain.{0, 0} Parameter :=
  (variant 2 (SumEncoding.alternatives left right)).reindex
    (fun sizes => left.Carrier sizes ⊕ right.Carrier sizes) (SumEncoding.equivalence left right)

end Polytime2.EncodedDomain

namespace Polytime2.Computation

open EncodedDomain
variable {Parameter : Type} [Fintype Parameter]

/-- Inject an ordinary left value using the existing variant implementation. -/
noncomputable def sumInl (left right : EncodedDomain.{0, 0} Parameter) : Computation Parameter Unit :=
  unaryMap left (left.sum right) (fun _ _ => True) (fun _ value => Sum.inl value.val)

theorem sumInl_realizable (left right : EncodedDomain.{0, 0} Parameter) :
    (sumInl left right).Realizable :=
  (variantInjection_realizable 2 (SumEncoding.alternatives left right) 0).reindexOutput
    (fun sizes => left.Carrier sizes ⊕ right.Carrier sizes) (SumEncoding.equivalence left right)

/-- Inject an ordinary right value using the existing variant implementation. -/
noncomputable def sumInr (left right : EncodedDomain.{0, 0} Parameter) : Computation Parameter Unit :=
  unaryMap right (left.sum right) (fun _ _ => True) (fun _ value => Sum.inr value.val)

theorem sumInr_realizable (left right : EncodedDomain.{0, 0} Parameter) :
    (sumInr left right).Realizable :=
  (variantInjection_realizable 2 (SumEncoding.alternatives left right) 1).reindexOutput
    (fun sizes => left.Carrier sizes ⊕ right.Carrier sizes) (SumEncoding.equivalence left right)

/-- Apply a certified branch to the selected alternative. Only its mathematical
precondition is required. -/
noncomputable def sumCases (left right output : EncodedDomain.{0, 0} Parameter)
    (allowedLeft : ∀ sizes, left.Carrier sizes → Prop)
    (allowedRight : ∀ sizes, right.Carrier sizes → Prop)
    (first : ∀ sizes, {value // allowedLeft sizes value} → output.Carrier sizes)
    (second : ∀ sizes, {value // allowedRight sizes value} → output.Carrier sizes) :
    Computation Parameter Unit where
  inputDomains _ := left.sum right
  outputDomain := output
  precondition sizes arguments := (arguments ()).elim (allowedLeft sizes) (allowedRight sizes)
  compute sizes arguments := match equal : arguments.val () with
    | .inl value => first sizes ⟨value, by simpa [equal] using arguments.property⟩
    | .inr value => second sizes ⟨value, by simpa [equal] using arguments.property⟩

theorem sumCases_realizable (left right output : EncodedDomain.{0, 0} Parameter)
    (allowedLeft : ∀ sizes, left.Carrier sizes → Prop)
    (allowedRight : ∀ sizes, right.Carrier sizes → Prop)
    (first : ∀ sizes, {value // allowedLeft sizes value} → output.Carrier sizes)
    (second : ∀ sizes, {value // allowedRight sizes value} → output.Carrier sizes)
    (firstReady : (unaryMap left output allowedLeft first).Realizable)
    (secondReady : (unaryMap right output allowedRight second).Realizable) :
    (sumCases left right output allowedLeft allowedRight first second).Realizable := by
  let allowed : ∀ tag sizes, ((SumEncoding.alternatives left right) tag).Carrier sizes → Prop
    | 0 => allowedLeft | 1 => allowedRight
  let branches : ∀ tag sizes, {value // allowed tag sizes value} → output.Carrier sizes
    | 0 => first | 1 => second
  have ready := variantCases_realizable 2 (SumEncoding.alternatives left right) output allowed branches (by
    intro tag; fin_cases tag
    · exact firstReady
    · exact secondReady)
  have reindexed := ready.reindexDomains (fun _ => left.sum right) output
    (fun _ => SumEncoding.equivalence left right) (fun _ => Equiv.refl _)
    (by intros; rfl) (by intros; rfl) (by intros; rfl) (by intros; rfl)
  exact reindexed.withSpecification (sumCases left right output allowedLeft allowedRight first second).precondition
    (sumCases left right output allowedLeft allowedRight first second).compute
    (by
      intro sizes arguments valid
      change Unit → left.Carrier sizes ⊕ right.Carrier sizes at arguments
      dsimp only [reindexDomains, variantCases]
      cases equal : arguments () <;> simpa [sumCases, SumEncoding.equivalence, allowed, equal] using valid)
    (by
      intro sizes arguments valid
      have same (value : left.Carrier sizes ⊕ right.Carrier sizes)
          (admissible : value.elim (allowedLeft sizes) (allowedRight sizes)) :
          branches ((SumEncoding.equivalence left right sizes) value).1 sizes
            ⟨((SumEncoding.equivalence left right sizes) value).2,
              by cases value <;> exact admissible⟩ =
          (sumCases left right output allowedLeft allowedRight first second).compute sizes
            ⟨(fun _ => value), admissible⟩ := by
        cases value <;> rfl
      exact same (arguments ()) valid)

end Polytime2.Computation
