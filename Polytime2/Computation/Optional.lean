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
import Polytime2.Computation.Conditional

/-! # Optional mathematical results

Use the existing two-alternative variant codec for an absent result or an
actual value. The public carrier is Option; inactive payload bits remain
canonical zero padding inside the codec.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def alternatives (domain : EncodedDomain.{0, 0} Parameter) : Fin 2 → EncodedDomain Parameter :=
  ![fixed (Equiv.refl (Fin 1)), domain]

private noncomputable def optionalEquiv (domain : EncodedDomain.{0, 0} Parameter) (sizes : Parameter → ℕ) :
    Option (domain.Carrier sizes) ≃ ((index : Fin 2) × (alternatives domain index).Carrier sizes) where
  toFun value := match value with | none => ⟨0, (0 : Fin 1)⟩ | some value => ⟨1, value⟩
  invFun value := Fin.cases (fun _ => none)
    (fun index => Fin.cases (fun payload => some payload) (fun impossible => Fin.elim0 impossible) index)
    value.1 value.2
  left_inv := by intro value; cases value <;> rfl
  right_inv := by
    rintro ⟨index, value⟩
    fin_cases index
    · change Fin 1 at value
      fin_cases value
      rfl
    · rfl

/-- Canonically encode either no result or an actual mathematical value. -/
noncomputable def optional (domain : EncodedDomain.{0, 0} Parameter) : EncodedDomain Parameter :=
  (variant 2 (alternatives domain)).reindex (fun sizes => Option (domain.Carrier sizes)) (optionalEquiv domain)

end Polytime2.EncodedDomain

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Return an actual optional value. -/
noncomputable def optionalSome (domain : EncodedDomain.{0, 0} Parameter) : Computation Parameter Unit :=
  unaryMap domain (optional domain) (fun _ _ => True) (fun _ value => some value.val)

/-- Variant injection and the ordinary Option equivalence preserve canonical bits. -/
theorem optionalSome_realizable (domain : EncodedDomain.{0, 0} Parameter) :
    (optionalSome domain).Realizable := by
  have ready := (variantInjection_realizable 2 (EncodedDomain.alternatives domain) 1).reindexOutput
    (fun sizes => Option (domain.Carrier sizes)) (EncodedDomain.optionalEquiv domain)
  exact ready.withSpecification (fun _ _ => True) (optionalSome domain).compute (by intros; trivial) (by intros; rfl)

/-- Return the mathematical absence of a result without requiring a payload. -/
noncomputable def optionalNone (domain : EncodedDomain.{0, 0} Parameter) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := optional domain
  precondition _ _ := True
  compute _ _ := none

/-- The absent alternative uses canonical zero padding rather than an arbitrary value. -/
theorem optionalNone_realizable (domain : EncodedDomain.{0, 0} Parameter) :
    (optionalNone domain).Realizable := by
  let tag : EncodedDomain Parameter := fixed (Equiv.refl (Fin 1))
  have constant := (constant_realizable (fixed (Parameter := Empty) (Equiv.refl (Fin 1))) (fun _ => (0 : Fin 1))).withConstantSizes
    (Parameter := Parameter)
  have prepared := constant.reinterpretOutput tag (fun _ value => value) (by
    intro sizes
    simp [tag, EncodedDomain.constant, fixed, ofCodec, width, Computation.withConstantSizes, Computation.constant]) (by
    intro sizes value
    simp [tag, EncodedDomain.constant, fixed, ofCodec, Computation.withConstantSizes,
      Computation.constant, ArrayEncoding.bits_cast])
  have packed := prepared.followedBy (variantInjection_realizable 2 (EncodedDomain.alternatives domain) 0)
    rfl (by intros; trivial)
  have viewed := packed.reindexOutput (fun sizes => Option (domain.Carrier sizes)) (EncodedDomain.optionalEquiv domain)
  have selected := viewed.withArguments (Empty.elim : Empty → EncodedDomain Parameter)
    (Function.Embedding.refl Empty) (by intro impossible; exact impossible.elim)
  exact selected.withSpecification (fun _ _ => True) (optionalNone domain).compute (by intros; trivial) (by intros; rfl)

/-- Return the supplied value exactly when the Boolean condition holds. -/
noncomputable def optionalWhen (domain : EncodedDomain.{0, 0} Parameter) : Computation Parameter Bool where
  inputDomains choice := if choice then domain else booleans
  outputDomain := optional domain
  precondition _ _ := True
  compute _ arguments := if (show Bool from arguments.val false) then some (arguments.val true) else none

/-- Boolean selection composes the two certified optional constructors. -/
theorem optionalWhen_realizable (domain : EncodedDomain.{0, 0} Parameter) :
    (optionalWhen domain).Realizable := by
  let computation := optionalWhen domain
  let accepted (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) : Bool := arguments false
  have guard := Realizable.argument computation.inputDomains false computation.precondition
  apply Realizable.ofCases (computation := computation) accepted guard
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ accepted sizes arguments = true
    have ready := ((optionalSome_realizable domain).withArguments computation.inputDomains
      (MultiTape.oneTape true) (by intros; rfl)).withPrecondition allowed (by intros; trivial)
    apply ready.withSpecification allowed _ (by intros; trivial)
    intro sizes arguments valid
    change some _ = if accepted sizes arguments then some _ else none
    simp only [valid.2, ↓reduceIte]
    rfl
  · let rejected sizes arguments := computation.precondition sizes arguments ∧ accepted sizes arguments = false
    have ready := (optionalNone_realizable domain).onResults computation.inputDomains rejected
      (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
    apply ready.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    change none = if accepted sizes arguments then some _ else none
    simp only [valid.2, Bool.false_eq_true, ↓reduceIte]

/-- An actual result is returned precisely for an accepted condition and that value. -/
theorem optionalWhen_some_iff (domain : EncodedDomain.{0, 0} Parameter) (sizes : Parameter → ℕ)
    (arguments : (optionalWhen domain).Arguments sizes) (value : domain.Carrier sizes) :
    (optionalWhen domain).compute sizes ⟨arguments, trivial⟩ = some value ↔
      arguments false = true ∧ arguments true = value := by
  change (if (show Bool from arguments false) then some (arguments true) else none) = some value ↔ _
  cases flag : (show Bool from arguments false) <;> simp [flag]

/-- An absent result is exactly a rejected condition. -/
theorem optionalWhen_none_iff (domain : EncodedDomain.{0, 0} Parameter) (sizes : Parameter → ℕ)
    (arguments : (optionalWhen domain).Arguments sizes) :
    (optionalWhen domain).compute sizes ⟨arguments, trivial⟩ = none ↔ arguments false ≠ true := by
  change (if (show Bool from arguments false) then some (arguments true) else none) = none ↔ _
  cases flag : (show Bool from arguments false) <;> simp [flag]

end Polytime2.Computation
