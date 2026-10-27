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
import Polytime2.Encoding.ParameterRename

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

/-- Optional encodings preserve an element conversion with equal widths and
identical canonical bits, including the inactive payload of none. -/
theorem optional_encode_bits_congr {TargetParameter : Type} [Fintype TargetParameter]
    (source : EncodedDomain Parameter) (target : EncodedDomain TargetParameter)
    (sourceSizes : Parameter → ℕ) (targetSizes : TargetParameter → ℕ)
    (convert : source.Carrier sourceSizes → target.Carrier targetSizes)
    (sameWidth : source.width sourceSizes = target.width targetSizes)
    (sameBits : ∀ value, ArrayEncoding.bits (source.encode sourceSizes value) =
      ArrayEncoding.bits (target.encode targetSizes (convert value)))
    (value : Option (source.Carrier sourceSizes)) :
    ArrayEncoding.bits ((optional source).encode sourceSizes value) =
      ArrayEncoding.bits ((optional target).encode targetSizes (value.map convert)) := by
  change ArrayEncoding.bits ((variant 2 (alternatives source)).encode sourceSizes
    ((optionalEquiv source sourceSizes) value)) =
      ArrayEncoding.bits ((variant 2 (alternatives target)).encode targetSizes
        ((optionalEquiv target targetSizes) (value.map convert)))
  rw [bits_variant_encode, bits_variant_encode]
  cases value with
  | none =>
    simp [optionalEquiv, alternatives, VariantEncoding.fields, List.ofFn_succ,
      ArrayEncoding.bits, fixed, ofCodec, sameWidth]
  | some value =>
    simp [optionalEquiv, alternatives, VariantEncoding.fields, List.ofFn_succ, fixed_encode_bits, sameBits]
    simp [ArrayEncoding.bits]

/-- Renaming sizes commutes with optional encoding without changing any bits. -/
theorem optional_renameParameters_bits {NewParameter : Type} [Fintype NewParameter]
    (domain : EncodedDomain Parameter) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) (value : Option (domain.Carrier (sizes ∘ names))) :
    ArrayEncoding.bits (((optional domain).renameParameters names).encode sizes value) =
      ArrayEncoding.bits ((optional (domain.renameParameters names)).encode sizes value) := by
  rw [renameParameters_bits]
  have equal := optional_encode_bits_congr domain (domain.renameParameters names) (sizes ∘ names) sizes id
    (renameParameters_width domain names sizes).symm
    (fun value => (renameParameters_bits domain names sizes value).symm) value
  simpa only [Option.map_id, id_eq] using equal

/-- Size renaming commutes with the complete optional codec, including padding. -/
@[simp] theorem optional_renameParameters {NewParameter : Type} [Fintype NewParameter]
    (domain : EncodedDomain Parameter) (names : Parameter → NewParameter) :
    (optional domain).renameParameters names = optional (domain.renameParameters names) := by
  refine ext_of_encode_bits ((optional domain).renameParameters names)
    (optional (domain.renameParameters names)) rfl ?_ ?_
  · simp [optional, reindex_widthPolynomial, variant_widthPolynomial, alternatives, Fin.sum_univ_succ]
  · exact optional_renameParameters_bits domain names

end Polytime2.EncodedDomain

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Move size renaming inside an optional codec without changing its value. -/
noncomputable def optionalRename {HostParameter : Type} [Fintype HostParameter]
    (source : EncodedDomain HostParameter) (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((optional source).renameParameters names) (optional (source.renameParameters names))
    (fun _ value => value)

theorem optionalRename_realizable {HostParameter : Type} [Fintype HostParameter]
    (source : EncodedDomain HostParameter) (names : HostParameter → Parameter) :
    (optionalRename source names).Realizable := by
  apply encodingMap_realizable
  · intros; rw [optional_renameParameters]
  · exact optional_renameParameters_bits source names

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

/-- Run a partial computation only when a certified guard permits it. Failed
guards return none without requiring a value in the result domain. -/
noncomputable def optionalGuard {InputName : Type} [Fintype InputName]
    (consumer : Computation Parameter InputName)
    (allowed : ∀ sizes, consumer.Arguments sizes → Prop)
    (guard : ∀ sizes, consumer.Arguments sizes → Bool)
    (permits : ∀ sizes arguments, allowed sizes arguments → guard sizes arguments = true →
      consumer.precondition sizes arguments) : Computation Parameter InputName where
  inputDomains := consumer.inputDomains
  outputDomain := optional consumer.outputDomain
  precondition := allowed
  compute sizes arguments := if selected : guard sizes arguments.val = true then
    some (consumer.compute sizes ⟨arguments.val, permits sizes arguments.val arguments.property selected⟩)
    else none

/-- Guarding, branching, and optional result construction are charged through
ordinary composition. Only the selected branch invokes the consumer. -/
theorem Realizable.optionalGuard {InputName : Type} [Fintype InputName]
    {consumer : Computation Parameter InputName} (ready : consumer.Realizable)
    (allowed : ∀ sizes, consumer.Arguments sizes → Prop)
    (guard : ∀ sizes, consumer.Arguments sizes → Bool)
    (permits : ∀ sizes arguments, allowed sizes arguments → guard sizes arguments = true →
      consumer.precondition sizes arguments)
    (guardReady : (Computation.mk consumer.inputDomains booleans allowed
      (fun sizes arguments => guard sizes arguments.val)).Realizable) :
    (consumer.optionalGuard allowed guard permits).Realizable := by
  have lifted := ready.followedBy (optionalSome_realizable consumer.outputDomain) rfl (by intros; trivial)
  have complete := lifted.guarded (fun _ => none) (optionalNone_realizable consumer.outputDomain)
    allowed guard permits guardReady
  exact complete.withSpecification allowed (consumer.optionalGuard allowed guard permits).compute
    (by intros; assumption) (by intros; rfl)

/-- Test presence without requiring a value in the optional payload domain. -/
noncomputable def optionalIsSome (source : EncodedDomain Parameter) : Computation Parameter Unit :=
  unaryMap (optional source) booleans (fun _ _ => True) (fun _ value => value.val.isSome)

theorem optionalIsSome_realizable (source : EncodedDomain Parameter) :
    (optionalIsSome source).Realizable := by
  have ready := (variantIs_realizable 2 (EncodedDomain.alternatives source) 1).reinterpretInputs
    (fun _ : Unit => optional source) (fun _ sizes => EncodedDomain.optionalEquiv source sizes)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  apply ready.withSpecification (fun _ _ => True) (optionalIsSome source).compute (by intros; trivial)
  intro sizes arguments valid
  change decide (((EncodedDomain.optionalEquiv source sizes) (arguments ())).1 = 1) =
    (arguments ()).isSome
  cases arguments () <;> rfl

/-- Extract an actual optional payload under exactly the presence precondition. -/
noncomputable def optionalGet (source : EncodedDomain Parameter) : Computation Parameter Unit :=
  unaryMap (optional source) source (fun _ value => value.isSome = true)
    (fun _ value => value.val.get value.property)

theorem optionalGet_realizable (source : EncodedDomain Parameter) :
    (optionalGet source).Realizable := by
  have ready := (variantProjection_realizable 2 (EncodedDomain.alternatives source) 1).reinterpretInputs
    (fun _ : Unit => optional source) (fun _ sizes => EncodedDomain.optionalEquiv source sizes)
    (by intros; rfl) (by intros; rfl) (fun _ arguments => (arguments ()).isSome = true) (by
      intro sizes arguments present
      change ((EncodedDomain.optionalEquiv source sizes) (arguments ())).1 = 1
      cases chosen : arguments () with
      | none => simp [chosen] at present
      | some value => rfl)
  apply ready.withSpecification (fun _ arguments => (arguments ()).isSome = true)
    (optionalGet source).compute (by intros; assumption)
  intro sizes arguments present
  cases chosen : arguments () with
  | none => simp [chosen] at present
  | some value =>
    have eta : arguments = fun _ => some value := by
      funext name
      cases name
      exact chosen
    subst arguments
    rfl

/-- Dispatch an optional value into a certified empty branch or a total
consumer. The result may use any canonical codec. -/
noncomputable def optionalElim (source target : EncodedDomain Parameter)
    (empty : ∀ sizes, target.Carrier sizes)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes) : Computation Parameter Unit :=
  unaryMap (optional source) target (fun _ _ => True)
    (fun sizes value => value.val.elim (empty sizes) (operation sizes))

theorem optionalElim_realizable (source target : EncodedDomain Parameter)
    (empty : ∀ sizes, target.Carrier sizes)
    (operation : ∀ sizes, source.Carrier sizes → target.Carrier sizes)
    (emptyReady : (Computation.mk (Empty.elim : Empty → EncodedDomain Parameter) target
      (fun _ _ => True) (fun sizes _ => empty sizes)).Realizable)
    (ready : (unaryMap source target (fun _ _ => True)
      (fun sizes value => operation sizes value.val)).Realizable) :
    (optionalElim source target empty operation).Realizable := by
  let alternatives := EncodedDomain.alternatives source
  let action (index : Fin 2) sizes (value : {value : (alternatives index).Carrier sizes // True}) :
      target.Carrier sizes :=
    Fin.cases (fun _ => empty sizes)
      (fun next => Fin.cases (fun value => operation sizes value.val)
        (fun impossible => Fin.elim0 impossible) next) index value
  have branches (index : Fin 2) :
      (unaryMap (alternatives index) target (fun _ _ => True) (action index)).Realizable := by
    fin_cases index
    · exact emptyReady.onResults (fun _ : Unit => alternatives 0) (fun _ _ => True)
        (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
    · exact ready
  have casesReady := variantCases_realizable 2 alternatives target (fun _ _ _ => True) action branches
  have converted := casesReady.reinterpretInputs (fun _ : Unit => optional source)
    (fun _ sizes => EncodedDomain.optionalEquiv source sizes) (by intros; rfl) (by intros; rfl)
    (fun _ _ => True) (by intros; trivial)
  apply converted.withSpecification (fun _ _ => True) (optionalElim source target empty operation).compute (by intros; trivial)
  intro sizes arguments valid
  cases chosen : arguments () with
  | none =>
    have eta : arguments = fun _ => (none : Option (source.Carrier sizes)) := by
      funext name
      cases name
      exact chosen
    subst arguments
    rfl
  | some value =>
    have eta : arguments = fun _ => some value := by
      funext name
      cases name
      exact chosen
    subst arguments
    rfl

/-- Compose total optional-result decoders, invoking the consumer only when the
source contains an actual value. -/
noncomputable def optionalBind (source target : EncodedDomain Parameter)
    (operation : ∀ sizes, source.Carrier sizes → Option (target.Carrier sizes)) : Computation Parameter Unit :=
  unaryMap (optional source) (optional target) (fun _ _ => True)
    (fun sizes value => value.val.bind (operation sizes))

theorem optionalBind_realizable (source target : EncodedDomain Parameter)
    (operation : ∀ sizes, source.Carrier sizes → Option (target.Carrier sizes))
    (ready : (unaryMap source (optional target) (fun _ _ => True)
      (fun sizes value => operation sizes value.val)).Realizable) :
    (optionalBind source target operation).Realizable := by
  have combined := optionalElim_realizable source (optional target) (fun _ => none) operation
    (optionalNone_realizable target) ready
  apply combined.withSpecification (fun _ _ => True) (optionalBind source target operation).compute
    (by intros; trivial)
  intro sizes arguments valid
  change (arguments ()).elim none (operation sizes) = (arguments ()).bind (operation sizes)
  cases arguments () <;> rfl

end Polytime2.Computation
