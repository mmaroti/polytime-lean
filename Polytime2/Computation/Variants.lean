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

import Polytime2.Computation.Records
import Polytime2.Primitives.BitOperations
import Polytime2.Primitives.ConstantOperations
import Polytime2.Computation.Constant
import Polytime2.Primitives.FiniteOperations
import Polytime2.Computation.Branch

/-! # Certified injection, discrimination, projection, and variant case analysis -/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def variantTag (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter) :
    Computation Parameter Unit :=
  unaryMap (variant count alternatives) (fixed (Equiv.refl (Fin count))) (fun _ _ => True)
    (fun _ value => value.val.1)

theorem variantTag_realizable (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter) :
    (variantTag count alternatives).Realizable := by
  apply Realizable.Internal.fieldProjection _ _ 0
  intro sizes value
  refine ⟨[], (List.ofFn (fun index => ArrayEncoding.bits
    (VariantEncoding.fields count alternatives sizes value.val index))).flatten, ?_, by simp⟩
  simpa only [List.nil_append] using bits_variant_encode count alternatives sizes value.val

/-- Projection is defined when the discriminator selects this alternative. -/
noncomputable def variantProjection (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : Computation Parameter Unit :=
  unaryMap (variant count alternatives) (alternatives index) (fun _ value => value.1 = index)
    (fun _ value => value.property ▸ value.val.2)

theorem variantProjection_realizable (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : (variantProjection count alternatives index).Realizable := by
  let fields := fun index => bitVectors (alternatives index).widthPolynomial
  apply Realizable.Internal.fieldProjection _ _
    (MvPolynomial.C (Nat.clog 2 count) + recordOffset count fields index)
  intro sizes value
  rcases value with ⟨⟨tag, payload⟩, equal⟩
  dsimp at equal
  subst tag
  obtain ⟨before, after, decomposition, length⟩ :=
    split_record_encode count fields sizes (VariantEncoding.fields count alternatives sizes ⟨index, payload⟩) index
  rw [bits_record_encode] at decomposition
  have selected : VariantEncoding.fields count alternatives sizes ⟨index, payload⟩ index =
      (alternatives index).encode sizes payload := by simp [VariantEncoding.fields]
  refine ⟨ArrayEncoding.bits ((fixed (Parameter := Parameter) (Equiv.refl (Fin count))).encode sizes index) ++ before,
    after, ?_, ?_⟩
  · change ArrayEncoding.bits ((variant count alternatives).encode sizes ⟨index, payload⟩) = _
    rw [bits_variant_encode, decomposition]
    simp only [List.append_assoc, fields, bitVectors, selected]
  · simp only [List.length_append, List.length_ofFn, length, map_add, MvPolynomial.eval_C]
    simp [fixed, ofCodec]

/-- Injection takes only the selected value; inactive fields are zero-filled. -/
noncomputable def variantInjection (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : Computation Parameter Unit :=
  unaryMap (alternatives index) (variant count alternatives) (fun _ _ => True)
    (fun _ value => ⟨index, value.val⟩)

theorem variantInjection_realizable (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : (variantInjection count alternatives index).Realizable := by
  classical
  let inputs := fun _ : Unit => alternatives index
  let fields := fun name => bitVectors (alternatives name).widthPolynomial
  let values := fun name sizes (arguments : {arguments : (name : Unit) → (inputs name).Carrier sizes // True}) =>
    if equal : name = index then (alternatives name).encode sizes (equal.symm ▸ arguments.val ()) else 0
  have fieldsRealizable : ∀ name, (Computation.mk inputs (fields name) (fun _ _ => True) (values name)).Realizable := by
    intro name
    by_cases equal : name = index
    · subst name
      simpa [inputs, fields, values, encodingMap, unaryMap] using encode_realizable (alternatives index)
    · have zero := (zeroBits_realizable (alternatives name).widthPolynomial).withArguments inputs
        ⟨Empty.elim, by intro name; cases name⟩ (by intro name; cases name)
      exact zero.withSpecification (fun _ _ => True) (values name) (by intros; trivial)
        (by
          intro sizes arguments valid
          simp only [values, equal, zeroBits, withArguments]
          rfl)
  have collected := Realizable.recordOutputs inputs count fields (fun _ _ => True) values fieldsRealizable
  let tag : EncodedDomain Parameter := fixed (Equiv.refl (Fin count))
  have fixedTag := (constant_realizable (fixed (Parameter := Empty) (Equiv.refl (Fin count))) (fun _ => index)).withConstantSizes
    (Parameter := Parameter)
  have tagContext := fixedTag.withArguments inputs ⟨Empty.elim, by intro name; cases name⟩ (by intro name; cases name)
  have tagRealizable : (Computation.mk inputs tag (fun _ _ => True) (fun _ _ => index)).Realizable := by
    refine tagContext.reinterpretOutput tag (fun _ value => value) ?_ ?_
    · intro sizes; simp [tag, EncodedDomain.constant, fixed, ofCodec, width, Computation.withConstantSizes, withArguments, Computation.constant]
    · intro sizes value
      simp [tag, EncodedDomain.constant, fixed, ofCodec, Computation.withConstantSizes,
        withArguments, Computation.constant, ArrayEncoding.bits_cast]
  have packed := Realizable.pairOutputs inputs tag (record count fields) (fun _ _ => True)
    (fun _ _ => index) (fun sizes arguments name => values name sizes arguments) tagRealizable collected
  exact packed.withEncodedOutput (variant count alternatives) (fun _ arguments => ⟨index, arguments.val ()⟩)
    (fun _ => rfl) (fun _ _ => rfl)

/-- A discriminator test has no precondition on the selected alternative. -/
noncomputable def variantIs (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : Computation Parameter Unit :=
  unaryMap (variant count alternatives) EncodedDomain.booleans (fun _ _ => True)
    (fun _ value => decide (value.val.1 = index))

theorem variantIs_realizable (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (index : Fin count) : (variantIs count alternatives index).Realizable := by
  classical
  let tag : EncodedDomain Empty := fixed (Equiv.refl (Fin count))
  have extracted := (variantTag_realizable count alternatives).reinterpretOutput (EncodedDomain.constant tag)
    (fun _ value => value)
    (by intro sizes; simp [tag, EncodedDomain.constant, variantTag, fixed, ofCodec, width, unaryMap])
    (by intro sizes value; simp [tag, EncodedDomain.constant, variantTag, fixed, ofCodec,
      unaryMap, ArrayEncoding.bits_cast])
  have predicate := (finitePredicate_realizable tag (fun (value : Fin count) => decide (value = index))).withConstantSizes
    (Parameter := Parameter)
  have composed := extracted.followedBy predicate rfl (by intros; trivial)
  refine composed.reinterpretOutput EncodedDomain.booleans (fun _ value => value) ?_ ?_
  · intro sizes
    simp [EncodedDomain.constant, finitePredicate, finiteOperation, withConstantSizes, followedBy,
      EncodedDomain.booleans, fixed, ofCodec, width]
  · intro sizes value
    simp [EncodedDomain.constant, finitePredicate, finiteOperation, withConstantSizes, followedBy,
      variantTag, unaryMap, EncodedDomain.booleans, fixed, ofCodec, ArrayEncoding.bits_cast]

/-- Case analysis calls only the selected alternative's certified algorithm. -/
noncomputable def variantCases (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (output : EncodedDomain.{0, 0} Parameter)
    (preconditions : ∀ index sizes, (alternatives index).Carrier sizes → Prop)
    (branches : ∀ index sizes, {value // preconditions index sizes value} → output.Carrier sizes) :
    Computation Parameter Unit where
  inputDomains _ := variant count alternatives
  outputDomain := output
  precondition sizes arguments := preconditions (arguments ()).1 sizes (arguments ()).2
  compute sizes arguments := branches (arguments.val ()).1 sizes ⟨(arguments.val ()).2, arguments.property⟩

theorem variantCases_realizable (count : ℕ) (alternatives : Fin count → EncodedDomain.{0, 0} Parameter)
    (output : EncodedDomain.{0, 0} Parameter)
    (preconditions : ∀ index sizes, (alternatives index).Carrier sizes → Prop)
    (branches : ∀ index sizes, {value // preconditions index sizes value} → output.Carrier sizes)
    (realizable : ∀ index, (unaryMap (alternatives index) output (preconditions index) (branches index)).Realizable) :
    (variantCases count alternatives output preconditions branches).Realizable := by
  classical
  let computation := variantCases count alternatives output preconditions branches
  have restricted : ∀ limit, limit ≤ count →
      (computation.withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ (arguments ()).1.val < limit)
        (fun _ _ valid => valid.1)).Realizable := by
    intro limit
    induction limit with
    | zero =>
      intro bound
      apply Realizable.ofFalsePrecondition
      intro sizes arguments valid
      exact Nat.not_lt_zero _ valid.2
    | succ limit hypothesis =>
      intro bound
      let index : Fin count := ⟨limit, by omega⟩
      let current := computation.withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ (arguments ()).1.val < limit + 1)
        (fun _ _ valid => valid.1)
      let test := fun sizes (arguments : current.Arguments sizes) => decide ((arguments ()).1 = index)
      apply Realizable.byCases current test
      · exact (variantIs_realizable count alternatives index).withPrecondition current.precondition (by intros; trivial)
      · let selected := current.withPrecondition
          (fun sizes arguments => current.precondition sizes arguments ∧ test sizes arguments = true)
          (fun _ _ valid => valid.1)
        let projection := (variantProjection count alternatives index).withPrecondition selected.precondition
          (by
            intro sizes arguments valid
            have equal : (arguments ()).1 = index := of_decide_eq_true valid.2
            exact equal)
        have projected := (variantProjection_realizable count alternatives index).withPrecondition selected.precondition
          (by
            intro sizes arguments valid
            have equal : (arguments ()).1 = index := of_decide_eq_true valid.2
            exact equal)
        have compatible : ∀ sizes (arguments : projection.Arguments sizes)
            (valid : projection.precondition sizes arguments),
            (unaryMap (alternatives index) output (preconditions index) (branches index)).precondition sizes
              (fun _ => projection.compute sizes ⟨arguments, valid⟩) := by
          intro sizes arguments valid
          have equal : (arguments ()).1 = index := of_decide_eq_true valid.2
          cases value : arguments () with
          | mk tag payload =>
            have tagEqual : tag = index := by simpa only [value] using equal
            subst tag
            have argumentsEq : arguments = fun _ => Sigma.mk index payload := by
              funext name; cases name; exact value
            subst arguments
            exact valid.1.1
        have composed := projected.followedBy (realizable index) rfl compatible
        exact composed.withSpecification selected.precondition selected.compute (by intros; assumption) (by
          intro sizes arguments valid
          have equal : (arguments ()).1 = index := of_decide_eq_true valid.2
          cases value : arguments () with
          | mk tag payload =>
            have tagEqual : tag = index := by simpa only [value] using equal
            subst tag
            have argumentsEq : arguments = fun _ => Sigma.mk index payload := by
              funext name; cases name; exact value
            subst arguments
            rfl)
      · let selected := current.withPrecondition
          (fun sizes arguments => current.precondition sizes arguments ∧ test sizes arguments = false)
          (fun _ _ valid => valid.1)
        have previous := (hypothesis (by omega)).withPrecondition selected.precondition (by
          intro sizes arguments valid
          refine ⟨valid.1.1, ?_⟩
          have different : (arguments ()).1 ≠ index := of_decide_eq_false valid.2
          have bound := valid.1.2
          have notEqual : (arguments ()).1.val ≠ limit := by
            intro equal
            exact different (Fin.ext equal)
          omega)
        exact previous.withSpecification selected.precondition selected.compute (by intros; assumption) (by intros; rfl)
  exact (restricted count le_rfl).withSpecification computation.precondition computation.compute
    (by intro sizes arguments valid; exact ⟨valid, (arguments ()).1.isLt⟩) (by intros; rfl)

end Polytime2.Computation
