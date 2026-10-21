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

import Polytime2.Computation.Layout
import Polytime2.Arrays.RuntimeLookupContract
import Polytime2.Arrays.RuntimeUpdateContract
import Polytime2.Arrays.Transform
import Polytime2.Computation.Constant
import Polytime2.Primitives.FiniteOperations

/-! # Fixed-length array lookup and update with existential implementations -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

namespace Realizable.Internal

/-- False names the binary index and true the immutable mathematical array. -/
noncomputable def arrayLookupWithIndex (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains | false => indexDomain
               | true => element.arrayOfLength length
  outputDomain := element
  precondition sizes arguments := toNat sizes (arguments false) < MvPolynomial.eval sizes length
  compute sizes arguments := arguments.val true ⟨toNat sizes (arguments.val false), arguments.property⟩

/-- Arguments are the index, immutable array, and replacement. The result is a
separate array; the original remains available to subsequent computations. -/
noncomputable def arrayUpdateWithIndex (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains | 0 => indexDomain
               | 1 => element.arrayOfLength length
               | 2 => element
  outputDomain := element.arrayOfLength length
  precondition sizes arguments := toNat sizes (arguments 0) < MvPolynomial.eval sizes length
  compute sizes arguments := Function.update (arguments.val 1)
    ⟨toNat sizes (arguments.val 0), arguments.property⟩ (arguments.val 2)

noncomputable def arrayLookupWithCapacity (element : EncodedDomain.{0, 0} Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  arrayLookupWithIndex element (EncodedDomain.binaryNaturals capacity) (fun _ index => index.val) length

noncomputable def arrayUpdateWithCapacity (element : EncodedDomain.{0, 0} Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  arrayUpdateWithIndex element (EncodedDomain.binaryNaturals capacity) (fun _ index => index.val) length

end Realizable.Internal

/-- A fixed finite binary operation maps an array using one runtime coefficient. -/
noncomputable def arrayMap (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : parameterDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim) :
    Computation Parameter Bool where
  inputDomains | false => parameterDomain.constant | true => elementDomain.constant.arrayOfLength length
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := fun index => operation (arguments.val false) (arguments.val true index)

namespace Realizable.Internal

/-- Ordinary arguments occupy the first slots; the unary width is last.
The result follows the ordinary arguments, with counters left private. -/
private def arrayPlacement {InputName : Type} (arity : ℕ) (enumeration : Fin arity ≃ InputName) :
    PublicTape Parameter (InputName ⊕ Unit) ↪ Parameter ⊕ Fin (arity + 5) :=
  (Function.Embedding.refl Parameter).sumMap ⟨(fun role => match role with
    | .inl (.inl name) => ⟨(enumeration.symm name).val, by have bound := (enumeration.symm name).isLt; omega⟩
    | .inl (.inr _) => ⟨arity + 4, by omega⟩
    | .inr _ => ⟨arity, by omega⟩), by
    let recover (slot : Fin (arity + 5)) : Option ((InputName ⊕ Unit) ⊕ Unit) :=
      if valid : slot.val < arity then some (.inl (.inl (enumeration ⟨slot.val, valid⟩)))
      else if slot.val = arity + 4 then some (.inl (.inr ()))
      else if slot.val = arity then some (.inr ()) else none
    have recovered (role : (InputName ⊕ Unit) ⊕ Unit) : recover
        (match role with
        | .inl (.inl name) => ⟨(enumeration.symm name).val, by have bound := (enumeration.symm name).isLt; omega⟩
        | .inl (.inr _) => ⟨arity + 4, by omega⟩
        | .inr _ => ⟨arity, by omega⟩) = some role := by
      rcases role with (name | marker) | result
      · simp [recover, (enumeration.symm name).isLt]
      · cases marker; simp [recover]
      · cases result; simp [recover]
    intro first second equal
    exact Option.some.inj ((recovered first).symm.trans ((congrArg recover equal).trans (recovered second)))⟩

end Realizable.Internal

open Realizable.Internal in
/-- Lookup using a prepared unary width input. -/
private theorem arrayLookupWithIndex_withUnaryWidth_realizable (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (value_encode : ∀ sizes index, Binary.value (EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index)
    (length : MvPolynomial Parameter ℕ) :
    ((arrayLookupWithIndex element indexDomain toNat length).withUnaryWidth element.widthPolynomial).Realizable := by
  refine ofNamedLayout ((arrayLookupWithIndex element indexDomain toNat length).withUnaryWidth element.widthPolynomial)
    (RuntimeArrayLookup.domainsSized element indexDomain length)
    RuntimeArrayLookup.argumentReadOnly RuntimeArrayLookup.sizeTapes RuntimeArrayLookup.outputTapes
    RuntimeArrayLookup.algorithmSized RuntimeArrayLookup.entry RuntimeArrayLookup.exit _ _
    (RuntimeArrayLookup.contractSized element indexDomain length toNat value_encode) (arrayPlacement 2 finTwoEquiv)
    (by rintro (parameter | (argument | marker) | result) <;> first
      | rfl | (fin_cases argument <;> rfl))
    (by rintro (parameter | (argument | marker) | result) <;> first
      | rfl | (fin_cases argument <;> rfl))
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl (.inl false)), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl (.inl true)), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl (.inr ())), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨within, result⟩ := correct
  exact congrArg (encoded element sizes) result

open Realizable.Internal in
/-- Update overwrites a separate public result array under an in-range hypothesis. -/
private theorem arrayUpdateWithIndex_withUnaryWidth_realizable (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (value_encode : ∀ sizes index, Binary.value (EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index)
    (length : MvPolynomial Parameter ℕ) :
    ((arrayUpdateWithIndex element indexDomain toNat length).withUnaryWidth element.widthPolynomial).Realizable := by
  refine ofNamedLayout ((arrayUpdateWithIndex element indexDomain toNat length).withUnaryWidth element.widthPolynomial)
    (RuntimeArrayUpdate.domainsSized element indexDomain length)
    RuntimeArrayUpdate.argumentReadOnly RuntimeArrayUpdate.sizeTapes RuntimeArrayUpdate.outputTapes
    RuntimeArrayUpdate.algorithmSized RuntimeArrayUpdate.entry RuntimeArrayUpdate.exit _ _
    (RuntimeArrayUpdate.contractSized element indexDomain length toNat value_encode) (arrayPlacement 3 (Equiv.refl (Fin 3)))
    (by rintro (parameter | (argument | marker) | result) <;> first
      | rfl | (fin_cases argument <;> rfl))
    (by rintro (parameter | (argument | marker) | result) <;> first
      | rfl | (fin_cases argument <;> rfl))
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl (.inl 0)), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl (.inl 1)), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl (.inl 2)), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl (.inr ())), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨within, result⟩ := correct
  exact congrArg (encoded (element.arrayOfLength length) sizes) result

/-- Polynomial element widths are computed privately from the size inputs. -/
theorem Realizable.Internal.arrayLookupWithIndex_realizable (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (value_encode : ∀ sizes index, Binary.value (EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index)
    (length : MvPolynomial Parameter ℕ) : (arrayLookupWithIndex element indexDomain toNat length).Realizable :=
  Realizable.withComputedWidth (arrayLookupWithIndex element indexDomain toNat length) element.widthPolynomial
    (arrayLookupWithIndex_withUnaryWidth_realizable element indexDomain toNat value_encode length)

/-- Polynomial-width update preserves its original array and replacement. -/
theorem Realizable.Internal.arrayUpdateWithIndex_realizable (element : EncodedDomain.{0, 0} Parameter) (indexDomain : EncodedDomain.{0, 0} Parameter)
    (toNat : ∀ sizes, indexDomain.Carrier sizes → ℕ)
    (value_encode : ∀ sizes index, Binary.value (EncodedDomain.ArrayEncoding.bits (indexDomain.encode sizes index)) = toNat sizes index)
    (length : MvPolynomial Parameter ℕ) : (arrayUpdateWithIndex element indexDomain toNat length).Realizable :=
  Realizable.withComputedWidth (arrayUpdateWithIndex element indexDomain toNat length) element.widthPolynomial
    (arrayUpdateWithIndex_withUnaryWidth_realizable element indexDomain toNat value_encode length)

/-- Capacity-sensitive access remains available to internal binary controllers. -/
theorem Realizable.Internal.arrayLookupWithCapacity_realizable (element : EncodedDomain.{0, 0} Parameter)
    (capacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayLookupWithCapacity element capacity length).Realizable :=
  arrayLookupWithIndex_realizable element (EncodedDomain.binaryNaturals capacity) (fun _ index => index.val)
    (by intros; exact Binary.value_bits _) length

theorem Realizable.Internal.arrayUpdateWithCapacity_realizable (element : EncodedDomain.{0, 0} Parameter)
    (capacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayUpdateWithCapacity element capacity length).Realizable :=
  arrayUpdateWithIndex_realizable element (EncodedDomain.binaryNaturals capacity) (fun _ index => index.val)
    (by intros; exact Binary.value_bits _) length

/-- Every coordinate is in range by its mathematical type. No index capacity
or admissibility proof is part of the public array interface. -/
noncomputable def arrayLookup (element : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains | false => EncodedDomain.boundedIndex length | true => element.arrayOfLength length
  outputDomain := element
  precondition _ _ := True
  compute _ arguments := arguments.val true (arguments.val false)

noncomputable def arrayUpdate (element : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains | 0 => EncodedDomain.boundedIndex length | 1 => element.arrayOfLength length | 2 => element
  outputDomain := element.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := Function.update (arguments.val 1) (arguments.val 0) (arguments.val 2)

theorem arrayLookup_realizable (element : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayLookup element length).Realizable :=
  (arrayLookupWithIndex_realizable element (EncodedDomain.boundedIndex length) (fun _ index => index.val)
    (EncodedDomain.boundedIndex_value length) length).withSpecification (fun _ _ => True)
    (arrayLookup element length).compute (by intro sizes arguments valid; exact (arguments false).isLt)
    (by intros; rfl)

theorem arrayUpdate_realizable (element : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ) :
    (arrayUpdate element length).Realizable :=
  (arrayUpdateWithIndex_realizable element (EncodedDomain.boundedIndex length) (fun _ index => index.val)
    (EncodedDomain.boundedIndex_value length) length).withSpecification (fun _ _ => True)
    (arrayUpdate element length).compute (by intro sizes arguments valid; exact (arguments 0).isLt)
    (by intros; rfl)

noncomputable section NamedAccess

open EncodedDomain

def arrayLookupAtParameter (element indexDomain : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (index : ∀ sizes, indexDomain.Carrier sizes → Fin (sizes parameter)) :
    Computation Parameter Bool where
  inputDomains | false => indexDomain | true => element.array parameter
  outputDomain := element
  precondition _ _ := True
  compute sizes arguments := arguments.val true (index sizes (arguments.val false))

def arrayUpdateAtParameter (element indexDomain : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (index : ∀ sizes, indexDomain.Carrier sizes → Fin (sizes parameter)) :
    Computation Parameter (Fin 3) where
  inputDomains | 0 => indexDomain | 1 => element.array parameter | 2 => element
  outputDomain := element.array parameter
  precondition _ _ := True
  compute sizes arguments := Function.update (arguments.val 1)
    (index sizes (arguments.val 0)) (arguments.val 2)

theorem arrayLookupAtParameter_realizable (element indexDomain : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (index : ∀ sizes, indexDomain.Carrier sizes → Fin (sizes parameter))
    (value_encode : ∀ sizes value,
      Binary.value (ArrayEncoding.bits (indexDomain.encode sizes value)) = (index sizes value).val) :
    (arrayLookupAtParameter element indexDomain parameter index).Realizable := by
  let computation := arrayLookupAtParameter element indexDomain parameter index
  let inputMap (name : Bool) sizes : (computation.inputDomains name).Carrier sizes →
      ((arrayLookupWithIndex element indexDomain (fun sizes value => (index sizes value).val)
        (MvPolynomial.X parameter)).inputDomains name).Carrier sizes :=
    match name with | false => id | true => arrayParameterEquiv element parameter sizes
  exact (arrayLookupWithIndex_realizable element indexDomain
    (fun sizes value => (index sizes value).val) value_encode (MvPolynomial.X parameter)).reinterpretInputs
    computation.inputDomains inputMap (by intro name sizes; cases name <;> rfl)
    (by intro name sizes value; cases name; rfl
        exact array_X_encode_bits element parameter sizes value)
    (fun _ _ => True) (by
      intro sizes arguments valid
      change (index sizes (arguments false)).val < MvPolynomial.eval sizes (MvPolynomial.X parameter)
      simpa only [MvPolynomial.eval_X] using (index sizes (arguments false)).isLt)

theorem arrayUpdateAtParameter_realizable (element indexDomain : EncodedDomain.{0, 0} Parameter)
    (parameter : Parameter) (index : ∀ sizes, indexDomain.Carrier sizes → Fin (sizes parameter))
    (value_encode : ∀ sizes value,
      Binary.value (ArrayEncoding.bits (indexDomain.encode sizes value)) = (index sizes value).val) :
    (arrayUpdateAtParameter element indexDomain parameter index).Realizable := by
  let computation := arrayUpdateAtParameter element indexDomain parameter index
  let inputMap (name : Fin 3) sizes : (computation.inputDomains name).Carrier sizes →
      ((arrayUpdateWithIndex element indexDomain (fun sizes value => (index sizes value).val)
        (MvPolynomial.X parameter)).inputDomains name).Carrier sizes :=
    match name with | 0 => id | 1 => arrayParameterEquiv element parameter sizes | 2 => id
  have prepared := (arrayUpdateWithIndex_realizable element indexDomain
    (fun sizes value => (index sizes value).val) value_encode (MvPolynomial.X parameter)).reinterpretInputs
    computation.inputDomains inputMap (by intro name sizes; fin_cases name <;> rfl)
    (by intro name sizes value; fin_cases name
        rfl
        exact array_X_encode_bits element parameter sizes value
        rfl)
    computation.precondition (by
      intro sizes arguments valid
      change (index sizes (arguments 0)).val < MvPolynomial.eval sizes (MvPolynomial.X parameter)
      simpa only [MvPolynomial.eval_X] using (index sizes (arguments 0)).isLt)
  have transported := prepared.reinterpretOutput computation.outputDomain
    (fun sizes => (arrayParameterEquiv element parameter sizes).symm)
    (arrayParameter_width element parameter)
    (fun sizes value => array_X_encode_bits element parameter sizes _)
  apply transported.withSpecification computation.precondition computation.compute
    (by intros; trivial)
  intro sizes arguments valid
  apply (arrayParameterEquiv element parameter sizes).injective
  change (arrayParameterEquiv element parameter sizes)
      ((arrayParameterEquiv element parameter sizes).symm _) = _
  rw [Equiv.apply_symm_apply]
  symm
  have updateTransport (values : Fin (sizes parameter) → element.Carrier sizes)
      (selected : Fin (sizes parameter)) (replacement : element.Carrier sizes) :
      arrayParameterEquiv element parameter sizes (Function.update values selected replacement) =
        Function.update (arrayParameterEquiv element parameter sizes values)
          ⟨selected.val, by simpa only [MvPolynomial.eval_X] using selected.isLt⟩ replacement := by
    funext position
    change Function.update values selected replacement
      (Fin.cast (MvPolynomial.eval_X (f := sizes) parameter) position) =
        Function.update
          (fun position => values (Fin.cast (MvPolynomial.eval_X (f := sizes) parameter) position))
          ⟨selected.val, _⟩ replacement position
    simp only [Function.update_apply, Fin.ext_iff, Fin.val_cast]
  exact updateTransport (arguments 1) (index sizes (arguments 0)) (arguments 2)

end NamedAccess

theorem arrayMap_realizable (parameterDomain elementDomain : EncodedDomain.{0, 0} Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : parameterDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim) :
    (arrayMap parameterDomain elementDomain length operation).Realizable := by
  let context : Unit → EncodedDomain.{0, 0} Parameter := fun _ => parameterDomain.constant
  let element : EncodedDomain.{0, 0} Parameter := elementDomain.constant
  let update := fun sizes (values : ∀ name, (context name).Carrier sizes) (value : element.Carrier sizes) =>
    operation (values ()) value
  have step := ((finiteTable_realizable parameterDomain elementDomain elementDomain operation).withConstantSizes
    (Parameter := Parameter)).withArguments (arrayTransformStep context element element update).inputDomains
      ⟨(fun choice => if choice then (Sum.inr () : Unit ⊕ Unit) else .inl ()), by
        intro first second equal; cases first <;> cases second <;> simp_all⟩
      (by intro choice; cases choice <;> rfl)
  have mapped := arrayTransform_realizable context element element length update step
  exact mapped.withArguments (arrayMap parameterDomain elementDomain length operation).inputDomains
    ⟨(fun name => match name with | .inl _ => false | .inr _ => true), by
      rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) equal <;> first | rfl | cases equal⟩
    (by rintro (name | name); cases name; rfl; cases name; rfl)

end Polytime2.Computation
