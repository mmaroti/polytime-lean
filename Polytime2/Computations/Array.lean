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
import Polytime2.StandardArrayLookupSizedContract
import Polytime2.StandardArrayUpdate
import Polytime2.StandardArrayMapContract

/-! # Fixed-length array lookup and update with existential implementations -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

variable {Parameter : Type} [Fintype Parameter]

/-- False names the binary index and true the immutable mathematical array. -/
noncomputable def arrayLookup (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Bool where
  inputDomains | false => EncodedDomain.binaryNaturals indexCapacity
               | true => element.arrayOfLength length
  outputDomain := element
  precondition sizes arguments := (arguments false).val < MvPolynomial.eval sizes length
  compute _ arguments := arguments.val true ⟨(arguments.val false).val, arguments.property⟩

/-- Arguments are the index, immutable array, and replacement. The result is a
separate array; the original remains available to subsequent computations. -/
noncomputable def arrayUpdate (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) where
  inputDomains | 0 => EncodedDomain.binaryNaturals indexCapacity
               | 1 => element.arrayOfLength length
               | 2 => element
  outputDomain := element.arrayOfLength length
  precondition sizes arguments := (arguments 0).val < MvPolynomial.eval sizes length
  compute _ arguments := Function.update (arguments.val 1)
    ⟨(arguments.val 0).val, arguments.property⟩ (arguments.val 2)

/-- A fixed finite binary operation maps an array using one runtime coefficient. -/
noncomputable def arrayMap (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    Computation Parameter Bool where
  inputDomains | false => parameterDomain.constant | true => elementDomain.constant.arrayOfLength length
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := fun index => operation Empty.elim (arguments.val false) (arguments.val true index)

namespace Realizable.Internal

/-- A static partition: arguments, one result, then three private tapes. -/
private def arrayLayout {InputName : Type} (arity : ℕ) (enumeration : Fin arity ≃ InputName) :
    Parameter ⊕ Fin (arity + 4) ≃ Parameter ⊕ (InputName ⊕ (Unit ⊕ Fin 3)) :=
  Equiv.sumCongr (Equiv.refl Parameter)
    (finSumFinEquiv.symm.trans (Equiv.sumCongr enumeration
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.ofUnique (Fin 1) Unit) (Equiv.refl (Fin 3))))))

private noncomputable def arrayScratch (capacity : Parameter) (name : Fin 3) : EncodedDomain Parameter :=
  if name = 2 then EncodedDomain.booleans else EncodedDomain.binaryNaturals capacity

private theorem lookupDomains (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (name : Parameter ⊕ Fin 6) :
    domains (arrayLookup element capacity length) (arrayScratch capacity)
      (arrayLayout 2 finTwoEquiv name) = StandardArrayLookupSized.domainsSized element capacity length name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private theorem updateDomains (element : EncodedDomain Parameter) (capacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (name : Parameter ⊕ Fin 7) :
    domains (arrayUpdate element capacity length) (arrayScratch capacity)
      (arrayLayout 3 (Equiv.refl (Fin 3)) name) = StandardArrayUpdate.domainsSized element capacity length name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def mapLayout : Parameter ⊕ Fin 3 ≃ Parameter ⊕ (Bool ⊕ (Unit ⊕ Empty)) where
  toFun | .inl parameter => .inl parameter
        | .inr 0 => .inr (.inl false)
        | .inr 1 => .inr (.inl true)
        | .inr 2 => .inr (.inr (.inl ()))
  invFun | .inl parameter => .inl parameter
         | .inr (.inl false) => .inr 0
         | .inr (.inl true) => .inr 1
         | .inr (.inr (.inl _)) => .inr 2
         | .inr (.inr (.inr empty)) => nomatch empty
  left_inv name := by cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | empty
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · exact Empty.elim empty

end Realizable.Internal

open Realizable.Internal in
/-- Element width is fixed by specialization; length is polynomial in the
runtime sizes. No scratch or controller names occur in the public certificate. -/
theorem arrayLookup_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (elementWidth : ℕ)
    (fixedWidth : ∀ sizes, element.width sizes = elementWidth) :
    (arrayLookup element indexCapacity length).Realizable := by
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes)
    (lookupDomains element indexCapacity length name))
  have readonly name : StandardArrayLookupSized.argumentReadOnly name =
      readOnly (arrayLookup element indexCapacity length) (arrayLayout 2 finTwoEquiv name) := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  refine ofLayout (arrayLookup element indexCapacity length) (arrayScratch indexCapacity)
    (StandardArrayLookupSized.domainsSized element indexCapacity length)
    StandardArrayLookupSized.argumentReadOnly StandardArrayLookupSized.sizeTapes StandardArrayLookupSized.outputTapes
    (StandardArrayLookupSized.algorithmSized elementWidth) (StandardArrayLookup.entry elementWidth)
    (StandardArrayLookup.exit elementWidth) _ _
    (StandardArrayLookupSized.contractSized element elementWidth indexCapacity length fixedWidth)
    (arrayLayout 2 finTwoEquiv).toEmbedding values ?_ ?_ readonly (by intro parameter; rfl)
    () rfl (by intro sizes input valid; exact valid) ?_
  · intro name sizes
    exact congrArg (fun domain => domain.width sizes) (lookupDomains element indexCapacity length name)
  · intro name sizes value
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  · intro sizes input valid output correct
    obtain ⟨within, result⟩ := correct
    exact congrArg (encoded element sizes) result

open Realizable.Internal in
/-- Update overwrites a separate public result array under an in-range hypothesis. -/
theorem arrayUpdate_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) (elementWidth : ℕ)
    (fixedWidth : ∀ sizes, element.width sizes = elementWidth) :
    (arrayUpdate element indexCapacity length).Realizable := by
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes)
    (updateDomains element indexCapacity length name))
  have readonly name : StandardArrayUpdate.argumentReadOnlySized name =
      readOnly (arrayUpdate element indexCapacity length) (arrayLayout 3 (Equiv.refl (Fin 3)) name) := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  refine ofLayout (arrayUpdate element indexCapacity length) (arrayScratch indexCapacity)
    (StandardArrayUpdate.domainsSized element indexCapacity length)
    StandardArrayUpdate.argumentReadOnlySized StandardArrayUpdate.sizeTapesSized StandardArrayUpdate.outputTapesSized
    (StandardArrayUpdate.algorithmSized elementWidth) (StandardArrayUpdate.entry elementWidth)
    (StandardArrayUpdate.exit elementWidth) _ _
    (StandardArrayUpdate.contractSized element elementWidth indexCapacity length fixedWidth)
    (arrayLayout 3 (Equiv.refl (Fin 3))).toEmbedding values ?_ ?_ readonly (by intro parameter; rfl)
    () rfl (by intro sizes input valid; exact valid) ?_
  · intro name sizes
    exact congrArg (fun domain => domain.width sizes) (updateDomains element indexCapacity length name)
  · intro name sizes value
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  · intro sizes input valid output correct
    obtain ⟨within, result⟩ := correct
    exact congrArg (encoded (element.arrayOfLength length) sizes) result

open Realizable.Internal in
theorem arrayMap_realizable (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    (arrayMap parameterDomain elementDomain length operation).Realizable := by
  let computation := arrayMap parameterDomain elementDomain length operation
  let scratchDomains : Empty → EncodedDomain Parameter := Empty.elim
  have domainsEqual name : domains computation scratchDomains (mapLayout name) =
      StandardArrayMap.domains parameterDomain elementDomain length name := by
    cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (domainsEqual name))
  refine ofLayout computation scratchDomains (StandardArrayMap.domains parameterDomain elementDomain length)
    StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
    (StandardArrayMap.algorithm parameterDomain elementDomain operation) StandardArrayMap.entry StandardArrayMap.exit
    _ _ (StandardArrayMap.contract parameterDomain elementDomain length operation) mapLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (domainsEqual name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded (elementDomain.constant.arrayOfLength length) sizes) correct

end Polytime2.Computation
