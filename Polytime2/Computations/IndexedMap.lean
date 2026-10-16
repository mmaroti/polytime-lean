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
import Polytime2.IndexedMapContract
import Polytime2.CatalogueMapContract

/-! # Indexed finite operations through mathematical certificates -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

variable {Parameter : Type} [Fintype Parameter]

noncomputable section IndexedComputations

/-- Arguments are the index, immutable array, and finite scalar parameter. -/
def indexedMap (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes →
      elementDomain.Carrier sizes) : Computation Parameter (Fin 3) where
  inputDomains
    | 0 => EncodedDomain.binaryNaturals indexCapacity
    | 1 => elementDomain.constant.arrayOfLength length
    | 2 => parameterDomain.constant
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition sizes arguments := (arguments 0).val < MvPolynomial.eval sizes length
  compute _ arguments := Function.update (arguments.val 1)
    ⟨(arguments.val 0).val, arguments.property⟩
    (operation Empty.elim (arguments.val 2)
      (arguments.val 1 ⟨(arguments.val 0).val, arguments.property⟩))

/-- Two fixed maps act sequentially on selected coordinates in an active prefix.
Arguments are the first index, second index, active count, and immutable array.
Coincident indices apply the second map to the first map's result. -/
def catalogueMaps (elementDomain : EncodedDomain Empty) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (first second : ∀ sizes, elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    Computation Parameter (Fin 4) where
  inputDomains
    | 0 | 1 | 2 => EncodedDomain.binaryNaturals indexCapacity
    | 3 => elementDomain.constant.arrayOfLength length
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition sizes arguments := (arguments 2).val ≤ MvPolynomial.eval sizes length ∧
    (arguments 0).val < (arguments 2).val ∧ (arguments 1).val < (arguments 2).val
  compute _ arguments := CatalogueMap.compute (first Empty.elim) (second Empty.elim)
    (arguments.val 3)
    ⟨(arguments.val 0).val, lt_of_lt_of_le arguments.property.2.1 arguments.property.1⟩
    ⟨(arguments.val 1).val, lt_of_lt_of_le arguments.property.2.2 arguments.property.1⟩

namespace Realizable.Internal

private def indexedMapLayout (name : Parameter ⊕ Fin 12) :
    Parameter ⊕ (Fin 3 ⊕ (Unit ⊕ Fin 12)) :=
  match name with
  | .inl parameter => .inl parameter
  | .inr 0 => .inr (.inl 0)
  | .inr 1 => .inr (.inl 1)
  | .inr 2 => .inr (.inl 2)
  | .inr 3 => .inr (.inr (.inl ()))
  | .inr privateTape => .inr (.inr (.inr privateTape))

private def indexedMapSource : Parameter ⊕ (Fin 3 ⊕ (Unit ⊕ Fin 12)) → Parameter ⊕ Fin 12
  | .inl parameter => .inl parameter
  | .inr (.inl 0) => .inr 0
  | .inr (.inl 1) => .inr 1
  | .inr (.inl 2) => .inr 2
  | .inr (.inr (.inl _)) => .inr 3
  | .inr (.inr (.inr name)) => .inr name

omit [Fintype Parameter] in
private theorem indexedMapLayout_leftInverse : Function.LeftInverse
    (indexedMapSource (Parameter := Parameter)) indexedMapLayout := by
  intro name
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def indexedMapEmbedding : Parameter ⊕ Fin 12 ↪ Parameter ⊕ (Fin 3 ⊕ (Unit ⊕ Fin 12)) :=
  ⟨indexedMapLayout, indexedMapLayout_leftInverse.injective⟩

private def catalogueMapsLayout (name : Parameter ⊕ Fin 15) :
    Parameter ⊕ (Fin 4 ⊕ (Unit ⊕ Fin 15)) :=
  match name with
  | .inl parameter => .inl parameter
  | .inr 0 => .inr (.inl 0)
  | .inr 1 => .inr (.inl 1)
  | .inr 2 => .inr (.inl 2)
  | .inr 3 => .inr (.inl 3)
  | .inr 5 => .inr (.inr (.inl ()))
  | .inr privateTape => .inr (.inr (.inr privateTape))

private def catalogueMapsSource : Parameter ⊕ (Fin 4 ⊕ (Unit ⊕ Fin 15)) → Parameter ⊕ Fin 15
  | .inl parameter => .inl parameter
  | .inr (.inl 0) => .inr 0
  | .inr (.inl 1) => .inr 1
  | .inr (.inl 2) => .inr 2
  | .inr (.inl 3) => .inr 3
  | .inr (.inr (.inl _)) => .inr 5
  | .inr (.inr (.inr name)) => .inr name

omit [Fintype Parameter] in
private theorem catalogueMapsLayout_leftInverse : Function.LeftInverse
    (catalogueMapsSource (Parameter := Parameter)) catalogueMapsLayout := by
  intro name
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def catalogueMapsEmbedding : Parameter ⊕ Fin 15 ↪ Parameter ⊕ (Fin 4 ⊕ (Unit ⊕ Fin 15)) :=
  ⟨catalogueMapsLayout, catalogueMapsLayout_leftInverse.injective⟩

private theorem indexedMapDomains (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes →
      elementDomain.Carrier sizes)
    (name : Parameter ⊕ Fin 12) :
    domains (indexedMap parameterDomain elementDomain indexCapacity length operation)
      (fun privateTape => IndexedMap.domains parameterDomain elementDomain indexCapacity length (.inr privateTape))
      (indexedMapEmbedding name) = IndexedMap.domains parameterDomain elementDomain indexCapacity length name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private theorem catalogueMapsDomains (elementDomain : EncodedDomain Empty) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (first second : ∀ sizes, elementDomain.Carrier sizes → elementDomain.Carrier sizes)
    (name : Parameter ⊕ Fin 15) :
    domains (catalogueMaps elementDomain indexCapacity length first second)
      (fun privateTape => CatalogueMap.domains elementDomain indexCapacity length (.inr privateTape))
      (catalogueMapsEmbedding name) = CatalogueMap.domains elementDomain indexCapacity length name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

end Realizable.Internal

open Realizable.Internal in
theorem indexedMap_realizable (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes →
      elementDomain.Carrier sizes) :
    (indexedMap parameterDomain elementDomain indexCapacity length operation).Realizable := by
  let computation := indexedMap parameterDomain elementDomain indexCapacity length operation
  let scratchDomains := fun privateTape => IndexedMap.domains parameterDomain elementDomain indexCapacity length (.inr privateTape)
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (indexedMapDomains parameterDomain elementDomain indexCapacity length operation name))
  refine ofLayout computation scratchDomains (IndexedMap.domains parameterDomain elementDomain indexCapacity length)
    IndexedMap.argumentReadOnly IndexedMap.sizeTapes IndexedMap.outputTapes
    (IndexedMap.algorithm parameterDomain elementDomain operation)
    (IndexedMap.entry (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) (IndexedMap.exit (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim)) _ _
    (IndexedMap.contract parameterDomain elementDomain indexCapacity length operation) indexedMapEmbedding values
    (by
      intro name sizes
      exact congrArg (fun domain => domain.width sizes) (indexedMapDomains parameterDomain elementDomain indexCapacity length operation name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨within, result⟩ := correct
  exact congrArg (encoded (elementDomain.constant.arrayOfLength length) sizes) result

open Realizable.Internal in
theorem catalogueMaps_realizable (elementDomain : EncodedDomain Empty) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (first second : ∀ sizes, elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    (catalogueMaps elementDomain indexCapacity length first second).Realizable := by
  let computation := catalogueMaps elementDomain indexCapacity length first second
  let scratchDomains := fun privateTape => CatalogueMap.domains elementDomain indexCapacity length (.inr privateTape)
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (catalogueMapsDomains elementDomain indexCapacity length first second name))
  refine ofLayout computation scratchDomains (CatalogueMap.domains elementDomain indexCapacity length)
    CatalogueMap.argumentReadOnly CatalogueMap.sizeTapes CatalogueMap.outputTapes
    (CatalogueMap.algorithm elementDomain first second)
    (CatalogueMap.entry (elementDomain.width Empty.elim)) (CatalogueMap.exit (elementDomain.width Empty.elim)) _ _
    (CatalogueMap.contract elementDomain indexCapacity length first second) catalogueMapsEmbedding values
    (by
      intro name sizes
      exact congrArg (fun domain => domain.width sizes) (catalogueMapsDomains elementDomain indexCapacity length first second name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  obtain ⟨firstWithin, secondWithin, result⟩ := correct
  exact congrArg (encoded (elementDomain.constant.arrayOfLength length) sizes) result

end IndexedComputations
end Polytime2.Computation
