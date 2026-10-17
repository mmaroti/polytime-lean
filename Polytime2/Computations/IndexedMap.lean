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

import Polytime2.Computation.Composition
import Polytime2.Computation.Constant
import Polytime2.Computations.Array
import Polytime2.Computations.FiniteTable
import Polytime2.Computations.Constant

/-! # Indexed finite operations through mathematical certificates -/

namespace Polytime2.Computation

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
  compute _ arguments :=
    let firstIndex := ⟨(arguments.val 0).val, lt_of_lt_of_le arguments.property.2.1 arguments.property.1⟩
    let secondIndex := ⟨(arguments.val 1).val, lt_of_lt_of_le arguments.property.2.2 arguments.property.1⟩
    let middle := Function.update (arguments.val 3) firstIndex (first Empty.elim (arguments.val 3 firstIndex))
    Function.update middle secondIndex (second Empty.elim (middle secondIndex))

theorem indexedMap_realizable (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes →
      elementDomain.Carrier sizes) :
    (indexedMap parameterDomain elementDomain indexCapacity length operation).Realizable := by
  let computation := indexedMap parameterDomain elementDomain indexCapacity length operation
  let lookupSelection : Bool ↪ Fin 3 :=
    ⟨(fun flag => if flag then 1 else 0), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let lookup := (arrayLookup elementDomain.constant indexCapacity length).withArguments
    computation.inputDomains lookupSelection (by intro flag; cases flag <;> rfl)
  let context : Fin 3 ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim computation.inputDomains (fun _ => elementDomain.constant)
  let tableSelection : Bool ↪ Fin 3 ⊕ Unit :=
    ⟨(fun flag => if flag then .inr () else .inl 2), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let table := (((finiteTable parameterDomain elementDomain elementDomain operation).withConstantSizes).withArguments
    context tableSelection (by intro flag; cases flag <;> rfl)).withPrecondition
      (fun sizes arguments => (arguments (.inl 0)).val < MvPolynomial.eval sizes length)
      (by intro sizes arguments valid; trivial)
  let updateContext : (Fin 3 ⊕ Unit) ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim context (fun _ => elementDomain.constant)
  let updateSelection : Fin 3 ↪ (Fin 3 ⊕ Unit) ⊕ Unit :=
    ⟨(fun | 0 => .inl (.inl 0) | 1 => .inl (.inl 1) | 2 => .inr ()), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
  let update := (arrayUpdate elementDomain.constant indexCapacity length).withArguments
    updateContext updateSelection (by intro name; fin_cases name <;> rfl)
  have lookupRealizable : lookup.Realizable :=
    (arrayLookup_realizable elementDomain.constant indexCapacity length).withArguments _ _ _
  have tableRealizable : table.Realizable :=
    (((finiteTable_realizable parameterDomain elementDomain elementDomain operation).withConstantSizes).withArguments _ _ _).withPrecondition _ _
  have updateRealizable : update.Realizable :=
    (arrayUpdate_realizable elementDomain.constant indexCapacity length).withArguments _ _ _
  let continuation := table.letThen update (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact valid)
  have continuationRealizable : continuation.Realizable :=
    tableRealizable.letThen updateRealizable _ _ _
  exact lookupRealizable.letThen continuationRealizable (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact valid)

theorem catalogueMaps_realizable (elementDomain : EncodedDomain Empty) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ)
    (first second : ∀ sizes, elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    (catalogueMaps elementDomain indexCapacity length first second).Realizable := by
  let computation := catalogueMaps elementDomain indexCapacity length first second
  let singleton : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 1))
  let noArguments : Empty ↪ Fin 4 := ⟨Empty.elim, by intro empty; exact Empty.elim empty⟩
  let unitValue := (((constant singleton (fun _ => (0 : Fin 1))).withConstantSizes).withArguments
    computation.inputDomains noArguments (by intro empty; exact Empty.elim empty)).withPrecondition
      computation.precondition (by intro sizes arguments valid; trivial)
  let context : Fin 4 ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim computation.inputDomains (fun _ => singleton.constant)
  let firstSelection : Fin 3 ↪ Fin 4 ⊕ Unit :=
    ⟨(fun | 0 => .inl 0 | 1 => .inl 3 | 2 => .inr ()), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
  let firstCall := ((indexedMap singleton elementDomain indexCapacity length
    (fun sizes _ value => first sizes value)).withArguments context firstSelection
      (by intro name; fin_cases name <;> rfl)).withPrecondition
        (fun sizes arguments => computation.precondition sizes (fun name => arguments (.inl name)))
        (by intro sizes arguments valid; exact lt_of_lt_of_le valid.2.1 valid.1)
  let secondContext : (Fin 4 ⊕ Unit) ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim context (fun _ => elementDomain.constant.arrayOfLength length)
  let secondSelection : Fin 3 ↪ (Fin 4 ⊕ Unit) ⊕ Unit :=
    ⟨(fun | 0 => .inl (.inl 1) | 1 => .inr () | 2 => .inl (.inr ())), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩
  let secondCall := (indexedMap singleton elementDomain indexCapacity length
    (fun sizes _ value => second sizes value)).withArguments secondContext secondSelection
      (by intro name; fin_cases name <;> rfl)
  have unitRealizable : unitValue.Realizable :=
    (((constant_realizable singleton (fun _ => (0 : Fin 1))).withConstantSizes).withArguments _ _ _).withPrecondition _ _
  have firstRealizable : firstCall.Realizable :=
    ((indexedMap_realizable singleton elementDomain indexCapacity length _).withArguments _ _ _).withPrecondition _ _
  have secondRealizable : secondCall.Realizable :=
    (indexedMap_realizable singleton elementDomain indexCapacity length _).withArguments _ _ _
  let continuation := firstCall.letThen secondCall (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact lt_of_lt_of_le valid.2.2 valid.1)
  have continuationRealizable : continuation.Realizable :=
    firstRealizable.letThen secondRealizable _ _ _
  exact unitRealizable.letThen continuationRealizable (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact valid)

end IndexedComputations
end Polytime2.Computation
