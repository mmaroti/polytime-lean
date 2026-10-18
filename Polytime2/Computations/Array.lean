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
import Polytime2.RuntimeArrayLookupContract
import Polytime2.RuntimeArrayUpdateContract
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

private def mapPlacement : PublicTape Parameter Bool ↪ Parameter ⊕ Fin 3 :=
  (Function.Embedding.refl Parameter).sumMap
    ⟨(fun role => match role with | .inl false => 0 | .inl true => 1 | .inr _ => 2), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
/-- Lookup using a prepared unary width input. -/
private theorem arrayLookup_withUnaryWidth_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) :
    ((arrayLookup element indexCapacity length).withUnaryWidth element.widthPolynomial).Realizable := by
  refine ofNamedLayout ((arrayLookup element indexCapacity length).withUnaryWidth element.widthPolynomial)
    (RuntimeArrayLookup.domainsSized element indexCapacity length)
    RuntimeArrayLookup.argumentReadOnly RuntimeArrayLookup.sizeTapes RuntimeArrayLookup.outputTapes
    RuntimeArrayLookup.algorithmSized RuntimeArrayLookup.entry RuntimeArrayLookup.exit _ _
    (RuntimeArrayLookup.contractSized element indexCapacity length) (arrayPlacement 2 finTwoEquiv)
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
private theorem arrayUpdate_withUnaryWidth_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) :
    ((arrayUpdate element indexCapacity length).withUnaryWidth element.widthPolynomial).Realizable := by
  refine ofNamedLayout ((arrayUpdate element indexCapacity length).withUnaryWidth element.widthPolynomial)
    (RuntimeArrayUpdate.domainsSized element indexCapacity length)
    RuntimeArrayUpdate.argumentReadOnly RuntimeArrayUpdate.sizeTapes RuntimeArrayUpdate.outputTapes
    RuntimeArrayUpdate.algorithmSized RuntimeArrayUpdate.entry RuntimeArrayUpdate.exit _ _
    (RuntimeArrayUpdate.contractSized element indexCapacity length) (arrayPlacement 3 (Equiv.refl (Fin 3)))
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
theorem arrayLookup_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayLookup element indexCapacity length).Realizable :=
  Realizable.withComputedWidth (arrayLookup element indexCapacity length) element.widthPolynomial
    (arrayLookup_withUnaryWidth_realizable element indexCapacity length)

/-- Polynomial-width update preserves its original array and replacement. -/
theorem arrayUpdate_realizable (element : EncodedDomain Parameter) (indexCapacity : Parameter)
    (length : MvPolynomial Parameter ℕ) : (arrayUpdate element indexCapacity length).Realizable :=
  Realizable.withComputedWidth (arrayUpdate element indexCapacity length) element.widthPolynomial
    (arrayUpdate_withUnaryWidth_realizable element indexCapacity length)

open Realizable.Internal in
theorem arrayMap_realizable (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : ∀ sizes, parameterDomain.Carrier sizes → elementDomain.Carrier sizes → elementDomain.Carrier sizes) :
    (arrayMap parameterDomain elementDomain length operation).Realizable := by
  refine ofNamedLayout (arrayMap parameterDomain elementDomain length operation)
    (StandardArrayMap.domains parameterDomain elementDomain length)
    StandardArrayMap.argumentReadOnly StandardArrayMap.sizeTapes StandardArrayMap.outputTapes
    (StandardArrayMap.algorithm parameterDomain elementDomain operation) StandardArrayMap.entry StandardArrayMap.exit
    _ _ (StandardArrayMap.contract parameterDomain elementDomain length operation) mapPlacement
    (by rintro (parameter | argument | result) <;> first | rfl | (cases argument <;> rfl))
    (by rintro (parameter | argument | result) <;> first | rfl | (cases argument <;> rfl))
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded (elementDomain.constant.arrayOfLength length) sizes) correct

end Polytime2.Computation
