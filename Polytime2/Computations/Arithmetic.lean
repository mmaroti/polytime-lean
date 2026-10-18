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
import Polytime2.Computation.Composition
import Polytime2.BinaryAddition
import Polytime2.BinarySubtraction
import Polytime2.StandardBinaryMultiplication
import Polytime2.StandardBinaryRemainder

/-! # Mathematical bounded arithmetic with hidden finite implementations -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

private noncomputable def binarySpecificationAt {Parameter : Type} [Fintype Parameter] (capacity : Parameter)
    (precondition : ∀ sizes : Parameter → ℕ, (Bool → Fin (2 ^ sizes capacity)) → Prop)
    (compute : ∀ sizes, {arguments : Bool → Fin (2 ^ sizes capacity) // precondition sizes arguments} →
      Fin (2 ^ sizes capacity)) : Computation Parameter Bool where
  inputDomains _ := EncodedDomain.binaryNaturals capacity
  outputDomain := EncodedDomain.binaryNaturals capacity
  precondition := precondition
  compute := compute

private noncomputable abbrev binarySpecification := binarySpecificationAt ()

/-- Addition at any named capacity is exact whenever its sum fits. -/
noncomputable def binaryAddAt {Parameter : Type} [Fintype Parameter] (capacity : Parameter) :
    Computation Parameter Bool := binarySpecificationAt capacity
  (fun sizes arguments => (arguments false).val + (arguments true).val < 2 ^ sizes capacity)
  (fun _ arguments => ⟨(arguments.val false).val + (arguments.val true).val, arguments.property⟩)

/-- The single-capacity addition specification. -/
noncomputable def binaryAdd : Computation Unit Bool := binaryAddAt ()

/-- Natural subtraction is specified only when the second operand is no larger. -/
noncomputable def binarySubtract : Computation Unit Bool := binarySpecification
  (fun _ arguments => (arguments true).val ≤ (arguments false).val)
  (fun _ arguments => ⟨(arguments.val false).val - (arguments.val true).val,
    lt_of_le_of_lt (Nat.sub_le _ _) (arguments.val false).isLt⟩)

/-- Unsigned comparison has no capacity or ordering precondition. -/
noncomputable def binaryLess : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.booleans
  precondition _ _ := True
  compute _ arguments := decide ((arguments.val false).val < (arguments.val true).val)

/-- The factor/result and multiplier capacities are independent size parameters. -/
noncomputable def binaryMultiply : Computation Bool Bool where
  inputDomains := EncodedDomain.binaryNaturals
  outputDomain := EncodedDomain.binaryNaturals false
  precondition sizes arguments := (arguments false).val * (arguments true).val < 2 ^ sizes false
  compute _ arguments := ⟨(arguments.val false).val * (arguments.val true).val, arguments.property⟩

/-- A positive divisor reserves the shift bit needed by binary long remainder. -/
noncomputable def binaryRemainder : Computation Unit Bool := binarySpecification
  (fun sizes arguments => 0 < (arguments true).val ∧ 2 * (arguments true).val ≤ 2 ^ sizes ())
  (fun _ arguments => ⟨(arguments.val false).val % (arguments.val true).val,
    lt_trans (Nat.mod_lt _ arguments.property.1) (arguments.val true).isLt⟩)

/-- Arguments are the two summands and the independent-width multiplier.
The intermediate sum and final product must fit the declared capacity. -/
noncomputable def binaryAddMultiply : Computation Bool (Fin 3) where
  inputDomains name := EncodedDomain.binaryNaturals (decide (name = 2))
  outputDomain := EncodedDomain.binaryNaturals false
  precondition sizes arguments :=
    (arguments 0).val + (arguments 1).val < 2 ^ sizes false ∧
      ((arguments 0).val + (arguments 1).val) * (arguments 2).val < 2 ^ sizes false
  compute _ arguments :=
    ⟨((arguments.val 0).val + (arguments.val 1).val) * (arguments.val 2).val,
      arguments.property.2⟩

/-- Arguments are the factor, independent-width multiplier, and addend. -/
noncomputable def binaryMultiplyAdd : Computation Bool (Fin 3) where
  inputDomains name := EncodedDomain.binaryNaturals (decide (name = 1))
  outputDomain := EncodedDomain.binaryNaturals false
  precondition sizes arguments :=
    (arguments 0).val * (arguments 1).val + (arguments 2).val < 2 ^ sizes false
  compute _ arguments :=
    ⟨(arguments.val 0).val * (arguments.val 1).val + (arguments.val 2).val,
      arguments.property⟩

namespace Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private def arithmeticPlacement : PublicTape Parameter Bool ↪ Parameter ⊕ Fin 4 :=
  (Function.Embedding.refl Parameter).sumMap
    ⟨(fun role => match role with | .inl false => 0 | .inl true => 1 | .inr _ => 2), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

/-- The carry/borrow is private when only the bounded natural result is exposed. -/
private theorem arithmetic_realizable (capacity : Parameter)
    (precondition : ∀ sizes : Parameter → ℕ, (Bool → Fin (2 ^ sizes capacity)) → Prop)
    (compute : ∀ sizes, {arguments : Bool → Fin (2 ^ sizes capacity) // precondition sizes arguments} →
      Fin (2 ^ sizes capacity))
    (digit carry : Bool → Bool → Bool → Bool) (previous : Bool)
    (mathematical : ∀ sizes arguments (valid : precondition sizes arguments),
      Binary.value (BinaryRipple.ripple digit carry previous
        (List.ofFn (fun index : Fin (sizes capacity) => (BitVec.ofFin (arguments false)).getLsbD index.val))
        (List.ofFn (fun index : Fin (sizes capacity) => (BitVec.ofFin (arguments true)).getLsbD index.val))).1 =
        (compute sizes ⟨arguments, valid⟩).val) :
    (binarySpecificationAt capacity precondition compute).Realizable := by
  refine ofNamedLayout (binarySpecificationAt capacity precondition compute)
    (StandardBinaryArithmetic.domainsSized capacity) StandardBinaryArithmetic.argumentReadOnly
    StandardBinaryArithmetic.sizeTapes StandardBinaryArithmetic.outputTapes (StandardBinaryArithmetic.algorithm digit carry)
    (StandardBinaryArithmetic.entry previous) StandardBinaryArithmetic.exit _ _
    (StandardBinaryArithmetic.contractSized capacity digit carry previous) arithmeticPlacement
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
    (by intro parameter; rfl) false rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output result
  apply congrArg (encoded (EncodedDomain.binaryNaturals capacity) sizes)
  apply Fin.ext
  exact result.1.trans (mathematical sizes _ valid)

private def comparisonPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 4 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 0 | .inl true => 1 | .inr _ => 3), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

private def multiplicationPlacement : PublicTape Bool Bool ↪ Bool ⊕ Fin 6 :=
  (Function.Embedding.refl Bool).sumMap
    ⟨(fun role => match role with | .inl false => 1 | .inl true => 5 | .inr _ => 0), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

private def remainderPlacement : PublicTape Unit Bool ↪ Unit ⊕ Fin 7 :=
  (Function.Embedding.refl Unit).sumMap
    ⟨(fun role => match role with | .inl false => 6 | .inl true => 1 | .inr _ => 0), by
      intro first second equal
      fin_cases first <;> fin_cases second <;> first | rfl | cases equal⟩

end Realizable.Internal

open Realizable.Internal in
theorem binaryAddAt_realizable {Parameter : Type} [Fintype Parameter] (capacity : Parameter) :
    (binaryAddAt capacity).Realizable := by
  apply arithmetic_realizable capacity _ _ BinaryAddition.digit BinaryAddition.carry false
  intro sizes arguments valid
  let left := List.ofFn (fun index : Fin (sizes capacity) => (BitVec.ofFin (arguments false)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (sizes capacity) => (BitVec.ofFin (arguments true)).getLsbD index.val)
  have leftValue : Binary.value left = (arguments false).val := Binary.value_bits (BitVec.ofFin (arguments false))
  have rightValue : Binary.value right = (arguments true).val := Binary.value_bits (BitVec.ofFin (arguments true))
  have fits : Binary.value left + Binary.value right < 2 ^ left.length := by
    simpa only [leftValue, rightValue, left, List.length_ofFn] using valid
  simpa only [BinaryAddition.lowSum, leftValue, rightValue] using
    (BinaryAddition.lowSum_value left right (by simp [left, right]) fits).1

theorem binaryAdd_realizable : binaryAdd.Realizable := binaryAddAt_realizable ()

open Realizable.Internal in
theorem binarySubtract_realizable : binarySubtract.Realizable := by
  apply arithmetic_realizable () _ _ BinarySubtraction.digit BinarySubtraction.borrow false
  intro sizes arguments valid
  let left := List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments false)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments true)).getLsbD index.val)
  have leftValue : Binary.value left = (arguments false).val := Binary.value_bits (BitVec.ofFin (arguments false))
  have rightValue : Binary.value right = (arguments true).val := Binary.value_bits (BitVec.ofFin (arguments true))
  have nonnegative : Binary.value right ≤ Binary.value left := by rw [leftValue, rightValue]; exact valid
  simpa only [leftValue, rightValue] using
    BinarySubtraction.difference_of_no_borrow left right (by simp [left, right]) nonnegative

open Realizable.Internal in
theorem binaryLess_realizable : binaryLess.Realizable := by
  refine ofNamedLayout binaryLess StandardBinaryArithmetic.domains StandardBinaryArithmetic.argumentReadOnly
    StandardBinaryArithmetic.sizeTapes StandardBinaryArithmetic.outputTapes BinarySubtraction.algorithm BinarySubtraction.entry BinarySubtraction.exit
    _ _ BinarySubtraction.comparison_contract comparisonPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro parameter; rfl) true rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  exact congrArg (encoded EncodedDomain.booleans sizes) correct

open Realizable.Internal in
theorem binaryMultiply_realizable : binaryMultiply.Realizable := by
  refine ofNamedLayout binaryMultiply StandardBinaryMultiplication.domains StandardBinaryMultiplication.argumentReadOnly
    StandardBinaryMultiplication.sizeTapes StandardBinaryMultiplication.outputTapes StandardBinaryMultiplication.algorithm StandardBinaryMultiplication.entry StandardBinaryMultiplication.exit
    _ _ StandardBinaryMultiplication.contract multiplicationPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals false) sizes)
  apply Fin.ext
  exact correct

open Realizable.Internal in
theorem binaryRemainder_realizable : binaryRemainder.Realizable := by
  refine ofNamedLayout binaryRemainder StandardBinaryRemainder.domains StandardBinaryRemainder.argumentReadOnly
    StandardBinaryRemainder.sizeTapes StandardBinaryRemainder.outputTapes StandardBinaryRemainder.algorithm StandardBinaryRemainder.entry StandardBinaryRemainder.exit
    _ _ StandardBinaryRemainder.contract remainderPlacement
    (by intro role; fin_cases role <;> rfl) (by intro role; fin_cases role <;> rfl)
    (by
      intro name outside
      cases name with
      | inl parameter => exact False.elim (outside ⟨.inl parameter, rfl⟩)
      | inr name => fin_cases name <;> first
        | rfl
        | exact False.elim (outside ⟨.inr (.inl false), rfl⟩)
        | exact False.elim (outside ⟨.inr (.inl true), rfl⟩))
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
  apply Fin.ext
  exact correct

theorem binaryAddMultiply_realizable : binaryAddMultiply.Realizable := by
  let domains := binaryAddMultiply.inputDomains
  let selectSummands : Bool ↪ Fin 3 :=
    ⟨(fun flag => if flag then 1 else 0), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let addition := ((binaryAddAt false).withArguments domains selectSummands
    (by intro flag; cases flag <;> rfl)).withPrecondition binaryAddMultiply.precondition
      (by intro sizes arguments valid; exact valid.1)
  let context : Fin 3 ⊕ Unit → EncodedDomain Bool :=
    Sum.elim domains (fun _ => EncodedDomain.binaryNaturals false)
  let selectProduct : Bool ↪ Fin 3 ⊕ Unit :=
    ⟨(fun flag => if flag then .inl 2 else .inr ()), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let multiplication := binaryMultiply.withArguments context selectProduct
    (by intro flag; cases flag <;> rfl)
  have additionRealizable : addition.Realizable :=
    ((binaryAddAt_realizable false).withArguments _ _ _).withPrecondition _ _
  have multiplicationRealizable : multiplication.Realizable := binaryMultiply_realizable.withArguments _ _ _
  exact additionRealizable.letThen multiplicationRealizable (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact valid.2)

theorem binaryMultiplyAdd_realizable : binaryMultiplyAdd.Realizable := by
  let domains := binaryMultiplyAdd.inputDomains
  let selectFactors : Bool ↪ Fin 3 :=
    ⟨(fun flag => if flag then 1 else 0), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let multiplication := (binaryMultiply.withArguments domains selectFactors
    (by intro flag; cases flag <;> rfl)).withPrecondition binaryMultiplyAdd.precondition
      (by intro sizes arguments valid; exact lt_of_le_of_lt (Nat.le_add_right _ _) valid)
  let context : Fin 3 ⊕ Unit → EncodedDomain Bool :=
    Sum.elim domains (fun _ => EncodedDomain.binaryNaturals false)
  let selectSum : Bool ↪ Fin 3 ⊕ Unit :=
    ⟨(fun flag => if flag then .inl 2 else .inr ()), by
      intro first second equal
      cases first <;> cases second <;> simp_all⟩
  let addition := (binaryAddAt false).withArguments context selectSum
    (by intro flag; cases flag <;> rfl)
  have multiplicationRealizable : multiplication.Realizable :=
    (binaryMultiply_realizable.withArguments _ _ _).withPrecondition _ _
  have additionRealizable : addition.Realizable := (binaryAddAt_realizable false).withArguments _ _ _
  exact multiplicationRealizable.letThen additionRealizable (by intro name; rfl) rfl
    (by intro sizes arguments valid; exact valid)

end Polytime2.Computation
