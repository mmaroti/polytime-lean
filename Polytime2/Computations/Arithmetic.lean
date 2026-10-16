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
import Polytime2.BinaryAddition
import Polytime2.BinarySubtraction
import Polytime2.StandardBinaryMultiplication
import Polytime2.StandardBinaryRemainder
import Polytime2.AddMultiply
import Polytime2.MultiplyAddContract

/-! # Mathematical bounded arithmetic with hidden finite implementations -/

namespace Polytime2.Computation

open MultiTape CallingConvention Realizable

private noncomputable def binarySpecification
    (precondition : ∀ sizes : Unit → ℕ, (Bool → Fin (2 ^ sizes ())) → Prop)
    (compute : ∀ sizes, {arguments : Bool → Fin (2 ^ sizes ()) // precondition sizes arguments} →
      Fin (2 ^ sizes ())) : Computation Unit Bool where
  inputDomains _ := EncodedDomain.binaryNaturals ()
  outputDomain := EncodedDomain.binaryNaturals ()
  precondition := precondition
  compute := compute

/-- Addition is exact whenever the sum fits the declared result capacity. -/
noncomputable def binaryAdd : Computation Unit Bool := binarySpecification
  (fun sizes arguments => (arguments false).val + (arguments true).val < 2 ^ sizes ())
  (fun _ arguments => ⟨(arguments.val false).val + (arguments.val true).val, arguments.property⟩)

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

private def arithmeticLayout : Unit ⊕ Fin 4 ≃ Unit ⊕ (Bool ⊕ (Unit ⊕ Unit)) where
  toFun
    | .inl parameter => .inl parameter
    | .inr 0 => .inr (.inl false)
    | .inr 1 => .inr (.inl true)
    | .inr 2 => .inr (.inr (.inl ()))
    | .inr 3 => .inr (.inr (.inr ()))
  invFun
    | .inl parameter => .inl parameter
    | .inr (.inl false) => .inr 0
    | .inr (.inl true) => .inr 1
    | .inr (.inr (.inl _)) => .inr 2
    | .inr (.inr (.inr _)) => .inr 3
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · cases scratch; rfl

private theorem arithmeticDomains
    (precondition : ∀ sizes : Unit → ℕ, (Bool → Fin (2 ^ sizes ())) → Prop)
    (compute : ∀ sizes, {arguments : Bool → Fin (2 ^ sizes ()) // precondition sizes arguments} →
      Fin (2 ^ sizes ())) (name : Unit ⊕ Fin 4) :
    domains (binarySpecification precondition compute) (fun _ : Unit => EncodedDomain.booleans)
      (arithmeticLayout name) = StandardBinaryArithmetic.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

/-- The carry/borrow is private when only the bounded natural result is exposed. -/
private theorem arithmetic_realizable
    (precondition : ∀ sizes : Unit → ℕ, (Bool → Fin (2 ^ sizes ())) → Prop)
    (compute : ∀ sizes, {arguments : Bool → Fin (2 ^ sizes ()) // precondition sizes arguments} →
      Fin (2 ^ sizes ()))
    (digit carry : Bool → Bool → Bool → Bool) (previous : Bool)
    (mathematical : ∀ sizes arguments (valid : precondition sizes arguments),
      Binary.value (BinaryRipple.ripple digit carry previous
        (List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments false)).getLsbD index.val))
        (List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments true)).getLsbD index.val))).1 =
        (compute sizes ⟨arguments, valid⟩).val) :
    (binarySpecification precondition compute).Realizable := by
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (arithmeticDomains precondition compute name))
  have readonly name : StandardBinaryArithmetic.argumentReadOnly name =
      readOnly (binarySpecification precondition compute) (arithmeticLayout name) := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  refine ofLayout (binarySpecification precondition compute) (fun _ : Unit => EncodedDomain.booleans)
    StandardBinaryArithmetic.domains StandardBinaryArithmetic.argumentReadOnly
    StandardBinaryArithmetic.sizeTapes StandardBinaryArithmetic.outputTapes (StandardBinaryArithmetic.algorithm digit carry)
    (StandardBinaryArithmetic.entry previous) StandardBinaryArithmetic.exit _ _
    (StandardBinaryArithmetic.contract digit carry previous) arithmeticLayout.toEmbedding values ?_ ?_ readonly
    (by intro parameter; rfl) false rfl (by intro sizes input valid; trivial) ?_
  · intro name sizes
    exact congrArg (fun domain => domain.width sizes) (arithmeticDomains precondition compute name)
  · intro name sizes value
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  · intro sizes input valid output result
    apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
    apply Fin.ext
    exact result.1.trans (mathematical sizes _ valid)

private def comparisonLayout : Unit ⊕ Fin 4 ≃ Unit ⊕ (Bool ⊕ (Unit ⊕ Unit)) where
  toFun
    | .inl parameter => .inl parameter
    | .inr 0 => .inr (.inl false)
    | .inr 1 => .inr (.inl true)
    | .inr 2 => .inr (.inr (.inr ()))
    | .inr 3 => .inr (.inr (.inl ()))
  invFun
    | .inl parameter => .inl parameter
    | .inr (.inl false) => .inr 0
    | .inr (.inl true) => .inr 1
    | .inr (.inr (.inl _)) => .inr 3
    | .inr (.inr (.inr _)) => .inr 2
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · cases scratch; rfl

private theorem comparisonDomains (name : Unit ⊕ Fin 4) :
    domains binaryLess (fun _ : Unit => EncodedDomain.binaryNaturals ()) (comparisonLayout name) =
      StandardBinaryArithmetic.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def multiplicationLayout : Bool ⊕ Fin 6 ≃ Bool ⊕ (Bool ⊕ (Unit ⊕ Fin 3)) where
  toFun | .inl parameter => .inl parameter
        | .inr 0 => .inr (.inr (.inl ()))
        | .inr 1 => .inr (.inl false)
        | .inr 2 => .inr (.inr (.inr 0))
        | .inr 3 => .inr (.inr (.inr 1))
        | .inr 4 => .inr (.inr (.inr 2))
        | .inr 5 => .inr (.inl true)
  invFun | .inl parameter => .inl parameter
         | .inr (.inr (.inl ())) => .inr 0
         | .inr (.inl false) => .inr 1
         | .inr (.inr (.inr 0)) => .inr 2
         | .inr (.inr (.inr 1)) => .inr 3
         | .inr (.inr (.inr 2)) => .inr 4
         | .inr (.inl true) => .inr 5
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · fin_cases scratch <;> rfl

private noncomputable def multiplicationScratch (name : Fin 3) : EncodedDomain Bool :=
  if name = 2 then EncodedDomain.booleans else EncodedDomain.binaryNaturals false

private theorem multiplicationDomains (name : Bool ⊕ Fin 6) :
    domains binaryMultiply multiplicationScratch (multiplicationLayout name) = StandardBinaryMultiplication.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def remainderLayout : Unit ⊕ Fin 7 ≃ Unit ⊕ (Bool ⊕ (Unit ⊕ Fin 4)) where
  toFun | .inl parameter => .inl parameter
        | .inr 0 => .inr (.inr (.inl ()))
        | .inr 1 => .inr (.inl true)
        | .inr 2 => .inr (.inr (.inr 0))
        | .inr 3 => .inr (.inr (.inr 1))
        | .inr 4 => .inr (.inr (.inr 2))
        | .inr 5 => .inr (.inr (.inr 3))
        | .inr 6 => .inr (.inl false)
  invFun | .inl parameter => .inl parameter
         | .inr (.inr (.inl ())) => .inr 0
         | .inr (.inl true) => .inr 1
         | .inr (.inr (.inr 0)) => .inr 2
         | .inr (.inr (.inr 1)) => .inr 3
         | .inr (.inr (.inr 2)) => .inr 4
         | .inr (.inr (.inr 3)) => .inr 5
         | .inr (.inl false) => .inr 6
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · cases argument <;> rfl
    · cases result; rfl
    · fin_cases scratch <;> rfl

private noncomputable def remainderScratch (name : Fin 4) : EncodedDomain Unit :=
  if name = 2 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

private theorem remainderDomains (name : Unit ⊕ Fin 7) :
    domains binaryRemainder remainderScratch (remainderLayout name) = StandardBinaryRemainder.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private noncomputable def compoundScratch (name : Fin 5) : EncodedDomain Bool :=
  if name = 3 ∨ name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals false

private def binaryAddMultiplyLayout : Bool ⊕ Fin 9 ≃ Bool ⊕ (Fin 3 ⊕ (Unit ⊕ Fin 5)) where
  toFun
    | .inl parameter => .inl parameter
    | .inr 0 => .inr (.inr (.inl ()))
    | .inr 1 => .inr (.inr (.inr 0))
    | .inr 2 => .inr (.inr (.inr 1))
    | .inr 3 => .inr (.inr (.inr 2))
    | .inr 4 => .inr (.inr (.inr 3))
    | .inr 5 => .inr (.inl 2)
    | .inr 6 => .inr (.inl 0)
    | .inr 7 => .inr (.inl 1)
    | .inr 8 => .inr (.inr (.inr 4))
  invFun
    | .inl parameter => .inl parameter
    | .inr (.inr (.inl ())) => .inr 0
    | .inr (.inr (.inr 0)) => .inr 1
    | .inr (.inr (.inr 1)) => .inr 2
    | .inr (.inr (.inr 2)) => .inr 3
    | .inr (.inr (.inr 3)) => .inr 4
    | .inr (.inl 2) => .inr 5
    | .inr (.inl 0) => .inr 6
    | .inr (.inl 1) => .inr 7
    | .inr (.inr (.inr 4)) => .inr 8
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · fin_cases argument <;> rfl
    · cases result; rfl
    · fin_cases scratch <;> rfl

private theorem binaryAddMultiplyDomains (name : Bool ⊕ Fin 9) :
    domains binaryAddMultiply compoundScratch (binaryAddMultiplyLayout name) = AddMultiply.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

private def binaryMultiplyAddLayout : Bool ⊕ Fin 9 ≃ Bool ⊕ (Fin 3 ⊕ (Unit ⊕ Fin 5)) where
  toFun
    | .inl parameter => .inl parameter
    | .inr 0 => .inr (.inr (.inr 0))
    | .inr 1 => .inr (.inl 0)
    | .inr 2 => .inr (.inr (.inr 1))
    | .inr 3 => .inr (.inr (.inr 2))
    | .inr 4 => .inr (.inr (.inr 3))
    | .inr 5 => .inr (.inl 1)
    | .inr 6 => .inr (.inl 2)
    | .inr 7 => .inr (.inr (.inl ()))
    | .inr 8 => .inr (.inr (.inr 4))
  invFun
    | .inl parameter => .inl parameter
    | .inr (.inr (.inr 0)) => .inr 0
    | .inr (.inl 0) => .inr 1
    | .inr (.inr (.inr 1)) => .inr 2
    | .inr (.inr (.inr 2)) => .inr 3
    | .inr (.inr (.inr 3)) => .inr 4
    | .inr (.inl 1) => .inr 5
    | .inr (.inl 2) => .inr 6
    | .inr (.inr (.inl ())) => .inr 7
    | .inr (.inr (.inr 4)) => .inr 8
  left_inv name := by
    cases name with
    | inl parameter => rfl
    | inr name => fin_cases name <;> rfl
  right_inv name := by
    rcases name with parameter | argument | result | scratch
    · rfl
    · fin_cases argument <;> rfl
    · cases result; rfl
    · fin_cases scratch <;> rfl

private theorem binaryMultiplyAddDomains (name : Bool ⊕ Fin 9) :
    domains binaryMultiplyAdd compoundScratch (binaryMultiplyAddLayout name) = MultiplyAdd.domains name := by
  cases name with
  | inl parameter => rfl
  | inr name => fin_cases name <;> rfl

end Realizable.Internal

open Realizable.Internal in
theorem binaryAdd_realizable : binaryAdd.Realizable := by
  apply arithmetic_realizable _ _ BinaryAddition.digit BinaryAddition.carry false
  intro sizes arguments valid
  let left := List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments false)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (sizes ()) => (BitVec.ofFin (arguments true)).getLsbD index.val)
  have equation := BinaryAddition.ripple_value false left right (by simp [left, right])
  have leftValue : Binary.value left = (arguments false).val := Binary.value_bits (BitVec.ofFin (arguments false))
  have rightValue : Binary.value right = (arguments true).val := Binary.value_bits (BitVec.ofFin (arguments true))
  simp only [leftValue, rightValue, Bool.toNat_false, Nat.add_zero] at equation
  cases finalCarry : (BinaryAddition.ripple false left right).2 with
  | false => simpa only [finalCarry, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] using equation
  | true =>
    simp only [finalCarry, Bool.toNat_true, Nat.mul_one, left, List.length_ofFn] at equation
    omega

open Realizable.Internal in
theorem binarySubtract_realizable : binarySubtract.Realizable := by
  apply arithmetic_realizable _ _ BinarySubtraction.digit BinarySubtraction.borrow false
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
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (comparisonDomains name))
  refine ofLayout binaryLess (fun _ : Unit => EncodedDomain.binaryNaturals ())
    BinarySubtraction.domains BinarySubtraction.argumentReadOnly BinarySubtraction.sizeTapes
    StandardBinaryArithmetic.outputTapes BinarySubtraction.algorithm BinarySubtraction.entry BinarySubtraction.exit
    _ _ BinarySubtraction.comparison_contract comparisonLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (comparisonDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) true rfl (by intro sizes input valid; trivial) ?_
  intro sizes input valid output correct
  exact congrArg (encoded EncodedDomain.booleans sizes) correct

open Realizable.Internal in
theorem binaryMultiply_realizable : binaryMultiply.Realizable := by
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (multiplicationDomains name))
  refine ofLayout binaryMultiply multiplicationScratch StandardBinaryMultiplication.domains StandardBinaryMultiplication.argumentReadOnly
    StandardBinaryMultiplication.sizeTapes StandardBinaryMultiplication.outputTapes StandardBinaryMultiplication.algorithm StandardBinaryMultiplication.entry StandardBinaryMultiplication.exit
    _ _ StandardBinaryMultiplication.contract multiplicationLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (multiplicationDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals false) sizes)
  apply Fin.ext
  exact correct

open Realizable.Internal in
theorem binaryRemainder_realizable : binaryRemainder.Realizable := by
  let values name sizes := Equiv.cast (congrArg (fun domain => domain.Carrier sizes) (remainderDomains name))
  refine ofLayout binaryRemainder remainderScratch StandardBinaryRemainder.domains StandardBinaryRemainder.argumentReadOnly
    StandardBinaryRemainder.sizeTapes StandardBinaryRemainder.outputTapes StandardBinaryRemainder.algorithm StandardBinaryRemainder.entry StandardBinaryRemainder.exit
    _ _ StandardBinaryRemainder.contract remainderLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (remainderDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals ()) sizes)
  apply Fin.ext
  exact correct

open Realizable.Internal in
theorem binaryAddMultiply_realizable : binaryAddMultiply.Realizable := by
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (binaryAddMultiplyDomains name))
  refine ofLayout binaryAddMultiply compoundScratch AddMultiply.domains AddMultiply.argumentReadOnly
    AddMultiply.sizeTapes AddMultiply.outputTapes AddMultiply.algorithm AddMultiply.entry AddMultiply.exit
    _ _ AddMultiply.contract binaryAddMultiplyLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (binaryAddMultiplyDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals false) sizes)
  apply Fin.ext
  exact correct

open Realizable.Internal in
theorem binaryMultiplyAdd_realizable : binaryMultiplyAdd.Realizable := by
  let values name sizes := Equiv.cast
    (congrArg (fun domain => domain.Carrier sizes) (binaryMultiplyAddDomains name))
  refine ofLayout binaryMultiplyAdd compoundScratch MultiplyAdd.domains MultiplyAdd.argumentReadOnly
    MultiplyAdd.sizeTapes MultiplyAdd.outputTapes MultiplyAdd.algorithm MultiplyAdd.entry MultiplyAdd.exit
    _ _ MultiplyAdd.contract binaryMultiplyAddLayout.toEmbedding values
    (by intro name sizes; exact congrArg (fun domain => domain.width sizes) (binaryMultiplyAddDomains name))
    (by intro name sizes value; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro parameter; rfl) () rfl (by intro sizes input valid; exact valid) ?_
  intro sizes input valid output correct
  apply congrArg (encoded (EncodedDomain.binaryNaturals false) sizes)
  apply Fin.ext
  exact correct

end Polytime2.Computation
