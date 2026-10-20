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

import Polytime2.Computation.Branch
import Polytime2.Computation.Composition
import Polytime2.Arithmetic.Operations
import Polytime2.Arithmetic.CounterOperations

/-! # Arithmetic through mathematical specifications and existential certificates -/

namespace Polytime2.Examples.Arithmetic

open Polytime2.Computation

/-- Subtract the original second argument from the preceding sum. -/
private noncomputable def subtractOriginal : Polytime2.Computation Unit (Bool ⊕ Unit) :=
  binarySubtract.withArguments (fun _ => EncodedDomain.binaryNaturals ())
    ⟨(fun | false => .inr () | true => .inl true), by
      intro first second equal
      cases first <;> cases second <;> first | rfl | cases equal⟩
    (fun _ => rfl)

/-- Compute a sum, then reuse one original argument in the next call. -/
noncomputable def addThenCancel : Polytime2.Computation Unit Bool :=
  binaryAdd.letThen subtractOriginal (fun _ => rfl) rfl (by
    intro sizes arguments valid
    change (arguments true).val ≤ (arguments false).val + (arguments true).val
    omega)

theorem addThenCancel_realizable : addThenCancel.Realizable := by
  apply Computation.Realizable.letThen binaryAdd_realizable
  exact binarySubtract_realizable.withArguments _ _ _

/-- The result is independent of every private implementation choice. -/
theorem addThenCancel_correct (sizes : Unit → ℕ) (arguments : addThenCancel.Arguments sizes)
    (valid : addThenCancel.precondition sizes arguments) :
    addThenCancel.compute sizes ⟨arguments, valid⟩ = arguments false := by
  apply Fin.ext
  change (arguments false).val + (arguments true).val - (arguments true).val = (arguments false).val
  omega

example : (addThenCancel.compute (fun _ => 4)
    ⟨(fun | false => (7 : Fin 16) | true => (5 : Fin 16)), by change 7 + 5 < 16; decide⟩ : Fin 16) = (7 : Fin 16) := rfl

-- Zero-bit operands remain admissible for exact bounded addition and subtraction.
example : (binaryAdd.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), by change 0 + 0 < 1; decide⟩ : Fin 1) = (0 : Fin 1) := rfl
example : (binarySubtract.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), by change 0 ≤ 0; decide⟩ : Fin 1) = (0 : Fin 1) := rfl

-- Modular increment keeps its capacity, including overflow and zero-bit inputs.
example : (counterIncrement ()).compute (fun _ => 3)
    ⟨(fun _ => (7 : Fin 8)), True.intro⟩ = (0 : Fin 8) := rfl
example : (counterIncrement ()).compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), True.intro⟩ = (0 : Fin 1) := rfl

/-- The zero case needs no proof that the decrement routine accepts zero. -/
noncomputable def saturatingDecrement : Polytime2.Computation Unit Unit :=
  counterNonzero.letThen
    ((counterDecrement ()).choose (copy (EncodedDomain.binaryNaturals ()))
      (fun _ => rfl) rfl)
    (fun _ => rfl) rfl (by
      intro sizes arguments valid
      dsimp only [choose, counterNonzero, counterDecrement, copy]
      split
      · rename_i selected
        exact of_decide_eq_true selected
      · trivial)

theorem saturatingDecrement_realizable : saturatingDecrement.Realizable := by
  apply Computation.Realizable.letThen counterNonzero_realizable
  exact (counterDecrement_realizable ()).choose
    (copy_realizable (EncodedDomain.binaryNaturals ())) _ _

example : (saturatingDecrement.compute (fun _ => 3)
    ⟨(fun _ => (5 : Fin 8)), True.intro⟩ : Fin 8) = (4 : Fin 8) := rfl
example : (saturatingDecrement.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), True.intro⟩ : Fin 1) = (0 : Fin 1) := rfl

example : binaryLess.Realizable := binaryLess_realizable
example : binaryLess.compute (fun _ => 3)
    ⟨(fun | false => (3 : Fin 8) | true => (5 : Fin 8)), True.intro⟩ = true := rfl
example : binaryLess.compute (fun _ => 3)
    ⟨(fun _ => (5 : Fin 8)), True.intro⟩ = false := rfl
example : binaryLess.compute (fun _ => 0)
    ⟨(fun _ => (0 : Fin 1)), True.intro⟩ = false := rfl

private def operandSelection (which : Bool) : Unit ↪ Bool :=
  ⟨(fun _ => which), by intro first second _; cases first; cases second; rfl⟩

private noncomputable def selectOperand (which : Bool) : Polytime2.Computation Unit Bool :=
  (copy (EncodedDomain.binaryNaturals ())).withArguments
    (fun _ => EncodedDomain.binaryNaturals ()) (operandSelection which) (fun _ => rfl)

private theorem selectOperand_realizable (which : Bool) : (selectOperand which).Realizable :=
  (copy_realizable (EncodedDomain.binaryNaturals ())).withArguments _ _ _

/-- Comparison chooses an operand while retaining both original arguments. -/
noncomputable def minimum : Polytime2.Computation Unit Bool := binaryLess.letThen
  ((selectOperand false).choose (selectOperand true) (fun _ => rfl) rfl)
  (fun _ => rfl) rfl (by
    intro sizes arguments valid
    dsimp only [choose, selectOperand, withArguments, copy]
    split <;> trivial)

theorem minimum_realizable : minimum.Realizable := by
  apply Computation.Realizable.letThen binaryLess_realizable
  exact (selectOperand_realizable false).choose (selectOperand_realizable true) _ _

example : (minimum.compute (fun _ => 3)
    ⟨(fun | false => (5 : Fin 8) | true => (3 : Fin 8)), True.intro⟩ : Fin 8) = (3 : Fin 8) := rfl
example : (minimum.compute (fun _ => 3)
    ⟨(fun | false => (3 : Fin 8) | true => (5 : Fin 8)), True.intro⟩ : Fin 8) = (3 : Fin 8) := rfl

example : binaryMultiply.Realizable := binaryMultiply_realizable
example : binaryRemainder.Realizable := binaryRemainder_realizable

-- Multiplication allows independent factor/result and multiplier capacities.
example : (binaryMultiply.compute (fun | false => 7 | true => 4)
    ⟨(fun | false => (8 : Fin 128) | true => (13 : Fin 16)),
      by change 8 * 13 < 128; decide⟩ : Fin 128) = (104 : Fin 128) := rfl
example : (binaryMultiply.compute (fun | false => 0 | true => 3)
    ⟨(fun | false => (0 : Fin 1) | true => (7 : Fin 8)),
      by change 0 * 7 < 1; decide⟩ : Fin 1) = (0 : Fin 1) := rfl

example : (binaryRemainder.compute (fun _ => 4)
    ⟨(fun | false => (13 : Fin 16) | true => (5 : Fin 16)),
      by change 0 < 5; decide⟩ : Fin 16) = (3 : Fin 16) := rfl

-- Divisors may occupy the highest bit; no shift-bit condition is public.
example : (binaryRemainder.compute (fun _ => 4)
    ⟨(fun | false => (13 : Fin 16) | true => (15 : Fin 16)), by change 0 < 15; decide⟩ : Fin 16) = (13 : Fin 16) := rfl
example : (binaryRemainder.compute (fun _ => 4)
    ⟨(fun | false => (13 : Fin 16) | true => (8 : Fin 16)), by change 0 < 8; decide⟩ : Fin 16) = (5 : Fin 16) := rfl
example : (binaryRemainder.compute (fun _ => 4)
    ⟨(fun _ => (15 : Fin 16)), by change 0 < 15; decide⟩ : Fin 16) = (0 : Fin 16) := rfl
example : (binaryRemainder.compute (fun _ => 4)
    ⟨(fun | false => (0 : Fin 16) | true => (15 : Fin 16)), by change 0 < 15; decide⟩ : Fin 16) = (0 : Fin 16) := rfl
example : (binaryRemainder.compute (fun _ => 1)
    ⟨(fun _ => (1 : Fin 2)), by change 0 < 1; decide⟩ : Fin 2) = (0 : Fin 2) := rfl

-- Width zero admits no positive divisor, as required mathematically.
example (arguments : binaryRemainder.Arguments (fun _ => 0)) :
    ¬ binaryRemainder.precondition (fun _ => 0) arguments := by
  change ¬ 0 < (arguments true).val
  have bound := (arguments true).isLt
  norm_num at bound
  omega

end Polytime2.Examples.Arithmetic
