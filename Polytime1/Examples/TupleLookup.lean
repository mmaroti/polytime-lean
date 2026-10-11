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

import Polytime1.TupleMachine

/-! # A complete indexed Boolean tuple example

The size context has one parameter, the tuple length. Indices have bounded
natural presentations. The machine returns both the lookup result and the
updated tuple, with a proved quadratic bound including frame preparation.
-/

namespace Polytime1.Examples.TupleLookup

abbrev context : SizeContext := ⟨Unit, inferInstance⟩

def assignment (length : ℕ) : SizeAssignment context := fun _ => length

def lengthCode : SizeExpression context := .parameter ()

@[simp] theorem evaluate_length (length : ℕ) : lengthCode.eval (assignment length) = length := rfl

noncomputable section DomainExamples

def tupleDomain : DomainExpression context := BoolTuple.domain lengthCode

def indexDomain : EncodedDomain context := BoundedNat.domain lengthCode

@[simp] theorem tuple_width (length : ℕ) : tupleDomain.bitWidth (assignment length) = length := by
  simp [tupleDomain, lengthCode, assignment]

@[simp] theorem index_width (length : ℕ) :
    indexDomain.expression.bitWidth (assignment length) = length := by
  simp [indexDomain, lengthCode, assignment]

/-- Zero capacity is an empty index domain, not a distinguished error value. -/
example : IsEmpty (indexDomain.Carrier (assignment 0)) := by
  simp [indexDomain, BoundedNat.domain, lengthCode, assignment]

example : tupleDomain.bitWidth (assignment 0) = 0 := by simp

end DomainExamples

theorem update_list {length : ℕ} (tuple : Fin length → Bool) (index : Fin length)
    (replacement : Bool) :
    List.ofFn (BoolTuple.update tuple index replacement) = (List.ofFn tuple).set index.val replacement := by
  apply List.ext_getElem (by simp)
  intro position firstValid secondValid
  simp [BoolTuple.update, List.getElem_set, Fin.ext_iff, eq_comm]

theorem lookup_list {length : ℕ} (tuple : Fin length → Bool) (index : Fin length) :
    (List.ofFn tuple).getD index.val false = BoolTuple.lookup tuple index := by
  simp [List.getD_eq_getElem?_getD, index.isLt, BoolTuple.lookup]

/-- Tape realization of the mathematical lookup/update contracts on exact tuples. -/
theorem realizes_tuple {length : ℕ} (tuple : Fin length → Bool) (index : Fin length)
    (replacement : Bool) :
    ∃ ticks, ticks ≤ 32 * (length + 1) ^ 2 ∧
      TupleMachine.Steps ticks
        (Turing.TM0.init (TupleMachine.input (List.ofFn tuple)
          (index.cast (List.length_ofFn (f := tuple)).symm) replacement))
        (TupleMachine.configuration (BoolTuple.lookup tuple index) 15
          (List.replicate length (TupleMachine.data true) ++ 3 :: TupleMachine.data false ::
            List.replicate length (TupleMachine.data true))
          (TupleMachine.data (BoolTuple.lookup tuple index) ::
            (TupleMachine.word (List.ofFn (BoolTuple.update tuple index replacement)) ++ [7]))) := by
  simpa [lookup_list, ← update_list, BoolTuple.lookup] using
    TupleMachine.realizes (List.ofFn tuple) (index.cast (List.length_ofFn (f := tuple)).symm) replacement

/-- An executable observer for the declared output region, used by examples. -/
def execute (bits : List Bool) (index : Fin bits.length) (replacement : Bool) : Option (List Bool) :=
  (Tape.run TupleMachine.machine (32 * (bits.length + 1) ^ 2)
    (Turing.TM0.init (TupleMachine.input bits index replacement))).map fun final =>
      (List.range (bits.length + 1)).map fun position =>
        decide (final.Tape.right₀.nth position = TupleMachine.data true)

#guard execute [false] 0 true = some [false, true]
#guard execute [true, false, true, false] 0 false = some [true, false, false, true, false]
#guard execute [true, false, true, false] 3 true = some [false, true, false, true, true]
-- Borrow propagates through three zero bits when the selected index is eight.
#guard execute [false, true, false, true, false, true, false, true, false] 8 true =
  some [false, false, true, false, true, false, true, false, true, true]

end Polytime1.Examples.TupleLookup
