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

import Polytime2.Computation.Traversal
import Polytime2.Computation.Constant
import Polytime2.Arithmetic.CounterOperations
import Polytime2.Primitives.FiniteOperations
import Polytime2.TM0.Computation

/-! # Folds and bounded iteration using only public mathematical rules -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.Fold

open _root_.Polytime2.Computation

private noncomputable def booleans : EncodedDomain Bool :=
  (EncodedDomain.booleans : EncodedDomain Empty).constant

/-- Boolean OR is accumulated across an array of runtime length. -/
noncomputable def anyTrue : Polytime2.Computation Bool (Empty ⊕ Bool) :=
  arrayFold Empty.elim booleans booleans (MvPolynomial.X true)
    (fun _ _ _ _ => True) (fun _ _ accumulator value => accumulator || value)

theorem anyTrue_realizable : anyTrue.Realizable := by
  apply arrayFold_total_realizable
  exact ((finiteTable_realizable EncodedDomain.booleans EncodedDomain.booleans EncodedDomain.booleans
    (fun _ first second => first || second)).withConstantSizes (Parameter := Bool)).withArguments _
      ⟨Sum.inr, Sum.inr_injective⟩ (by intro choice; cases choice <;> rfl)

example : anyTrue.TM0Realizable := anyTrue_realizable.tm0

/-- Whole runtime-width words, including matrix rows, can be fold elements.
An immutable context word remains available to the update without tape proofs. -/
noncomputable def lastWord : Polytime2.Computation Bool (Unit ⊕ Bool) :=
  let word := EncodedDomain.bitVectors (MvPolynomial.X false)
  arrayFold (fun _ => word) word word (MvPolynomial.X true)
    (fun _ _ _ _ => True) (fun _ _ _ value => value)

theorem lastWord_realizable : lastWord.Realizable := by
  apply arrayFold_total_realizable
  exact (Computation.copy_realizable (EncodedDomain.bitVectors (MvPolynomial.X false))).withArguments _
    ⟨(fun _ => Sum.inr true), by intro first second _; cases first; cases second; rfl⟩ (fun _ => rfl)

example : lastWord.TM0Realizable := lastWord_realizable.tm0

example (sizes : Bool → ℕ) (arguments : lastWord.Arguments sizes)
    (empty : sizes true = 0) :
    lastWord.compute sizes ⟨arguments, trivial⟩ = arguments (.inr false) := by
  simp [lastWord, arrayFold, ArrayFold.prefixValue, empty]

/-- Each logical iteration toggles, although its private token has zero bits. -/
noncomputable def toggle : Polytime2.Computation Bool (Empty ⊕ Unit) :=
  boundedIteration Empty.elim booleans (MvPolynomial.X true)
    (fun _ _ _ => True) (fun _ _ value => !value)

theorem toggle_realizable : toggle.Realizable := by
  refine boundedIteration_realizable Empty.elim booleans (MvPolynomial.X true)
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ value => !value)
    ?_ (fun _ _ _ _ _ => True) ?_ ?_ ?_
  · exact ((finitePredicate_realizable EncodedDomain.booleans
      (fun _ value => !value)).withConstantSizes (Parameter := Bool)).withArguments _
      ⟨Sum.inr, Sum.inr_injective⟩ (fun _ => rfl)
  · intros; trivial
  · intros; trivial
  · intros; trivial

example : toggle.TM0Realizable := toggle_realizable.tm0

example : toggle.compute (fun _ => 0) ⟨(fun name => match name with
    | .inl impossible => nomatch impossible
    | .inr _ => false), trivial⟩ = false := by
  simp [toggle, boundedIteration]

example : toggle.compute (fun _ => 3) ⟨(fun name => match name with
    | .inl impossible => nomatch impossible
    | .inr _ => false), trivial⟩ = true := by
  simp [toggle, boundedIteration, Function.iterate_succ_apply']

private def previous (sizes : Bool → ℕ) (value : Fin (2 ^ sizes false)) : Fin (2 ^ sizes false) :=
  ⟨value.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) value.isLt⟩

/-- A partial update is permitted by an indexed invariant, with no cost proof. -/
noncomputable def countdown : Polytime2.Computation Bool (Empty ⊕ Unit) :=
  boundedIteration Empty.elim (EncodedDomain.binaryNaturals false) (MvPolynomial.X true)
    (fun sizes _ value => value.val = sizes true) (fun sizes _ value => previous sizes value)

theorem countdown_realizable : countdown.Realizable := by
  refine boundedIteration_realizable Empty.elim (EncodedDomain.binaryNaturals false) (MvPolynomial.X true)
    (fun sizes _ value => value.val = sizes true) (fun _ _ value => 0 < value.val)
    (fun sizes _ value => previous sizes value) ?_
    (fun _ _ initial index value => value.val + index = initial.val) ?_ ?_ ?_
  · exact (counterDecrement_realizable false).withArguments _
      ⟨Sum.inr, Sum.inr_injective⟩ (fun _ => rfl)
  · intro sizes values initial valid; simp
  · intro sizes values initial valid index bounded value good
    simp only [MvPolynomial.eval_X] at bounded
    omega
  · intro sizes values initial valid index bounded value good
    simp only [MvPolynomial.eval_X] at bounded
    change value.val - 1 + (index + 1) = initial.val
    omega

/-- Final correctness uses only the mathematical invariant, independently of
realizability, tape encodings, and the private traversal counter. -/
theorem countdown_correct (sizes : Bool → ℕ) (arguments : countdown.Arguments sizes)
    (valid : countdown.precondition sizes arguments) :
    (countdown.compute sizes ⟨arguments, valid⟩).val = 0 := by
  have good := boundedIteration_invariant Empty.elim (EncodedDomain.binaryNaturals false)
    (MvPolynomial.X true) (fun sizes _ value => value.val = sizes true)
    (fun sizes _ value => previous sizes value) sizes ⟨arguments, valid⟩
    (fun index value => value.val + index = (arguments (.inr ())).val) (by simp)
    (by
      intro index bounded value good
      simp only [MvPolynomial.eval_X] at bounded
      change value.val - 1 + (index + 1) = (arguments (.inr ())).val
      change (arguments (.inr ())).val = sizes true at valid
      omega)
  simp only [MvPolynomial.eval_X] at good
  change (arguments (.inr ())).val = sizes true at valid
  change (countdown.compute sizes ⟨arguments, valid⟩).val + sizes true = _ at good
  omega

/-- Accumulators themselves may have zero width. -/
example : (arrayFold (Parameter := Bool) Empty.elim booleans (EncodedDomain.unaryOfLength 0)
    (MvPolynomial.X true) (fun _ _ _ _ => True) (fun _ _ value _ => value)).Realizable := by
  apply arrayFold_total_realizable
  exact (Computation.copy_realizable (EncodedDomain.unaryOfLength 0)).withArguments _
    ⟨(fun _ => Sum.inr false), by intro first second _; cases first; cases second; rfl⟩ (fun _ => rfl)

end Polytime2.Examples.Fold
