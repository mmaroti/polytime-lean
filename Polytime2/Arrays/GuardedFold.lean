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

import Polytime2.Arrays.FoldContract
import Polytime2.Computation.Records
import Polytime2.Computation.Conditional

/-! # Certified selection guards for array-fold updates

Internal tokens pair a selection flag with an ordinary mathematical element.
Only selected tokens need the update precondition. Unselected tokens retain
the accumulator, allowing runtime prefixes inside fixed-length traversals.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

/-- A guarded fixed-length traversal has processed exactly the selected prefix. -/
theorem ArrayFold.prefix_guarded {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Element → Accumulator) (array : Fin length → Element)
    (initial : Accumulator) (count visited : ℕ) (within : visited ≤ length) :
    prefixValue (fun value (token : Bool × Element) => if token.1 then update value token.2 else value)
      (fun index => (decide (index.val < count), array index)) initial visited =
      prefixValue update array initial (min visited count) := by
  apply prefix_invariant _ _ initial
    (fun visited value => value = prefixValue update array initial (min visited count)) ?_ ?_ visited within
  · simp
  · intro index value previous
    rw [previous]
    by_cases before : index.val < count
    · have first : index.val ≤ count := by omega
      have next : index.val + 1 ≤ count := by omega
      simpa only [Nat.min_eq_left first, Nat.min_eq_left next, before, decide_true, ite_true] using
        (prefix_succ update array initial index).symm
    · have first : count ≤ index.val := by omega
      have next : count ≤ index.val + 1 := by omega
      simp only [Nat.min_eq_right first, Nat.min_eq_right next, before, decide_false, Bool.false_eq_true, ite_false]

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- Only selected elements must satisfy the underlying update contract. -/
def arrayFoldGuardedAllowed (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (sizes : Parameter → ℕ) (values : ∀ name, (context name).Carrier sizes)
    (state : accumulator.Carrier sizes) (token : (booleans.prod element).Carrier sizes) :=
  token.1 = true → allowed sizes values state token.2

/-- Selection changes traversal, while retaining the ordinary accumulator and element carriers. -/
def arrayFoldGuardedUpdate (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes)
    (sizes : Parameter → ℕ) (values : ∀ name, (context name).Carrier sizes)
    (state : accumulator.Carrier sizes) (token : (booleans.prod element).Carrier sizes) : accumulator.Carrier sizes :=
  match (token.1 : Bool) with
  | true => update sizes values state token.2
  | false => state

/-- Guarding a certified update accounts for selecting tokens and copying unselected states. -/
theorem arrayFoldGuardedUpdate_realizable (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes)
    (step : (arrayFoldStep context element accumulator allowed update).Realizable) :
    (arrayFoldStep context (booleans.prod element) accumulator
      (arrayFoldGuardedAllowed context element accumulator allowed)
      (arrayFoldGuardedUpdate context element accumulator update)).Realizable := by
  let computation := arrayFoldStep context (booleans.prod element) accumulator
    (arrayFoldGuardedAllowed context element accumulator allowed) (arrayFoldGuardedUpdate context element accumulator update)
  let condition (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) := (arguments (.inr true)).1
  apply Realizable.ofCases condition ((Realizable.argument computation.inputDomains (.inr true) computation.precondition).fst)
  · let selected sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    have applied := step.onResults computation.inputDomains selected
      (fun name _ arguments => match name with
        | .inl name => arguments.val (.inl name)
        | .inr false => arguments.val (.inr false)
        | .inr true => (arguments.val (.inr true)).2)
      (by intro sizes arguments; exact arguments.property.1 arguments.property.2) (by
        intro name
        rcases name with name | choice
        · exact Realizable.argument computation.inputDomains (.inl name) selected
        · cases choice
          · exact Realizable.argument computation.inputDomains (.inr false) selected
          · exact (Realizable.argument computation.inputDomains (.inr true) selected).snd)
    apply applied.withSpecification selected _ (by intros; assumption)
    intro sizes arguments valid
    have active : (arguments (.inr true)).1 = true := valid.2
    simp [computation, arrayFoldStep, arrayFoldPartialStep, Computation.onResults, arrayFoldGuardedUpdate, active]
  · let skipped sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have copied := Realizable.argument computation.inputDomains (.inr false) skipped
    apply copied.withSpecification skipped _ (by intros; assumption)
    intro sizes arguments valid
    have inactive : (arguments (.inr true)).1 = false := valid.2
    simp [computation, arrayFoldStep, arrayFoldPartialStep, arrayFoldGuardedUpdate, inactive]

end Polytime2.Computation
