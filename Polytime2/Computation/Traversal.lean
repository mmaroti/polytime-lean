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
import Polytime2.Primitives.BitOperations
import Polytime2.Computation.Composition
import Polytime2.Computation.Reindex

/-! # Bounded iteration with private traversal storage -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- One update receives immutable context and the current mathematical state. -/
noncomputable def iterationStep (context : Context → EncodedDomain.{0, 0} Parameter)
    (state : EncodedDomain.{0, 0} Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → state.Carrier sizes) :
    Computation Parameter (Context ⊕ Unit) where
  inputDomains := Sum.elim context (fun _ => state)
  outputDomain := state
  precondition sizes arguments := allowed sizes (fun name => arguments (.inl name)) (arguments (.inr ()))
  compute sizes arguments := update sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ()))

/-- The iteration count is a fixed polynomial in sizes, with no public counter. -/
noncomputable def boundedIteration (context : Context → EncodedDomain.{0, 0} Parameter)
    (state : EncodedDomain.{0, 0} Parameter) (length : MvPolynomial Parameter ℕ)
    (admissible : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → state.Carrier sizes) :
    Computation Parameter (Context ⊕ Unit) where
  inputDomains := Sum.elim context (fun _ => state)
  outputDomain := state
  precondition sizes arguments := admissible sizes (fun name => arguments (.inl name)) (arguments (.inr ()))
  compute sizes arguments := (update sizes (fun name => arguments.val (.inl name)))^[MvPolynomial.eval sizes length]
    (arguments.val (.inr ()))

/-- Prove a final-answer property by induction on the mathematical iterations.
The private traversal array and all implementation details remain hidden. -/
theorem boundedIteration_invariant
    (context : Context → EncodedDomain.{0, 0} Parameter) (state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (admissible : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → state.Carrier sizes)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (boundedIteration context state length admissible update).Arguments sizes //
      (boundedIteration context state length admissible update).precondition sizes arguments})
    (invariant : ℕ → state.Carrier sizes → Prop)
    (starts : invariant 0 (arguments.val (.inr ())))
    (preserves : ∀ index < MvPolynomial.eval sizes length, ∀ value,
      invariant index value → invariant (index + 1) (update sizes (fun name => arguments.val (.inl name)) value)) :
    invariant (MvPolynomial.eval sizes length)
      ((boundedIteration context state length admissible update).compute sizes arguments) := by
  let advance := update sizes (fun name => arguments.val (.inl name))
  have iterated : ∀ count, count ≤ MvPolynomial.eval sizes length →
      invariant count (advance^[count] (arguments.val (.inr ()))) := by
    intro count bounded
    induction count with
    | zero => exact starts
    | succ count hypothesis =>
      rw [Function.iterate_succ_apply']
      exact preserves count (by omega) _ (hypothesis (by omega))
  exact iterated _ le_rfl

/-- Private zero-bit elements distinguish logical iterations even at zero width.
Applications supply only a certified update and its mathematical invariant. -/
theorem boundedIteration_realizable
    (context : Context → EncodedDomain.{0, 0} Parameter) (state : EncodedDomain.{0, 0} Parameter)
    (length : MvPolynomial Parameter ℕ)
    (admissible allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → state.Carrier sizes)
    (stepRealizable : (iterationStep context state allowed update).Realizable)
    (invariant : ∀ sizes, (∀ name, (context name).Carrier sizes) → state.Carrier sizes → ℕ → state.Carrier sizes → Prop)
    (starts : ∀ sizes values initial, admissible sizes values initial → invariant sizes values initial 0 initial)
    (permits : ∀ sizes values initial, admissible sizes values initial →
      ∀ index < MvPolynomial.eval sizes length, ∀ value,
        invariant sizes values initial index value → allowed sizes values value)
    (preserves : ∀ sizes values initial, admissible sizes values initial →
      ∀ index < MvPolynomial.eval sizes length, ∀ value,
        invariant sizes values initial index value → invariant sizes values initial (index + 1) (update sizes values value)) :
    (boundedIteration context state length admissible update).Realizable := by
  classical
  let computation := boundedIteration context state length admissible update
  let token : EncodedDomain.{0, 0} Parameter := EncodedDomain.unaryOfLength 0
  let step := arrayFoldStep context token state (fun sizes values value _ => allowed sizes values value)
    (fun sizes values value _ => update sizes values value)
  let selection : Context ⊕ Unit ↪ Context ⊕ Bool :=
    (Function.Embedding.refl Context).sumMap ⟨fun _ => false, by intro first second _; cases first; cases second; rfl⟩
  have stepReady : step.Realizable := stepRealizable.withArguments step.inputDomains selection (by
    rintro (name | name) <;> rfl)
  have folded := arrayFold_realizable (Parameter := Parameter) (Context := Context)
    (context := context) (element := token) (accumulator := state) (length := length)
    (fun sizes values _ initial => admissible sizes values initial)
    (fun sizes values value _ => update sizes values value)
    (fun sizes values value _ => allowed sizes values value) stepReady
    (fun sizes values _ initial index value => invariant sizes values initial index value)
    (by intro sizes values array initial valid; exact starts sizes values initial valid)
    (by intro sizes values array initial valid index value good; exact permits sizes values initial valid index.val index.isLt value good)
    (by intro sizes values array initial valid index value good; exact preserves sizes values initial valid index.val index.isLt value good)
  have allocated := (zeroBits_realizable (0 : MvPolynomial Parameter ℕ)).withArguments computation.inputDomains
    ⟨Empty.elim, by intro name; exact name.elim⟩ (by intro name; exact name.elim)
  have allocated := allocated.withPrecondition computation.precondition (by intros; trivial)
  have generated := allocated.withEncodedOutput (token.arrayOfLength length)
    (fun _ _ _ => PUnit.unit) (by intro sizes; simp [token, EncodedDomain.arrayOfLength, EncodedDomain.unaryOfLength,
      withPrecondition, withArguments, zeroBits, EncodedDomain.bitVectors]) (by
      intro sizes arguments
      apply CallingConvention.tape_eq_of_nth
      intro index
      simp [CallingConvention.encoded, CallingConvention.tape, token, EncodedDomain.arrayOfLength,
        EncodedDomain.ofCodec, EncodedDomain.unaryOfLength, EncodedDomain.ArrayEncoding.bits,
        withPrecondition, withArguments, zeroBits])
  let continuationDomains : (Context ⊕ Unit) ⊕ Unit → EncodedDomain.{0, 0} Parameter :=
    Sum.elim computation.inputDomains (fun _ => token.arrayOfLength length)
  let placement : Context ⊕ Bool ↪ (Context ⊕ Unit) ⊕ Unit :=
    ⟨(fun name => match name with
      | .inl name => .inl (.inl name)
      | .inr false => .inl (.inr ())
      | .inr true => .inr ()), by
      rintro (first | first) (second | second) equal
      all_goals try cases first
      all_goals try cases second
      all_goals simp_all⟩
  have continuation := folded.withArguments continuationDomains placement (by
    rintro (name | choice) <;> first | rfl | (cases choice <;> rfl))
  have combined := generated.letThen continuation (fun _ => rfl) rfl (by intros; assumption)
  exact combined.withSpecification computation.precondition computation.compute (by intros; assumption) (by
    intro sizes arguments valid
    exact ArrayFold.prefix_constant (update sizes (fun name => arguments (.inl name))) PUnit.unit
      (arguments (.inr ())) _ le_rfl)

end Polytime2.Computation
