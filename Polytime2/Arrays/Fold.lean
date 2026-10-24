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

import Polytime2.Computation.Width
import Polytime2.Computation.Realizable
import Polytime2.Encoding.EncodedArray
import Polytime2.Machine.CallingConventionWhile
import Polytime2.Primitives.UnaryCopy
import Polytime2.Primitives.UnaryMove
import Polytime2.Primitives.TapeCommands

/-! # Public array folds over certified mathematical updates

The number of elements and the element and accumulator widths may depend on
sizes. A private unary cursor controls traversal; no binary capacity parameter
or physical loop counter is part of the public computation.
-/

namespace Polytime2.Computation

variable {Parameter Context : Type} [Fintype Parameter] [Fintype Context]

/-- A partial update receives its mathematical admissibility proof. The input
domains and output codec are the same as for `arrayFoldStep`. -/
noncomputable def arrayFoldPartialStep (context : Context → EncodedDomain Parameter)
    (element accumulator : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (step : ∀ sizes values state token, allowed sizes values state token → accumulator.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun name => if name then element else accumulator)
  outputDomain := accumulator
  precondition sizes arguments := allowed sizes (fun name => arguments (.inl name))
    (arguments (.inr false)) (arguments (.inr true))
  compute sizes arguments := step sizes (fun name => arguments.val (.inl name))
    (arguments.val (.inr false)) (arguments.val (.inr true)) arguments.property

/-- The update receives immutable context, the accumulator, and one element. -/
noncomputable def arrayFoldStep (context : Context → EncodedDomain Parameter)
    (element accumulator : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) :=
  arrayFoldPartialStep context element accumulator allowed (fun sizes values state token _valid =>
    update sizes values state token)

namespace ArrayFold

/-- Extend a partial mathematical update by retaining the current state outside
its domain. The fold invariant, rather than a runtime test, supplies `allowed`.
For every state and element satisfying `allowed`, the result is exactly `step`.
-/
noncomputable def extend {State Element : Type} (allowed : State → Element → Prop)
    (step : ∀ state element, allowed state element → State) (state : State) (element : Element) : State := by
  classical
  exact if valid : allowed state element then step state element valid else state

@[simp] theorem extend_of_allowed {State Element : Type} {allowed : State → Element → Prop}
    {step : ∀ state element, allowed state element → State} {state : State} {element : Element}
    (valid : allowed state element) : extend allowed step state element = step state element valid := by
  classical
  exact dite_eq_left valid

/-- The accumulator after a prefix of a mathematical array. -/
def prefixValue {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Element → Accumulator) (array : Fin length → Element)
    (initial : Accumulator) (count : ℕ) : Accumulator :=
  ((List.ofFn array).take count).foldl update initial

@[simp] theorem prefix_zero {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Element → Accumulator) (array : Fin length → Element) (initial : Accumulator) :
    prefixValue update array initial 0 = initial := by simp [prefixValue]

theorem prefix_succ {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Element → Accumulator) (array : Fin length → Element)
    (initial : Accumulator) (index : Fin length) :
    prefixValue update array initial (index.val + 1) = update (prefixValue update array initial index.val) (array index) := by
  unfold prefixValue
  rw [List.take_succ_eq_append_getElem (l := List.ofFn array) (i := index.val) (by simp)]
  simp

/-- The invariant proof is independent of all tape and cost representations. -/
theorem prefix_invariant {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Element → Accumulator) (array : Fin length → Element) (initial : Accumulator)
    (invariant : ℕ → Accumulator → Prop) (starts : invariant 0 initial)
    (preserves : ∀ index : Fin length, ∀ value, invariant index.val value →
      invariant (index.val + 1) (update value (array index)))
    (count : ℕ := length) (bounded : count ≤ length := by omega) :
    invariant count (prefixValue update array initial count) := by
  induction count with
  | zero => simpa using starts
  | succ count hypothesis =>
    rw [prefix_succ update array initial ⟨count, by omega⟩]
    exact preserves ⟨count, by omega⟩ _ (hypothesis (by omega))

/-- A constant array supplies a bounded number of logical update steps. -/
theorem prefix_constant {Element Accumulator : Type} {length : ℕ}
    (update : Accumulator → Accumulator) (token : Element) (initial : Accumulator)
    (count : ℕ) (bounded : count ≤ length) :
    prefixValue (fun value _ => update value) (fun _ : Fin length => token) initial count =
      update^[count] initial := by
  induction count with
  | zero => simp
  | succ count hypothesis =>
    rw [prefix_succ _ _ _ ⟨count, by omega⟩, hypothesis (by omega),
      Function.iterate_succ_apply']

end ArrayFold

/-- A certified partial update realizes its total extension on admissible
steps. No decision procedure for the logical precondition is required. -/
theorem arrayFoldStep_of_partial_realizable
    (context : Context → EncodedDomain Parameter) (element accumulator : EncodedDomain Parameter)
    (allowed : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → Prop)
    (step : ∀ sizes values state token, allowed sizes values state token → accumulator.Carrier sizes)
    (ready : (arrayFoldPartialStep context element accumulator allowed step).Realizable) :
    (arrayFoldStep context element accumulator allowed
      (fun sizes values => ArrayFold.extend (allowed sizes values) (step sizes values))).Realizable := by
  apply ready.withSpecification _ _ (by intros; assumption)
  intro sizes arguments valid
  exact (ArrayFold.extend_of_allowed valid).symm

/-- Initial accumulator and immutable array are separate inputs, after context. -/
noncomputable def arrayFold (context : Context → EncodedDomain Parameter)
    (element accumulator : EncodedDomain Parameter) (length : MvPolynomial Parameter ℕ)
    (admissible : ∀ sizes, (∀ name, (context name).Carrier sizes) →
      (element.arrayOfLength length).Carrier sizes → accumulator.Carrier sizes → Prop)
    (update : ∀ sizes, (∀ name, (context name).Carrier sizes) → accumulator.Carrier sizes → element.Carrier sizes → accumulator.Carrier sizes) :
    Computation Parameter (Context ⊕ Bool) where
  inputDomains := Sum.elim context (fun name => if name then element.arrayOfLength length else accumulator)
  outputDomain := accumulator
  precondition sizes arguments := admissible sizes (fun name => arguments (.inl name))
    (arguments (.inr true)) (arguments (.inr false))
  compute sizes arguments := ArrayFold.prefixValue (update sizes (fun name => arguments.val (.inl name)))
    (arguments.val (.inr true)) (arguments.val (.inr false)) (MvPolynomial.eval sizes length)

namespace Realizable.Internal.ArrayFold

open MultiTape CallingConvention
open Binary (Symbol word)

/-- Proof-only cursor positions do not introduce a tape representation layer. -/
def cursor (bits : List Bool) (offset : ℕ) : Turing.Tape Symbol :=
  (Turing.Tape.move .right)^[offset] (buffer (word bits))

@[simp] theorem cursor_zero (bits : List Bool) : cursor bits 0 = buffer (word bits) := rfl

theorem cursor_nth (bits : List Bool) (offset : ℕ) (index : ℤ) :
    (cursor bits offset).nth index = (buffer (word bits)).nth (index + offset) := by
  induction offset generalizing index with
  | zero => simp [cursor]
  | succ offset hypothesis =>
    simp only [cursor, Function.iterate_succ_apply', Turing.Tape.move_right_nth]
    change (cursor bits offset).nth (index + 1) = _
    rw [hypothesis]
    congr 1
    push_cast
    ring

theorem cursor_advance (bits : List Bool) (offset count : ℕ) :
    (Turing.Tape.move .right)^[count] (cursor bits offset) = cursor bits (offset + count) := by
  simp only [cursor, Nat.add_comm offset count, Function.iterate_add_apply]

theorem cursor_split (before after : List Bool) :
    cursor (before ++ after) before.length = Binary.tape (word before.reverse ++ [0]) (word after ++ [0]) () := by
  unfold cursor
  rw [← buffer_padding (word (before ++ after))]
  have moved := Move.right_list (word before) [0] (word after ++ [0])
  simpa [word, List.append_assoc, Binary.tape] using moved

theorem cursor_end (bits : List Bool) :
    cursor bits bits.length = Binary.tape (word bits.reverse ++ [0]) [0] () := by
  simpa [word] using cursor_split bits []

theorem cursor_blank (bits : List Bool) (offset : ℕ) :
    (cursor bits offset).head = 0 ↔ bits.length ≤ offset := by
  unfold cursor
  rw [Turing.Tape.move_right_n_head, ← buffer_padding (word bits)]
  have nonnegative : ¬(offset : ℤ) < 0 := by omega
  simpa [nonnegative] using word_nth_blank_iff bits (offset : ℤ)

end Realizable.Internal.ArrayFold

end Polytime2.Computation
