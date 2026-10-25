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

import Polytime2.Matrices.IntegerMultiply
import Polytime2.Arithmetic.SignedMultiplyAdd
import Polytime2.Arrays.Fold
import Polytime2.Arrays.Indices

/-! # Fixed-width integer dot products

Two bounded integer arrays have the same mathematical length and independent
entry widths. Their dot product fits length plus both widths. The fold retains
that fixed bound at every prefix, including the empty prefix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def dotContext (length leftWidth rightWidth : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter :=
  fun choice => (binaryIntegers (if choice then rightWidth else leftWidth)).arrayOfLength length

private noncomputable def dotAccumulator (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  binaryIntegers (length + leftWidth + rightWidth)

private def dotFits (length leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (dotContext length leftWidth rightWidth name).Carrier sizes)
    (value : (dotAccumulator length leftWidth rightWidth).Carrier sizes) (index : (arrayPosition length).Carrier sizes) : Prop :=
  (value.val + (context false index).val * (context true index).val).natAbs <
    2 ^ MvPolynomial.eval sizes (length + leftWidth + rightWidth)

private noncomputable def dotUpdate (length leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (dotContext length leftWidth rightWidth name).Carrier sizes)
    (value : (dotAccumulator length leftWidth rightWidth).Carrier sizes) (index : (arrayPosition length).Carrier sizes) :=
  ArrayFold.extend (dotFits length leftWidth rightWidth sizes context)
    (fun value index valid => ⟨value.val + (context false index).val * (context true index).val, valid⟩) value index

private theorem dotUpdate_realizable (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (dotContext length leftWidth rightWidth) (arrayPosition length)
      (dotAccumulator length leftWidth rightWidth) (dotFits length leftWidth rightWidth)
      (dotUpdate length leftWidth rightWidth)).Realizable := by
  apply arrayFoldStep_of_partial_realizable
  let computation := arrayFoldStep (dotContext length leftWidth rightWidth) (arrayPosition length)
    (dotAccumulator length leftWidth rightWidth) (dotFits length leftWidth rightWidth)
    (dotUpdate length leftWidth rightWidth)
  let capacity := length + leftWidth + rightWidth
  have lookup (choice : Bool) := (arrayLookupWithIndex_realizable
    (binaryIntegers (if choice then rightWidth else leftWidth)) (arrayPosition length)
    (fun _ index => index.val) (arrayPosition_value length) length).onArguments computation.inputDomains computation.precondition
      (fun name => match name with
      | false => (.inr true)
      | true => (.inl choice)) (by intro name; cases name <;> rfl) (by intro sizes arguments; exact (arguments.val (.inr true)).isLt)
  have left := (lookup false).followedBy (integerWidenTo_realizable leftWidth (length + rightWidth) capacity (by dsimp [capacity]; ring))
    rfl (by intros; trivial)
  have right := (lookup true).followedBy (integerWidenTo_realizable rightWidth (length + leftWidth) capacity (by dsimp [capacity]; ring))
    rfl (by intros; trivial)
  have arithmetic := (integerMultiplyAdd_realizable capacity).onResults computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
      | 0 => arguments.val (.inr false)
      | 1 => ⟨(arguments.val (.inl false) (arguments.val (.inr true))).val,
          ((integerWidenTo leftWidth (length + rightWidth) capacity (by dsimp [capacity]; ring)).compute sizes
            ⟨fun _ => arguments.val (.inl false) (arguments.val (.inr true)), trivial⟩).property⟩
      | 2 => ⟨(arguments.val (.inl true) (arguments.val (.inr true))).val,
          ((integerWidenTo rightWidth (length + leftWidth) capacity (by dsimp [capacity]; ring)).compute sizes
            ⟨fun _ => arguments.val (.inl true) (arguments.val (.inr true)), trivial⟩).property⟩)
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains (.inr false) computation.precondition
      · exact left
      · exact right)
  exact arithmetic.followedBy
    (integerNarrowAtWidths_realizable (2 * capacity + 1) capacity (by intro sizes; simp only [map_add, map_mul, map_one, MvPolynomial.eval_ofNat]; omega))
    rfl (by intro sizes arguments valid; exact valid)

private def dotPrefix {length : ℕ} (left right : Fin length → ℤ) (count : ℕ) : ℤ :=
  ∑ index ∈ Finset.univ.filter (fun index => index.val < count), left index * right index

private theorem dotPrefix_succ {length : ℕ} (left right : Fin length → ℤ) (index : Fin length) :
    dotPrefix left right (index.val + 1) = dotPrefix left right index.val + left index * right index := by
  have indices : Finset.univ.filter (fun candidate : Fin length => candidate.val < index.val + 1) =
      insert index (Finset.univ.filter (fun candidate => candidate.val < index.val)) := by
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold dotPrefix
  rw [indices, Finset.sum_insert (by simp)]
  exact add_comm _ _

private theorem dotPrefix_bound (length leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (dotContext length leftWidth rightWidth name).Carrier sizes) (count : ℕ) :
    (dotPrefix (fun index => (context false index).val) (fun index => (context true index).val) count).natAbs <
      2 ^ MvPolynomial.eval sizes (length + leftWidth + rightWidth) := by
  simpa only [map_add, dotPrefix] using IntegerMatrix.partial_dotProduct_bound
    (MvPolynomial.eval sizes leftWidth) (MvPolynomial.eval sizes rightWidth)
    (fun index => (context false index).val) (fun index => (context true index).val)
    (Finset.univ.filter (fun index => index.val < count))
    (fun index => (context false index).property) (fun index => (context true index).property)

private theorem dotUpdate_prefix (length leftWidth rightWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (dotContext length leftWidth rightWidth name).Carrier sizes)
    (index : Fin (MvPolynomial.eval sizes length)) (value : (dotAccumulator length leftWidth rightWidth).Carrier sizes)
    (before : value.val = dotPrefix (fun index => (context false index).val)
      (fun index => (context true index).val) index.val) :
    (dotUpdate length leftWidth rightWidth sizes context value index).val =
      dotPrefix (fun index => (context false index).val) (fun index => (context true index).val) (index.val + 1) := by
  classical
  have fits : dotFits length leftWidth rightWidth sizes context value index := by
    change (value.val + (context false index).val * (context true index).val).natAbs < _
    rw [before, ← dotPrefix_succ]
    exact dotPrefix_bound length leftWidth rightWidth sizes context (index.val + 1)
  simp only [dotUpdate, ArrayFold.extend_of_allowed fits]
  rw [before, dotPrefix_succ]

private noncomputable def dotFold (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :=
  arrayFold (dotContext length leftWidth rightWidth) (arrayPosition length)
    (dotAccumulator length leftWidth rightWidth) length
    (fun _ _ tokens initial => tokens = id ∧ initial.val = 0) (dotUpdate length leftWidth rightWidth)

private theorem dotFold_realizable (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (dotFold length leftWidth rightWidth).Realizable := by
  classical
  apply arrayFold_realizable (dotContext length leftWidth rightWidth) (arrayPosition length)
    (dotAccumulator length leftWidth rightWidth) length
    (fun _ _ tokens initial => tokens = id ∧ initial.val = 0) (dotUpdate length leftWidth rightWidth)
    (dotFits length leftWidth rightWidth) (dotUpdate_realizable length leftWidth rightWidth)
    (fun _ context _ _ count value => value.val =
      dotPrefix (fun index => (context false index).val) (fun index => (context true index).val) count)
  · intro sizes context tokens initial valid
    simpa [dotPrefix] using valid.2
  · intro sizes context tokens initial valid index value before
    rw [valid.1]
    change (value.val + (context false index).val * (context true index).val).natAbs < _
    rw [before, ← dotPrefix_succ]
    exact dotPrefix_bound length leftWidth rightWidth sizes context (index.val + 1)
  · intro sizes context tokens initial valid index value before
    rw [valid.1]
    exact dotUpdate_prefix length leftWidth rightWidth sizes context index value before

/-- Dot product of two arrays at independent entry widths, with derived output storage. -/
private noncomputable def implementation (length leftWidth rightWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (dotFold length leftWidth rightWidth).onResults (dotContext length leftWidth rightWidth) (fun _ _ => True)
    (fun name _ arguments => match name with
      | .inl choice => arguments.val choice
      | .inr false => ⟨0, by simp⟩
      | .inr true => id) (by intros; exact ⟨rfl, rfl⟩)

/-- Canonical positions, zero initialization, and the complete fixed-width fold are realized. -/
private theorem implementation_realizable (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (implementation length leftWidth rightWidth).Realizable := by
  apply (dotFold_realizable length leftWidth rightWidth).onResults
    (dotContext length leftWidth rightWidth) (fun _ _ => True) _ (by intros; exact ⟨rfl, rfl⟩)
  intro name
  rcases name with choice | choice
  · exact Realizable.argument _ choice (fun _ _ => True)
  · cases choice
    · let capacity := length + leftWidth + rightWidth
      have zero := ((integerBooleanOperation_realizable (Parameter := Parameter) (Argument := Empty)
        (fun _ => ⟨0, by decide⟩)).followedBy
        (integerWidenTo_realizable 1 capacity (capacity + 1) (by ring)) rfl (by intros; trivial)).followedBy
        (integerNarrowAtWidths_realizable (capacity + 1) capacity (by intro sizes; simp)) rfl (by
          intro sizes arguments valid
          change (0 : ℤ).natAbs < 2 ^ MvPolynomial.eval sizes capacity
          simp)
      exact zero.onResults _ _ (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)
    · exact (arrayPositions_realizable length).onResults _ _
        (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)

/-- The realized fold returns the ordinary finite dot product. -/
private theorem implementation_correct (length leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (implementation length leftWidth rightWidth).Arguments sizes //
      (implementation length leftWidth rightWidth).precondition sizes arguments}) :
    ((implementation length leftWidth rightWidth).compute sizes arguments).val =
      ∑ index, (arguments.val false index).val * (arguments.val true index).val := by
  let initial : (dotAccumulator length leftWidth rightWidth).Carrier sizes := ⟨0, by simp⟩
  have result := ArrayFold.prefix_invariant
    (dotUpdate length leftWidth rightWidth sizes arguments.val)
    (id : Fin (MvPolynomial.eval sizes length) → Fin (MvPolynomial.eval sizes length)) initial
    (fun count value => value.val = dotPrefix (fun index => (arguments.val false index).val)
      (fun index => (arguments.val true index).val) count)
    (by simp [initial, dotPrefix])
    (fun index value before => dotUpdate_prefix length leftWidth rightWidth sizes arguments.val index value before)
  have all : Finset.univ.filter (fun index : Fin (MvPolynomial.eval sizes length) =>
      index.val < MvPolynomial.eval sizes length) = Finset.univ := by
    ext index
    simp
  change (ArrayFold.prefixValue (dotUpdate length leftWidth rightWidth sizes arguments.val)
    id initial (MvPolynomial.eval sizes length)).val = _
  simpa only [dotPrefix, all] using result

/-- The ordinary finite integer dot product, with its exact derived bound.
The public answer contains no positions, initial accumulator, or fold. -/
noncomputable def integerDotProduct (length leftWidth rightWidth : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  specification (dotContext length leftWidth rightWidth) (dotAccumulator length leftWidth rightWidth)
    (fun _ _ => True) (fun sizes arguments =>
      ⟨∑ index, (arguments.val false index).val * (arguments.val true index).val, by
        simpa only [map_add] using IntegerMatrix.partial_dotProduct_bound
          (MvPolynomial.eval sizes leftWidth) (MvPolynomial.eval sizes rightWidth)
          (fun index => (arguments.val false index).val) (fun index => (arguments.val true index).val)
          Finset.univ (fun index => (arguments.val false index).property)
          (fun index => (arguments.val true index).property)⟩)

/-- The private fixed-workspace fold certifies the mathematical sum. -/
theorem integerDotProduct_realizable (length leftWidth rightWidth : MvPolynomial Parameter ℕ) :
    (integerDotProduct length leftWidth rightWidth).Realizable := by
  apply (implementation_realizable length leftWidth rightWidth).specification
  intro sizes arguments valid
  apply Subtype.ext
  exact implementation_correct length leftWidth rightWidth sizes ⟨arguments, valid⟩

/-- Evaluate the mathematical sum without exposing its traversal. -/
theorem integerDotProduct_correct (length leftWidth rightWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerDotProduct length leftWidth rightWidth).Arguments sizes //
      (integerDotProduct length leftWidth rightWidth).precondition sizes arguments}) :
    ((integerDotProduct length leftWidth rightWidth).compute sizes arguments).val =
      ∑ index, (arguments.val false index).val * (arguments.val true index).val := by
  simp only [integerDotProduct, specification_compute]

end Polytime2.Computation
