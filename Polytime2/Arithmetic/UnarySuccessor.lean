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

import Polytime2.Arrays.Snoc
import Polytime2.Arrays.Indices
import Polytime2.Arrays.PackingCount

/-! # Successor of a bounded unary rank

Increment a count strictly below its capacity. Reuse the unary word's prefix
flags, append one accepted flag, count with the existing packing algorithm,
and remove the final unused unary bit. No new scanning machine is needed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def flags (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (boundedUnary capacity) (booleans.arrayOfLength capacity)
    (fun _ count index => decide (index.val < count.val))

private theorem flags_realizable (capacity : MvPolynomial Parameter ℕ) : (flags capacity).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [EncodedDomain.width, booleans, arrayOfLength, ofCodec, boundedUnary, fixed,
      show Nat.clog 2 2 = 1 by decide]
  · intro sizes count
    rw [FirstFalse.boolean_bits]
    change ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes capacity) count) =
      List.ofFn (fun index : Fin (MvPolynomial.eval sizes capacity) => decide (index.val < count.val))
    rw [BoundedUnary.encode_bits]
    exact (ArrayPacking.unary_ofFn (Nat.le_of_lt_succ count.isLt)).symm

private noncomputable def narrow (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (boundedUnary (capacity + 1)) (boundedUnary capacity)
    (fun sizes count => count.val ≤ MvPolynomial.eval sizes capacity)
    (fun _ count => ⟨count.val.val, Nat.lt_succ_of_le count.property⟩)

private theorem narrow_realizable (capacity : MvPolynomial Parameter ℕ) : (narrow capacity).Realizable := by
  apply Realizable.Internal.fieldProjection (boundedUnary (capacity + 1)) (boundedUnary capacity) 0
  intro sizes count
  refine ⟨[], [false], ?_, by simp⟩
  change ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes (capacity + 1)) count.val) =
    [] ++ ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes capacity)
      ⟨count.val.val, Nat.lt_succ_of_le count.property⟩) ++ [false]
  rw [BoundedUnary.encode_bits, BoundedUnary.encode_bits]
  simp only [List.nil_append, map_add, map_one, BoundedUnary.bits]
  have difference : MvPolynomial.eval sizes capacity + 1 - count.val.val =
      (MvPolynomial.eval sizes capacity - count.val.val) + 1 := by have bounded := count.property; omega
  rw [difference, List.replicate_add]
  simp [List.append_assoc]

/-- Increment a mathematical rank strictly below the unary capacity. -/
noncomputable def boundedUnarySuccessor (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (boundedUnary capacity) (boundedUnary capacity)
    (fun sizes count => count.val < MvPolynomial.eval sizes capacity)
    (fun _ count => ⟨count.val.val + 1, Nat.succ_lt_succ count.property⟩)

/-- Successor is composition of existing array, packing-count, and projection realizations. -/
theorem boundedUnarySuccessor_realizable (capacity : MvPolynomial Parameter ℕ) :
    (boundedUnarySuccessor capacity).Realizable := by
  let computation := boundedUnarySuccessor capacity
  have original := (flags_realizable capacity).withPrecondition computation.precondition (by intros; trivial)
  have accepted := (arrayTrue_realizable (0 + 1 : MvPolynomial Parameter ℕ)).followedBy
    (arrayLast_realizable booleans 0) rfl (by intros; trivial)
  have extra := accepted.onResults computation.inputDomains computation.precondition
    (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  have appended := (arraySnoc_realizable booleans capacity).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => (flags capacity).compute sizes ⟨arguments.val, trivial⟩
      | true => true) (by intros; trivial) (by
      intro choice
      cases choice
      · exact original
      · exact extra)
  let countedComputation := ((arraySnoc booleans capacity).onResults computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => (flags capacity).compute sizes ⟨arguments.val, trivial⟩
      | true => true) (by intros; trivial)).followedBy (packingCount (capacity + 1)) rfl (by intros; trivial)
  have counted := appended.followedBy (packingCount_realizable (capacity + 1)) rfl (by intros; trivial)
  have countEquation sizes (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      (countedComputation.compute sizes arguments).val = (arguments.val ()).val + 1 := by
    change ArrayPacking.count (snocValues capacity sizes
      (fun index => decide (index.val < (arguments.val ()).val)) true) = _
    rw [ArrayPacking.count_eq_count_true, ofFn_snocValues]
    rw [ArrayPacking.unary_ofFn (Nat.le_of_lt_succ (arguments.val ()).isLt)]
    simp [BoundedUnary.bits_count]
  have result := counted.followedBy (narrow_realizable capacity) rfl (by
    intro sizes arguments valid
    change (countedComputation.compute sizes ⟨arguments, valid⟩).val ≤ MvPolynomial.eval sizes capacity
    rw [countEquation]
    exact Nat.succ_le_of_lt valid)
  apply result.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Fin.ext
  exact countEquation sizes ⟨arguments, valid⟩

end Polytime2.Computation
