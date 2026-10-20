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

import Polytime2.Computation.ComputedCall
import Polytime2.TM0.Computation

/-! # A data-dependent call with a quadratic callee width

The caller counts leading true flags. It invokes a fixed polynomial evaluator
at that actual count, so both the callee's result and live width depend on data.
-/

namespace Polytime2.Examples.DynamicSizes

open _root_.Polytime2.Computation EncodedDomain CallingConvention

private noncomputable def bounds (capacity : MvPolynomial Unit ℕ) : Unit → MvPolynomial Unit ℕ :=
  fun _ => capacity

private noncomputable def payload : EncodedDomain Unit :=
  namedRecord (Empty.elim : Empty → EncodedDomain Unit)

private theorem payload_width : payload.widthPolynomial = 0 := by
  change (record (Fintype.card Empty)
    (fun index => ((Fintype.equivFin Empty).symm index).elim : Fin (Fintype.card Empty) → EncodedDomain.{0, 0} Unit)).widthPolynomial = 0
  rw [record_widthPolynomial]
  exact Finset.sum_eq_zero (fun index _ => ((Fintype.equivFin Empty).symm index).elim)

private noncomputable def leadingRecord (capacity : MvPolynomial Unit ℕ) : Computation Unit Unit where
  inputDomains := (leadingUnarySize capacity).inputDomains
  outputDomain := computedSizeDomain (bounds capacity)
  precondition _ _ := True
  compute sizes arguments _ := (leadingUnarySize capacity).compute sizes arguments

private theorem leadingRecord_realizable (capacity : MvPolynomial Unit ℕ) :
    (leadingRecord capacity).Realizable := by
  exact Computation.Realizable.namedRecordOutputs (leadingUnarySize capacity).inputDomains
    (fun _ : Unit => boundedUnary capacity) (fun _ _ => True)
    (fun _ => (leadingUnarySize capacity).compute) (fun _ => leadingUnarySize_realizable capacity)

private noncomputable def emptyFrame (capacity : MvPolynomial Unit ℕ) : Computation Unit Unit where
  inputDomains _ := computedSizeDomain (bounds capacity)
  outputDomain := atComputedSizeDomain (bounds capacity) payload
  precondition _ _ := True
  compute _ arguments := ⟨arguments.val (), fun impossible => impossible.elim⟩

private theorem emptyFrame_realizable (capacity : MvPolynomial Unit ℕ) :
    (emptyFrame capacity).Realizable := by
  let index := computedSizeDomain (bounds capacity)
  have capacityZero : SizeSubstitution.polynomial (bounds capacity) payload.widthPolynomial = 0 := by
    rw [payload_width]
    exact map_zero _
  apply (copy_realizable index).withEncodedOutput (emptyFrame capacity).outputDomain
    (emptyFrame capacity).compute
  · intro sizes
    change MvPolynomial.eval sizes (index.widthPolynomial +
      SizeSubstitution.polynomial (bounds capacity) payload.widthPolynomial) = _
    rw [capacityZero, add_zero]
    rfl
  · intro sizes arguments
    let actual := computedSizeAssignment (bounds capacity) sizes (arguments.val ())
    let bits := (payload.encode actual (fun impossible => impossible.elim)).setWidth
      (MvPolynomial.eval sizes (SizeSubstitution.polynomial (bounds capacity) payload.widthPolynomial))
    have empty : ArrayEncoding.bits bits = [] := by
      apply List.eq_nil_of_length_eq_zero
      change MvPolynomial.eval sizes (SizeSubstitution.polynomial (bounds capacity) payload.widthPolynomial) = 0
      rw [capacityZero]
      rfl
    change tape (ArrayEncoding.bits ((index.prod
      (bitVectors (SizeSubstitution.polynomial (bounds capacity) payload.widthPolynomial))).encode
        sizes (arguments.val (), bits))) = tape (ArrayEncoding.bits (index.encode sizes (arguments.val ())))
    rw [bits_prod_encode, empty, List.append_nil]

/-- One fixed callee is invoked at the leading-prefix count, with a dependent
result whose numeric value and live unary width are that count squared. -/
noncomputable def leadingSquare (capacity : MvPolynomial Unit ℕ) : Computation Unit Unit :=
  ((leadingRecord capacity).followedBy (emptyFrame capacity) rfl (by intros; trivial)).followedBy
    ((polynomialUnarySize ((MvPolynomial.X ()) ^ 2)).atComputedSizes (bounds capacity))
    rfl (by intros; trivial)

theorem leadingSquare_realizable (capacity : MvPolynomial Unit ℕ) :
    (leadingSquare capacity).Realizable :=
  ((leadingRecord_realizable capacity).followedBy (emptyFrame_realizable capacity)
    rfl (by intros; trivial)).followedBy
      ((polynomialUnarySize_realizable ((MvPolynomial.X ()) ^ 2)).atComputedSizes (bounds capacity))
      rfl (by intros; trivial)

example (capacity : MvPolynomial Unit ℕ) : (leadingSquare capacity).TM0Realizable :=
  (leadingSquare_realizable capacity).tm0

example : (leadingSquare (0 : MvPolynomial Unit ℕ)).TM0Realizable :=
  (leadingSquare_realizable 0).tm0

example (capacity : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (flags : (leadingSquare capacity).Arguments sizes) :
    ((leadingSquare capacity).compute sizes ⟨flags, trivial⟩).2.val =
      ((List.ofFn (flags ())).findIdx (! ·)) ^ 2 := by
  simp [leadingSquare, Computation.followedBy, leadingRecord, emptyFrame,
    atComputedSizes, polynomialUnarySize, computedSizeAssignment, leadingUnarySize]

end Polytime2.Examples.DynamicSizes
