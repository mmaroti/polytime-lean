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

import Polytime2.Arrays.Tabulate
import Polytime2.Computation.Fields

/-! # Enumerating canonical bounded row coordinates

Array positions carry one extra bit for prefix-count operations. Matrix
coordinates use their mathematical bound as width. Discard that extra bit,
which is zero for every valid position, and tabulate the ordinary coordinates.
The empty bound produces an empty array without needing an index value.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Preserve the mathematical coordinate while using its canonical index width. -/
noncomputable def arrayPositionToIndex (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition length) (boundedIndex length) (fun _ _ => True) (fun _ value => value.val)

theorem arrayPositionToIndex_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayPositionToIndex length).Realizable := by
  apply Realizable.Internal.fieldProjection (arrayPosition length) (boundedIndex length) 0
    (fun _ _ => True) (fun _ value => value.val)
  intro sizes value
  have fits : value.val.val < 2 ^ MvPolynomial.eval sizes length :=
    value.val.isLt.trans_le Nat.lt_two_pow_self.le
  have trimmed : ((arrayPosition length).encode sizes value.val).setWidth (MvPolynomial.eval sizes length) =
      (boundedIndex length).encode sizes value.val := by
    apply BitVec.eq_of_toNat_eq
    simp [arrayPosition, boundedIndex, boundedIndexOfWidth, Nat.mod_eq_of_lt fits]
  have kept : ArrayEncoding.bits ((boundedIndex length).encode sizes value.val) =
      (ArrayEncoding.bits ((arrayPosition length).encode sizes value.val)).take (MvPolynomial.eval sizes length) :=
    (congrArg ArrayEncoding.bits trimmed.symm).trans
      (bits_setWidth_take ((arrayPosition length).encode sizes value.val) (by
        change MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes (length + 1)
        simp))
  refine ⟨[], (ArrayEncoding.bits ((arrayPosition length).encode sizes value.val)).drop
    (MvPolynomial.eval sizes length), ?_, by simp⟩
  simpa only [List.nil_append, kept] using
    (List.take_append_drop (MvPolynomial.eval sizes length)
      (ArrayEncoding.bits ((arrayPosition length).encode sizes value.val))).symm

/-- Enumerate every row coordinate using the matrix-access index codec. -/
noncomputable def arrayBoundedPositions (length : MvPolynomial Parameter ℕ) : Computation Parameter Empty :=
  arrayTabulate Empty.elim (boundedIndex length) length (fun _ _ index => index)

theorem arrayBoundedPositions_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayBoundedPositions length).Realizable := by
  apply arrayTabulate_realizable Empty.elim (boundedIndex length) length (fun _ _ index => index)
  exact (arrayPositionToIndex_realizable length).withArguments _
    (MultiTape.oneTape (Sum.inr () : Empty ⊕ Unit)) (by intros; rfl)

end Polytime2.Computation
