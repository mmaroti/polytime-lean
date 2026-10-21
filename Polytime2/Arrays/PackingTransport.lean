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

import Polytime2.Arrays.Packing
import Polytime2.Encoding.SizeSubstitution

/-! # Transporting array codecs across equal lengths and element widths -/

namespace Polytime2.ArrayPacking

open EncodedDomain

/-- Mathematical array transport; equality proofs generate no runtime work. -/
def arrayCast {firstLength secondLength : ℕ} {Source Target : Type}
    (lengthEq : firstLength = secondLength) (elementEq : Source ≃ Target) :
    (Fin firstLength → Source) ≃ (Fin secondLength → Target) :=
  Equiv.arrowCongr (Equiv.cast (congrArg Fin lengthEq)) elementEq

def bitArrayCast {firstLength secondLength firstWidth secondWidth : ℕ}
    (lengthEq : firstLength = secondLength) (widthEq : firstWidth = secondWidth) :
    (Fin firstLength → BitVec firstWidth) ≃ (Fin secondLength → BitVec secondWidth) :=
  arrayCast lengthEq (Equiv.cast (congrArg BitVec widthEq))

theorem arrayCast_ofFn {firstLength secondLength : ℕ} {Element : Type}
    (lengthEq : firstLength = secondLength) (values : Fin secondLength → Element) :
    List.ofFn ((arrayCast lengthEq (Equiv.refl Element)).symm values) = List.ofFn values := by
  cases lengthEq
  rfl

theorem bitArrayCast_bits {firstLength secondLength firstWidth secondWidth : ℕ}
    (lengthEq : firstLength = secondLength) (widthEq : firstWidth = secondWidth)
    (values : Fin secondLength → BitVec secondWidth) :
    ArrayEncoding.bits (ArrayEncoding.encode id firstLength ((bitArrayCast lengthEq widthEq).symm values)) =
      ArrayEncoding.bits (ArrayEncoding.encode id secondLength values) := by
  cases lengthEq
  cases widthEq
  rfl

/-- Stable selection is independent of casts of lengths and bit-vector widths. -/
theorem rawPack_bitArrayCast {firstLength secondLength firstWidth secondWidth : ℕ}
    (lengthEq : firstLength = secondLength) (widthEq : firstWidth = secondWidth)
    (flags : Fin secondLength → Bool) (values : Fin secondLength → BitVec secondWidth) :
    bitArrayCast lengthEq widthEq
      (rawPack id ((arrayCast lengthEq (Equiv.refl Bool)).symm flags)
        ((bitArrayCast lengthEq widthEq).symm values)) = rawPack id flags values := by
  cases lengthEq
  cases widthEq
  rfl

end Polytime2.ArrayPacking
