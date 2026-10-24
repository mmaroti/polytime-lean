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

import Polytime2.Arrays.FirstFalse
import Polytime2.Arrays.FindFalseMath
import Mathlib.Logic.Equiv.Fin.Basic

/-! # First-false search with an optional mathematical index

The existing prefix scan and count implement the search. Its all-accepted
sentinel stays inside the codec; the public result is `Option (Fin length)`.
The exact binary width is the existing prefix-count width `length + 1`,
including the empty array.
-/

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Optional array coordinates reuse the prefix-count binary encoding. -/
noncomputable def arraySearchResult (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (boundedIndexOfWidth (fun sizes => MvPolynomial.eval sizes length + 1) (length + 1)
    (by intro sizes; simp only [map_add, map_one]; exact Nat.lt_two_pow_self.le)).reindex
      (fun sizes => Option (Fin (MvPolynomial.eval sizes length)))
      (fun _ => (finSuccEquiv' (Fin.last _)).symm)

end Polytime2.EncodedDomain

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Find the first false flag, returning `none` when every flag is true. -/
noncomputable def arrayFindFalse (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (firstFalse length).inputDomains
  outputDomain := EncodedDomain.arraySearchResult length
  precondition _ _ := True
  compute sizes arguments := finSuccEquiv' (Fin.last _) ⟨((firstFalse length).compute sizes arguments).toNat,
    Nat.lt_succ_of_le (firstFalse_bound length sizes (arguments.val ()))⟩

set_option backward.isDefEq.respectTransparency false in
theorem arrayFindFalse_realizable (length : MvPolynomial Parameter ℕ) : (arrayFindFalse length).Realizable := by
  apply (firstFalse_realizable length).withEncodedOutput (EncodedDomain.arraySearchResult length)
    (arrayFindFalse length).compute (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  apply congrArg EncodedDomain.ArrayEncoding.bits
  apply BitVec.eq_of_toNat_eq
  change (((finSuccEquiv' (Fin.last _)).symm
    (finSuccEquiv' (Fin.last _) ⟨((firstFalse length).compute sizes arguments).toNat, _⟩)).val) =
      ((firstFalse length).compute sizes arguments).toNat
  exact congrArg Fin.val ((finSuccEquiv' (Fin.last _)).symm_apply_apply _)

/-- An actual result is the least false position of the mathematical flag list. -/
theorem arrayFindFalse_some_iff (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) (index : Fin (MvPolynomial.eval sizes length)) :
    (arrayFindFalse length).compute sizes ⟨(fun _ => flags), trivial⟩ = some index ↔
      (List.ofFn flags).findIdx (! ·) = index.val := by
  change finSuccEquiv' (Fin.last _) ⟨((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat, _⟩ = some index ↔ _
  rw [finSuccEquiv'_eq_some]
  have above : (Fin.last (MvPolynomial.eval sizes length)).succAbove index = Fin.castSucc index :=
    Fin.succAbove_of_castSucc_lt _ _ (by simp)
  rw [above, Fin.ext_iff]
  change ((firstFalse length).compute sizes ⟨(fun _ => flags), trivial⟩).toNat = index.val ↔
    (List.ofFn flags).findIdx (! ·) = index.val
  rw [firstFalse_correct]

/-- The certified scan implements the shared pure finite-array search specification. -/
theorem arrayFindFalse_spec (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    (arrayFindFalse length).compute sizes ⟨(fun _ => flags), trivial⟩ = ArraySearch.firstFalse flags := by
  apply Option.ext
  intro index
  exact (arrayFindFalse_some_iff length sizes flags index).trans (ArraySearch.firstFalse_some_iff flags index).symm

theorem arrayFindFalse_none (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) :
    (arrayFindFalse length).compute sizes ⟨(fun _ => flags), trivial⟩ = none ↔ ∀ index, flags index = true := by
  rw [arrayFindFalse_spec]
  exact ArraySearch.firstFalse_none flags

theorem arrayFindFalse_found (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (flags : Fin (MvPolynomial.eval sizes length) → Bool) (index : Fin (MvPolynomial.eval sizes length))
    (found : (arrayFindFalse length).compute sizes ⟨(fun _ => flags), trivial⟩ = some index) :
    flags index = false :=
  ArraySearch.firstFalse_found flags index ((arrayFindFalse_spec length sizes flags).symm.trans found)

end Polytime2.Computation
