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

import Polytime2.Encoding.BoundedArray
import Polytime2.Encoding.BinaryEncoding
import Mathlib.Data.Fintype.Card

/-! # Canonical encoding of Hermite pivot selections

The public carrier is an ordinary dependent pair of a rank and two finite
embeddings. Reuse one bounded array of row/column pairs, refining its two
projections to be injective. The rank bound follows from row injectivity;
there is no public padding, default coordinate, or independent array length.
-/

open scoped Classical

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def pivotStorage (rows columns : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  boundedArray ((boundedIndex rows).prod (boundedIndex columns)) rows

private def pivotInjective (rows columns : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (value : (pivotStorage rows columns).Carrier sizes) : Prop :=
  Function.Injective (fun index => (value.2 index).1) ∧
    Function.Injective (fun index => (value.2 index).2)

private noncomputable def pivotEquiv (rows columns : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (Σ rank : ℕ, (Fin rank ↪ Fin (MvPolynomial.eval sizes rows)) ×
      (Fin rank ↪ Fin (MvPolynomial.eval sizes columns))) ≃
      ((pivotStorage rows columns).restrict (pivotInjective rows columns)).Carrier sizes where
  toFun value := by
    have rankBound : value.1 ≤ MvPolynomial.eval sizes rows := by
      simpa using Fintype.card_le_of_injective value.2.1 value.2.1.injective
    exact ⟨⟨⟨value.1, Nat.lt_succ_of_le rankBound⟩, fun index => (value.2.1 index, value.2.2 index)⟩,
      value.2.1.injective, value.2.2.injective⟩
  invFun value := ⟨value.val.1.val, ⟨fun index => (value.val.2 index).1, value.property.1⟩,
    ⟨fun index => (value.val.2 index).2, value.property.2⟩⟩
  left_inv value := by rcases value with ⟨rank, activeRows, pivotColumns⟩; rfl
  right_inv value := by
    rcases value with ⟨⟨⟨rank, bounded⟩, values⟩, valid⟩
    apply Subtype.ext
    apply Sigma.ext rfl
    apply heq_of_eq
    funext index
    exact Prod.eta (values index)

/-- A runtime rank and row/column embeddings with one shared canonical bounded-array encoding. -/
noncomputable def hermitePivotSelection (rows columns : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  ((pivotStorage rows columns).restrict (pivotInjective rows columns)).reindex
    (fun sizes => Σ rank : ℕ, (Fin rank ↪ Fin (MvPolynomial.eval sizes rows)) ×
      (Fin rank ↪ Fin (MvPolynomial.eval sizes columns))) (pivotEquiv rows columns)

/-- Exact width includes one unary rank header and capacity for paired coordinates. -/
theorem hermitePivotSelection_width (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelection rows columns).widthPolynomial = rows + rows * (rows + columns) := rfl

/-- Rank zero reuses the empty bounded-array word, including empty coordinate types. -/
theorem hermitePivotSelection_empty_encode (rows columns : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (hermitePivotSelection rows columns).encode sizes
      ⟨0, ⟨Fin.elim0, by intro index; exact index.elim0⟩, ⟨Fin.elim0, by intro index; exact index.elim0⟩⟩ =
    (boundedArray ((boundedIndex rows).prod (boundedIndex columns)) rows).encode sizes
      ⟨⟨0, by omega⟩, Fin.elim0⟩ := rfl

end Polytime2.EncodedDomain
