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

import Polytime2.Encoding.HermitePivots
import Polytime2.Arrays.BoundedEmpty
import Polytime2.Arrays.PackingResult

/-! # Initialization of dynamic Hermite pivot selections

Start the outer row sweep at rank zero with ordinary empty row and column
embeddings. The generic bounded-array initializer supplies the same canonical
word, without requiring a default coordinate in either domain.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Initialize the empty mathematical pivot selection for arbitrary matrix dimensions. -/
noncomputable def hermitePivotSelectionEmpty (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := hermitePivotSelection rows columns
  precondition _ _ := True
  compute _ _ := ⟨0, ⟨Fin.elim0, by intro index; exact index.elim0⟩,
    ⟨Fin.elim0, by intro index; exact index.elim0⟩⟩

/-- Reinterpret the certified empty bounded array as the empty pair of embeddings. -/
theorem hermitePivotSelectionEmpty_realizable (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionEmpty rows columns).Realizable := by
  have ready := boundedArrayEmpty_realizable ((boundedIndex rows).prod (boundedIndex columns)) rows
  apply ready.withEncodedOutput (hermitePivotSelection rows columns) (hermitePivotSelectionEmpty rows columns).compute
    (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  exact congrArg ArrayEncoding.bits (hermitePivotSelection_empty_encode rows columns sizes)

/-- Read the actual rank, with its bound derived from the selected-row embedding. -/
noncomputable def hermitePivotSelectionRank (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (hermitePivotSelection rows columns) (boundedUnary rows) (fun _ _ => True)
    (fun sizes value => ⟨value.val.1, Nat.lt_succ_of_le (by
      simpa using Fintype.card_le_of_injective value.val.2.1 value.val.2.1.injective)⟩)

/-- Rank extraction reuses the canonical bounded-array count projection. -/
theorem hermitePivotSelectionRank_realizable (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionRank rows columns).Realizable := by
  have counted := (boundedArrayCount_realizable ((boundedIndex rows).prod (boundedIndex columns)) rows).reinterpretInputs
    (fun _ : Unit => hermitePivotSelection rows columns)
    (fun _ sizes value => ⟨⟨value.1, Nat.lt_succ_of_le (by
      simpa using Fintype.card_le_of_injective value.2.1 value.2.1.injective)⟩,
      fun index => (value.2.1 index, value.2.2 index)⟩)
    (by intros; rfl) (by intros; rfl) (fun _ _ => True) (by intros; trivial)
  exact counted.withSpecification (hermitePivotSelectionRank rows columns).precondition
    (hermitePivotSelectionRank rows columns).compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
