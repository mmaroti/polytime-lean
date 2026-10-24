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

import Polytime2.Matrices.HermitePivotSelection
import Polytime2.Arrays.BoundedSnoc
import Mathlib.Data.Fin.Tuple.Embedding

/-! # Appending a new Hermite pivot selection

Append a row and column excluded from the old embeddings. The new row
embedding implies room for the extra pair, so callers supply no capacity
premise. Reuse bounded-array snoc, refine injectivity, and reinterpret the
result as the ordinary dependent pair of embeddings.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Append a new row/column pivot pair to the mathematical embeddings. -/
noncomputable def hermitePivotSelectionSnoc (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (hermitePivotSelection rows columns).prod ((boundedIndex rows).prod (boundedIndex columns))
  outputDomain := hermitePivotSelection rows columns
  precondition _ arguments := (arguments ()).2.1 ∉ Set.range (arguments ()).1.2.1 ∧
    (arguments ()).2.2 ∉ Set.range (arguments ()).1.2.2
  compute _ arguments := ⟨(arguments.val ()).1.1 + 1,
    Fin.Embedding.snoc (arguments.val ()).1.2.1 arguments.property.1,
    Fin.Embedding.snoc (arguments.val ()).1.2.2 arguments.property.2⟩

/-- Metadata append is bounded-array snoc followed by proved injectivity and codec reinterpretation. -/
theorem hermitePivotSelectionSnoc_realizable (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionSnoc rows columns).Realizable := by
  classical
  let computation := hermitePivotSelectionSnoc rows columns
  let element := (boundedIndex rows).prod (boundedIndex columns)
  let convert (_name : Unit) sizes (value : (computation.inputDomains ()).Carrier sizes) :
      ((boundedArray element rows).prod element).Carrier sizes :=
    (⟨⟨value.1.1, Nat.lt_succ_of_le (by
      simpa using Fintype.card_le_of_injective value.1.2.1 value.1.2.1.injective)⟩,
      fun index => (value.1.2.1 index, value.1.2.2 index)⟩, value.2)
  have appended := (boundedArraySnoc_realizable element rows).reinterpretInputs computation.inputDomains convert
    (by intros; rfl) (by intros; rfl) computation.precondition (by
      intro sizes arguments valid
      have extended := Fin.Embedding.snoc (arguments ()).1.2.1 valid.1
      have room : (arguments ()).1.1 + 1 ≤ MvPolynomial.eval sizes rows := by
        simpa using Fintype.card_le_of_injective extended extended.injective
      change (arguments ()).1.1 < MvPolynomial.eval sizes rows
      omega)
  let injective (sizes : Parameter → ℕ) (value : (boundedArray element rows).Carrier sizes) :=
    Function.Injective (fun index => (value.2 index).1) ∧ Function.Injective (fun index => (value.2 index).2)
  have refined := appended.refineOutput injective (by
    intro sizes arguments
    change Function.Injective (Prod.fst ∘ Fin.snoc
      (fun index => ((arguments.val ()).1.2.1 index, (arguments.val ()).1.2.2 index)) (arguments.val ()).2) ∧
      Function.Injective (Prod.snd ∘ Fin.snoc
        (fun index => ((arguments.val ()).1.2.1 index, (arguments.val ()).1.2.2 index)) (arguments.val ()).2)
    rw [Fin.comp_snoc, Fin.comp_snoc]
    exact ⟨(Fin.Embedding.snoc (arguments.val ()).1.2.1 arguments.property.1).injective,
      (Fin.Embedding.snoc (arguments.val ()).1.2.2 arguments.property.2).injective⟩)
  have interpreted := refined.reinterpretOutput (hermitePivotSelection rows columns)
    (fun _ value => ⟨value.val.1.val,
      ⟨fun index => (value.val.2 index).1, value.property.1⟩,
      ⟨fun index => (value.val.2 index).2, value.property.2⟩⟩)
    (by intros; rfl) (by intros; rfl)
  apply interpreted.withSpecification computation.precondition computation.compute (by intros; assumption)
  intro sizes arguments valid
  dsimp only [Computation.reinterpretOutput, Computation.refineOutput, Computation.reinterpretInputs,
    boundedArraySnoc, computation, hermitePivotSelectionSnoc, convert]
  change @Eq (Σ rank : ℕ,
    (Fin rank ↪ Fin (MvPolynomial.eval sizes rows)) ×
    (Fin rank ↪ Fin (MvPolynomial.eval sizes columns))) _ _
  apply congrArg (Sigma.mk ((arguments ()).1.1 + 1))
  apply Prod.ext
  · apply Function.Embedding.ext
    intro index
    exact congrFun (Fin.comp_snoc Prod.fst _ _) index
  · apply Function.Embedding.ext
    intro index
    exact congrFun (Fin.comp_snoc Prod.snd _ _) index

end Polytime2.Computation
