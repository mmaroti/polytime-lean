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

import Polytime2.Matrices.HermitePivotAppend
import Polytime2.Arrays.SearchCoordinates
import Polytime2.Arrays.SearchGuard

/-! # Updating pivot metadata after optional rank growth

Keep the original embeddings when insertion returns no column. Otherwise append
the incoming row and the returned column; exclusions preserve injectivity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Keep metadata on no pivot, or append an excluded row and returned column. -/
noncomputable def hermitePivotSelectionUpdate (rows columns : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := ((hermitePivotSelection rows columns).prod (boundedIndex rows)).prod (arraySearchResult columns)
  outputDomain := hermitePivotSelection rows columns
  precondition _ arguments := (arguments ()).1.2 ∉ Set.range (arguments ()).1.1.2.1 ∧
    ∀ column, (arguments ()).2 = some column → column ∉ Set.range (arguments ()).1.1.2.2
  compute _ arguments := match found : (arguments.val ()).2 with
    | none => (arguments.val ()).1.1
    | some column => ⟨(arguments.val ()).1.1.1 + 1,
      Fin.Embedding.snoc (arguments.val ()).1.1.2.1 arguments.property.1,
      Fin.Embedding.snoc (arguments.val ()).1.1.2.2 (arguments.property.2 column found)⟩

/-- Optional-result branching and bounded-array snoc realize metadata updates. -/
theorem hermitePivotSelectionUpdate_realizable (rows columns : MvPolynomial Parameter ℕ) :
    (hermitePivotSelectionUpdate rows columns).Realizable := by
  let computation := hermitePivotSelectionUpdate rows columns
  let metadata := hermitePivotSelection rows columns
  let row := boundedIndex rows
  let optional := arraySearchResult columns
  let condition (_sizes : Parameter → ℕ) (arguments : computation.Arguments _sizes) := (arguments ()).2.isNone
  have result (allowed : ∀ sizes, computation.Arguments sizes → Prop) :=
    (pairProjection_realizable (metadata.prod row) optional true).withPrecondition allowed (by intros; trivial)
  have old (allowed : ∀ sizes, computation.Arguments sizes → Prop) :=
    ((pairProjection_realizable (metadata.prod row) optional false).fst).withPrecondition allowed (by intros; trivial)
  apply Realizable.ofCases condition
  · exact (result computation.precondition).followedBy (arraySearchIsNone_realizable columns) rfl (by intros; trivial)
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = true
    apply (old allowed).withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    have absent : (arguments ()).2 = none := Option.isNone_iff_eq_none.mp valid.2
    dsimp only [computation, hermitePivotSelectionUpdate]
    split
    · rfl
    · rename_i column found
      have impossible := absent.symm.trans found
      contradiction
  · let allowed sizes arguments := computation.precondition sizes arguments ∧ condition sizes arguments = false
    have present sizes (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :
        (arguments.val ()).2.isSome := by
      cases found : (arguments.val ()).2 with
      | none => have impossible := arguments.property.2; simp only [condition, found, Option.isNone_none, Bool.true_eq_false] at impossible
      | some column => simp only [Option.isSome_some]
    let selected sizes (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :=
      (arguments.val ()).2.get (present sizes arguments)
    have extracted := (result allowed).followedBy (arraySearchFound_realizable columns) rfl (by
      intro sizes arguments valid
      exact present sizes ⟨arguments, valid⟩)
    have source := ((pairProjection_realizable (metadata.prod row) optional false).snd).withPrecondition allowed (by intros; trivial)
    have coordinates := source.prodMk extracted
    have input := (old allowed).prodMk coordinates
    have appended := input.followedBy (hermitePivotSelectionSnoc_realizable rows columns) rfl (by
      intro sizes arguments valid
      exact ⟨valid.1.1, valid.1.2 _ (Option.some_get (present sizes ⟨arguments, valid⟩)).symm⟩)
    apply appended.withSpecification allowed _ (by intros; assumption)
    intro sizes arguments valid
    dsimp only [computation, hermitePivotSelectionUpdate]
    split
    · rename_i found
      have impossible := valid.2
      simp only [condition, found, Option.isNone_none, Bool.true_eq_false] at impossible
    · rename_i column found
      have same : selected sizes ⟨arguments, valid⟩ = column :=
        Option.some.inj ((Option.some_get (present sizes ⟨arguments, valid⟩)).trans found)
      change (hermitePivotSelectionSnoc rows columns).compute sizes _ = _
      dsimp only [hermitePivotSelectionSnoc]
      apply congrArg (Sigma.mk ((arguments ()).1.1.1 + 1))
      apply Prod.ext
      · rfl
      · apply Function.Embedding.ext
        intro index
        exact congrArg (fun value : Fin (MvPolynomial.eval sizes columns) =>
          Fin.snoc (α := fun _ => Fin (MvPolynomial.eval sizes columns))
            (arguments ()).1.1.2.2 value index) same

end Polytime2.Computation
