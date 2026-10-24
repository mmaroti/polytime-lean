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

import Polytime2.Matrices.IntegerHermiteStoredRank
import Polytime2.Matrices.HermitePivotUpdate
import Polytime2.Matrices.HermiteSweepMath

/-! # Runtime insertion with updated pivot embeddings

Insert the incoming row, retaining both actual matrices. Keep the old pivot
selection for a dependent row, or append the incoming row and new column.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem update_valid (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments}) :
    (hermitePivotSelectionUpdate rows columns).precondition sizes
      (fun _ => (arguments.val () 0, ((integerHermiteInsertHost rows columns width).compute sizes arguments).2)) :=
  ⟨arguments.property.1, fun column found => integerHermiteInsertHost_newColumn rows columns width sizes arguments column found⟩

/-- Update the pivot embeddings using the optional result of complete insertion. -/
noncomputable def integerHermiteInsertSelection (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  (hermitePivotSelectionUpdate rows columns).onResults (integerHermiteInsertHost rows columns width).inputDomains
    (integerHermiteInsertHost rows columns width).precondition
    (fun _ sizes arguments => (arguments.val () 0,
      ((integerHermiteInsertHost rows columns width).compute sizes arguments).2))
    (update_valid rows columns width)

/-- Coordinate exclusion is derived from insertion's mathematical contract. -/
theorem integerHermiteInsertSelection_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteInsertSelection rows columns width).Realizable := by
  let computation := integerHermiteInsertHost rows columns width
  let fields : Fin 3 → EncodedDomain Parameter
    | 0 => (hermitePivotSelection rows columns).prod (boundedIndex rows)
    | 1 => integerMatrices rows columns width
    | 2 => integerMatrices rows rows width
  have old := (recordProjection_realizable 3 fields 0).withPrecondition computation.precondition (by intros; trivial)
  apply (hermitePivotSelectionUpdate_realizable rows columns).onResults computation.inputDomains computation.precondition
    (fun _ sizes arguments => (arguments.val () 0, (computation.compute sizes arguments).2)) (update_valid rows columns width)
  intro name
  cases name
  exact (old.prodMk ((integerHermiteInsertHost_realizable rows columns width).snd))

/-- A dependent insertion retains exactly the old rank and embeddings. -/
theorem integerHermiteInsertSelection_none (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments})
    (found : ((integerHermiteInsertHost rows columns width).compute sizes arguments).2 = none) :
    (integerHermiteInsertSelection rows columns width).compute sizes arguments = (arguments.val () 0).1 := by
  dsimp only [integerHermiteInsertSelection, Computation.onResults, hermitePivotSelectionUpdate]
  split
  · rfl
  · rename_i column present
    have impossible := found.symm.trans present
    contradiction

/-- An independent insertion appends the incoming row and the actual new column. -/
theorem integerHermiteInsertSelection_some (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertHost rows columns width).Arguments sizes //
      (integerHermiteInsertHost rows columns width).precondition sizes arguments})
    (column : Fin (MvPolynomial.eval sizes columns))
    (found : ((integerHermiteInsertHost rows columns width).compute sizes arguments).2 = some column) :
    (integerHermiteInsertSelection rows columns width).compute sizes arguments =
      ⟨(arguments.val () 0).1.1 + 1,
        Fin.Embedding.snoc (arguments.val () 0).1.2.1 arguments.property.1,
        Fin.Embedding.snoc (arguments.val () 0).1.2.2
          (integerHermiteInsertHost_newColumn rows columns width sizes arguments column found)⟩ := by
  dsimp only [integerHermiteInsertSelection, Computation.onResults, hermitePivotSelectionUpdate]
  split
  · rename_i absent
    have impossible := absent.symm.trans found
    contradiction
  · rename_i selected present
    have same : selected = column := Option.some.inj (present.symm.trans found)
    subst column
    rfl

/-- Return both actual matrices and updated rank/embeddings after one incoming row. -/
noncomputable def integerHermiteAdvance (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerHermiteInsertHost rows columns width).inputDomains
  outputDomain := ((integerMatrices rows columns (hermiteInsertOutputWidth width rows)).prod
    (integerMatrices rows rows (hermiteInsertOutputWidth width rows))).prod (hermitePivotSelection rows columns)
  precondition := (integerHermiteInsertHost rows columns width).precondition
  compute sizes arguments := (((integerHermiteInsertHost rows columns width).compute sizes arguments).1,
    (integerHermiteInsertSelection rows columns width).compute sizes arguments)

/-- Insertion and metadata specialization are combined through ordinary output pairing. -/
theorem integerHermiteAdvance_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteAdvance rows columns width).Realizable := by
  exact ((integerHermiteInsertHost_realizable rows columns width).fst).prodMk (integerHermiteInsertSelection_realizable rows columns width)

/-- Updating embeddings retains the same actual presentation and unimodular basis. -/
theorem integerHermiteAdvance_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAdvance rows columns width).Arguments sizes //
      (integerHermiteAdvance rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val () 2).val * original * right = (arguments.val () 1).val)
    (unit : IsUnit (arguments.val () 2).val.det) :
    let result := (integerHermiteAdvance rows columns width).compute sizes arguments
    result.1.2.val * original * right = result.1.1.val ∧ IsUnit result.1.2.val.det :=
  integerHermiteInsertHost_preserves rows columns width sizes arguments original right equation unit

/-- Every mathematical outer-prefix state permits the next runtime insertion. -/
theorem integerHermiteAdvance_permitted (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerHermiteAdvance rows columns width).Arguments sizes)
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (invariant : IntegerMatrix.HermiteRowPrefix original (arguments () 0).2.val
      (((arguments () 1).val, (arguments () 2).val), (arguments () 0).1)) :
    (integerHermiteAdvance rows columns width).precondition sizes arguments := by
  obtain ⟨equation, unit, oldRows, support, upper, positive, reduced, basisSupport, future⟩ := invariant
  refine ⟨?_, positive, ?_⟩
  · rintro ⟨index, same⟩
    have before := oldRows index
    rw [same] at before
    exact (lt_irrefl _ before)
  · intro row column below
    exact upper below

/-- The complete runtime state equals the proof-carrying mathematical outer transition. -/
theorem integerHermiteAdvance_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAdvance rows columns width).Arguments sizes //
      (integerHermiteAdvance rows columns width).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (invariant : IntegerMatrix.HermiteRowPrefix original (arguments.val () 0).2.val
      (((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1)) :
    let result := (integerHermiteAdvance rows columns width).compute sizes arguments
    (((result.1.1.val, result.1.2.val), result.2) : IntegerMatrix.HermiteRowState
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)) =
      (IntegerMatrix.hermiteRowAdvance original (arguments.val () 0).2
        ⟨(((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1), invariant⟩).val := by
  let before : {state : IntegerMatrix.HermiteRowState (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) //
      IntegerMatrix.HermiteRowPrefix original (arguments.val () 0).2.val state} :=
    ⟨(((arguments.val () 1).val, (arguments.val () 2).val), (arguments.val () 0).1), invariant⟩
  have inserted := integerHermiteInsertHost_correct rows columns width sizes arguments
  apply Prod.ext
  · exact (congrArg Prod.fst inserted).trans
      (IntegerMatrix.hermiteRowAdvance_pair original (arguments.val () 0).2 before arguments.property.1).symm
  · cases found : ((integerHermiteInsertHost rows columns width).compute sizes arguments).2 with
    | none =>
      exact (integerHermiteInsertSelection_none rows columns width sizes arguments found).trans
        (IntegerMatrix.hermiteRowAdvance_selection_none original (arguments.val () 0).2 before arguments.property.1
          ((congrArg Prod.snd inserted).symm.trans found)).symm
    | some column =>
      exact (integerHermiteInsertSelection_some rows columns width sizes arguments column found).trans
        (IntegerMatrix.hermiteRowAdvance_selection_some original (arguments.val () 0).2 before arguments.property.1 column
          (integerHermiteInsertHost_newColumn rows columns width sizes arguments column found)
          ((congrArg Prod.snd inserted).symm.trans found)).symm

end Polytime2.Computation
