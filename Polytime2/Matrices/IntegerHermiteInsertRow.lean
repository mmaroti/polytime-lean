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

import Polytime2.Matrices.IntegerHermiteIncoming
import Polytime2.Matrices.IntegerHermiteResidualFinish
import Polytime2.Matrices.HermiteInsertMath

/-! # Certified insertion of an incoming integer row

The selected old rows and columns form a positive upper pivot block. Clear the
last selected row at the old pivots, then either retain its zero residual or
extend the block at a new nonzero pivot. Return both actual matrices and the
optional new column. All storage capacities are derived from the input sizes.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def finishingArguments (rows columns width pivots : MvPolynomial Parameter ℕ)
    (name : Fin 4) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteIncoming rows columns width pivots).Arguments sizes //
      (integerHermiteIncoming rows columns width pivots).precondition sizes arguments}) :
    ((integerHermiteResidualFinish rows columns (hermiteIncomingWorkspace width pivots) pivots).inputDomains name).Carrier sizes :=
  match name with
  | 0 => successorValues pivots sizes (arguments.val 0) (Fin.last (MvPolynomial.eval sizes pivots))
  | 1 => ((integerHermiteIncoming rows columns width pivots).compute sizes arguments).1
  | 2 => ((integerHermiteIncoming rows columns width pivots).compute sizes arguments).2
  | 3 => fun index => successorValues pivots sizes (arguments.val 0) index.castSucc

private theorem finishing_valid (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteIncoming rows columns width pivots).Arguments sizes //
      (integerHermiteIncoming rows columns width pivots).precondition sizes arguments}) :
    (integerHermiteResidualFinish rows columns (hermiteIncomingWorkspace width pivots) pivots).precondition sizes
      (fun name => finishingArguments rows columns width pivots name sizes arguments) := by
  constructor
  · apply List.nodup_ofFn.mpr
    intro first second same
    have values := congrArg Fin.val (arguments.property.1 same)
    exact Fin.ext values
  · intro member
    obtain ⟨index, same⟩ := List.mem_ofFn.mp member
    have values := congrArg Fin.val (arguments.property.1 same)
    simp only [Fin.val_castSucc, Fin.val_last] at values
    exact (ne_of_lt index.isLt) values

/-- Insert one incoming row and return the actual matrix, left basis, and optional new pivot. -/
noncomputable def integerHermiteInsertRow (rows columns width pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) :=
  (integerHermiteResidualFinish rows columns (hermiteIncomingWorkspace width pivots) pivots).onResults
    (integerHermiteIncoming rows columns width pivots).inputDomains
    (integerHermiteIncoming rows columns width pivots).precondition
    (finishingArguments rows columns width pivots) (finishing_valid rows columns width pivots)

/-- Incoming reduction and residual finishing are composed entirely through mathematical interfaces. -/
theorem integerHermiteInsertRow_realizable (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (integerHermiteInsertRow rows columns width pivots).Realizable := by
  let incoming := integerHermiteIncoming rows columns width pivots
  have cleared := integerHermiteIncoming_realizable rows columns width pivots
  have source := ((arrayLast_realizable (boundedIndex rows) pivots).withArguments incoming.inputDomains
    (MultiTape.oneTape 0) (by intros; rfl)).withPrecondition incoming.precondition (by intros; trivial)
  have oldRows := (((arrayUnsnoc_realizable (boundedIndex rows) pivots).withArguments incoming.inputDomains
    (MultiTape.oneTape 0) (by intros; rfl)).withPrecondition incoming.precondition (by intros; trivial)).fst
  apply (integerHermiteResidualFinish_realizable rows columns (hermiteIncomingWorkspace width pivots) pivots).onResults
    incoming.inputDomains incoming.precondition (finishingArguments rows columns width pivots) (finishing_valid rows columns width pivots)
  intro name
  fin_cases name
  · exact source
  · exact cleared.fst
  · exact cleared.snd
  · exact oldRows

/-- The complete runtime insertion agrees with the shared mathematical insertion in both rank outcomes. -/
theorem integerHermiteInsertRow_correct (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertRow rows columns width pivots).Arguments sizes //
      (integerHermiteInsertRow rows columns width pivots).precondition sizes arguments}) :
    let result := (integerHermiteInsertRow rows columns width pivots).compute sizes arguments
    ((result.1.1.val, result.1.2.val), result.2) = IntegerMatrix.hermiteInsertRow
      (Row := Fin (MvPolynomial.eval sizes rows))
      ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩
      (arguments.val 1) (arguments.val 2).val (arguments.val 3).val := by
  let selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows) :=
    ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩
  let source := selectedRows (Fin.last (MvPolynomial.eval sizes pivots))
  let finish (pair : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ ×
      Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes rows)) ℤ) :=
    match IntegerMatrix.hermiteResidualPivot source pair.1 with
    | none => (pair, none)
    | some column => (IntegerMatrix.hermiteExtendPivot (Fin.Embedding.init selectedRows) source column pair.1 pair.2, some column)
  have cleared := integerHermiteIncoming_correct rows columns width pivots sizes arguments
  have finished := integerHermiteResidualFinish_correct rows columns (hermiteIncomingWorkspace width pivots) pivots sizes
    ⟨(fun name => finishingArguments rows columns width pivots name sizes arguments), finishing_valid rows columns width pivots sizes arguments⟩
    (Fin.Embedding.init selectedRows) rfl
  have moved := congrArg finish cleared
  dsimp only [finish, source, selectedRows] at moved
  apply finished.trans
  dsimp only [IntegerMatrix.hermiteInsertRow, finishingArguments, selectedRows]
  convert moved using 1 <;> first | rfl | (split <;> simp_all only)

/-- Insertion retains the actual accumulated presentation and unimodular basis. -/
theorem integerHermiteInsertRow_preserves (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteInsertRow rows columns width pivots).Arguments sizes //
      (integerHermiteInsertRow rows columns width pivots).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 3).val * original * right = (arguments.val 2).val)
    (unit : IsUnit (arguments.val 3).val.det) :
    let result := (integerHermiteInsertRow rows columns width pivots).compute sizes arguments
    result.1.2.val * original * right = result.1.1.val ∧ IsUnit result.1.2.val.det := by
  have cleared := integerHermiteIncoming_preserves rows columns width pivots sizes arguments original right equation unit
  exact integerHermiteResidualFinish_preserves rows columns (hermiteIncomingWorkspace width pivots) pivots sizes
    ⟨(fun name => finishingArguments rows columns width pivots name sizes arguments), finishing_valid rows columns width pivots sizes arguments⟩
    original right cleared.1 cleared.2

end Polytime2.Computation
