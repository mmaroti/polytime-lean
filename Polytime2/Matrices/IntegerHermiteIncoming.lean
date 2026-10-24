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

import Polytime2.Matrices.HermiteIncomingController
import Polytime2.Matrices.IntegerOperations

/-! # Incoming-row reduction from original-width integer matrices

Given distinct selected rows and old pivot columns forming a positive upper
pivot block, clear the incoming row at the old pivots and normalize the entries
above them. Both input matrices use the supplied original entry width. The
implementation derives its workspace and widens both matrices internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns width pivots : MvPolynomial Parameter ℕ) : Fin 4 → EncodedDomain Parameter
  | 0 => (boundedIndex rows).arrayOfLength (pivots + 1)
  | 1 => (boundedIndex columns).arrayOfLength pivots
  | 2 => integerMatrices rows columns width
  | 3 => integerMatrices rows rows width

private def allowed (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ name, (inputs rows columns width pivots name).Carrier sizes) :=
  Function.Injective (successorValues pivots sizes (arguments 0)) ∧ Function.Injective (arguments 1) ∧
    (∀ index, 0 < (arguments 2).val
      (successorValues pivots sizes (arguments 0) index.castSucc) (arguments 1 index)) ∧
    (∀ row column : Fin (MvPolynomial.eval sizes pivots), column < row →
      (arguments 2).val (successorValues pivots sizes (arguments 0) row.castSucc) (arguments 1 column) = 0)

private noncomputable def prepared (rows columns width pivots : MvPolynomial Parameter ℕ) :=
  (integerMatrixWiden rows columns width (hermiteIncomingWorkspaceExtra width pivots)
      (hermiteIncomingWorkspace width pivots) rfl,
    integerMatrixWiden rows rows width (hermiteIncomingWorkspaceExtra width pivots)
      (hermiteIncomingWorkspace width pivots) rfl)

private noncomputable def preparedValues (rows columns width pivots : MvPolynomial Parameter ℕ)
    (name : Bool ⊕ Unit) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width pivots name).Carrier sizes //
      allowed rows columns width pivots sizes arguments}) :
    ((hermiteIncomingController rows columns width pivots).inputDomains name).Carrier sizes :=
  match name with
  | .inl false => arguments.val 0
  | .inl true => arguments.val 1
  | .inr () => ((prepared rows columns width pivots).1.compute sizes ⟨(fun _ => arguments.val 2), trivial⟩,
      (prepared rows columns width pivots).2.compute sizes ⟨(fun _ => arguments.val 3), trivial⟩)

private theorem prepared_valid (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (inputs rows columns width pivots name).Carrier sizes //
      allowed rows columns width pivots sizes arguments}) :
    (hermiteIncomingController rows columns width pivots).precondition sizes
      (fun name => preparedValues rows columns width pivots name sizes arguments) := by
  exact hermiteIncomingController_permitted rows columns width pivots sizes
    (fun name => preparedValues rows columns width pivots name sizes arguments)
    ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩
    ⟨arguments.val 1, arguments.property.2.1⟩ rfl rfl arguments.property.2.2.1 arguments.property.2.2.2
    (arguments.val 2).property (arguments.val 3).property

/-- Clear an incoming row against a positive upper pivot block, deriving all extra storage internally. -/
noncomputable def integerHermiteIncoming (rows columns width pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) :=
  (hermiteIncomingController rows columns width pivots).onResults (inputs rows columns width pivots)
    (allowed rows columns width pivots) (preparedValues rows columns width pivots) (prepared_valid rows columns width pivots)

/-- Input widening and the entire incoming traversal are realized by composition. -/
theorem integerHermiteIncoming_realizable (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (integerHermiteIncoming rows columns width pivots).Realizable := by
  apply (hermiteIncomingController_realizable rows columns width pivots).onResults (inputs rows columns width pivots)
    (allowed rows columns width pivots) (preparedValues rows columns width pivots) (prepared_valid rows columns width pivots)
  intro name
  rcases name with choice | singleton
  · cases choice
    · exact Realizable.argument (inputs rows columns width pivots) 0 (allowed rows columns width pivots)
    · exact Realizable.argument (inputs rows columns width pivots) 1 (allowed rows columns width pivots)
  · cases singleton
    have first := ((integerMatrixWiden_realizable rows columns width (hermiteIncomingWorkspaceExtra width pivots)
      (hermiteIncomingWorkspace width pivots) rfl).withArguments (inputs rows columns width pivots)
      (MultiTape.oneTape 2) (by intros; rfl)).withPrecondition (allowed rows columns width pivots) (by intros; trivial)
    have second := ((integerMatrixWiden_realizable rows rows width (hermiteIncomingWorkspaceExtra width pivots)
      (hermiteIncomingWorkspace width pivots) rfl).withArguments (inputs rows columns width pivots)
      (MultiTape.oneTape 3) (by intros; rfl)).withPrecondition (allowed rows columns width pivots) (by intros; trivial)
    exact first.prodMk second

/-- The original-width interface returns precisely the mathematical incoming traversal. -/
theorem integerHermiteIncoming_correct (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteIncoming rows columns width pivots).Arguments sizes //
      (integerHermiteIncoming rows columns width pivots).precondition sizes arguments}) :
    let result := (integerHermiteIncoming rows columns width pivots).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteIncomingPrefix
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩ (arguments.val 1)
      (MvPolynomial.eval sizes pivots) (arguments.val 2).val (arguments.val 3).val :=
  hermiteIncomingController_correct rows columns width pivots sizes
    ⟨(fun name => preparedValues rows columns width pivots name sizes arguments), prepared_valid rows columns width pivots sizes arguments⟩
    ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩
    ⟨arguments.val 1, arguments.property.2.1⟩ rfl rfl

/-- Every old pivot is positive and its incoming entry is zero after the traversal. -/
theorem integerHermiteIncoming_entries (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteIncoming rows columns width pivots).Arguments sizes //
      (integerHermiteIncoming rows columns width pivots).precondition sizes arguments}) :
    let result := (integerHermiteIncoming rows columns width pivots).compute sizes arguments
    ∀ index : Fin (MvPolynomial.eval sizes pivots),
      0 < result.1.val (successorValues pivots sizes (arguments.val 0) index.castSucc) (arguments.val 1 index) ∧
      result.1.val (successorValues pivots sizes (arguments.val 0) (Fin.last (MvPolynomial.eval sizes pivots)))
        (arguments.val 1 index) = 0 := by
  have actual := integerHermiteIncoming_correct rows columns width pivots sizes arguments
  dsimp only
  intro index
  have pure := IntegerMatrix.hermiteIncomingPrefix_entries
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    ⟨successorValues pivots sizes (arguments.val 0), arguments.property.1⟩ (arguments.val 1)
    (MvPolynomial.eval sizes pivots) le_rfl (arguments.val 2).val (arguments.val 3).val
    arguments.property.2.2.1 arguments.property.2.2.2 index index.isLt
  have transfer := congrArg (fun matrices =>
    0 < matrices.1 (successorValues pivots sizes (arguments.val 0) index.castSucc) (arguments.val 1 index) ∧
    matrices.1 (successorValues pivots sizes (arguments.val 0) (Fin.last (MvPolynomial.eval sizes pivots)))
      (arguments.val 1 index) = 0) actual
  exact transfer.mpr ⟨pure.1, pure.2.1⟩

/-- The actual accumulated left basis still presents the result and remains unimodular. -/
theorem integerHermiteIncoming_preserves (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteIncoming rows columns width pivots).Arguments sizes //
      (integerHermiteIncoming rows columns width pivots).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val 3).val * original * right = (arguments.val 2).val)
    (unit : IsUnit (arguments.val 3).val.det) :
    let result := (integerHermiteIncoming rows columns width pivots).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det :=
  hermiteIncomingController_preserves rows columns width pivots sizes
    ⟨(fun name => preparedValues rows columns width pivots name sizes arguments), prepared_valid rows columns width pivots sizes arguments⟩
    original right equation unit

end Polytime2.Computation
