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

import Polytime2.Matrices.HermiteIncomingWorkspace
import Polytime2.Arrays.FoldContract

/-! # Certified incoming-row traversal

Traverse old pivots in increasing order, clearing the incoming row and reducing
earlier rows. Embedded row and column selections and a positive upper pivot
block justify every update. Both actual matrices stay in a fixed polynomial
workspace derived from their original width and the pivot count.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def context (rows columns pivots : MvPolynomial Parameter ℕ) : Bool → EncodedDomain Parameter
  | false => (boundedIndex rows).arrayOfLength (pivots + 1)
  | true => (boundedIndex columns).arrayOfLength pivots

private def updateArguments (rows columns workspace pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (arrayPosition pivots).Carrier sizes) :
    (hermiteIncomingStageWithin rows columns workspace pivots).Arguments sizes
  | 0 => selected false | 1 => selected true | 2 => token | 3 => state.1 | 4 => state.2

private def updateAllowed (rows columns workspace pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (arrayPosition pivots).Carrier sizes) :=
  (hermiteIncomingStageWithin rows columns workspace pivots).precondition sizes
    (updateArguments rows columns workspace pivots sizes selected state token)

private noncomputable def update (rows columns workspace pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (token : (arrayPosition pivots).Carrier sizes) :
    (hermiteColumnState rows columns workspace).Carrier sizes := by
  classical
  exact if valid : updateAllowed rows columns workspace pivots sizes selected state token then
    (hermiteIncomingStageWithin rows columns workspace pivots).compute sizes
      ⟨updateArguments rows columns workspace pivots sizes selected state token, valid⟩ else state

private theorem update_realizable (rows columns workspace pivots : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (context rows columns pivots) (arrayPosition pivots) (hermiteColumnState rows columns workspace)
      (updateAllowed rows columns workspace pivots) (update rows columns workspace pivots)).Realizable := by
  classical
  let step := arrayFoldStep (context rows columns pivots) (arrayPosition pivots)
    (hermiteColumnState rows columns workspace) (updateAllowed rows columns workspace pivots)
    (update rows columns workspace pivots)
  have executed := (hermiteIncomingStageWithin_realizable rows columns workspace pivots).onResults
    step.inputDomains step.precondition
    (fun name sizes arguments => updateArguments rows columns workspace pivots sizes
      (fun original => arguments.val (.inl original)) (arguments.val (.inr false)) (arguments.val (.inr true)) name)
    (by intro sizes arguments; exact arguments.property) (by
      intro name
      fin_cases name
      · exact Realizable.argument step.inputDomains (.inl false) step.precondition
      · exact Realizable.argument step.inputDomains (.inl true) step.precondition
      · exact Realizable.argument step.inputDomains (.inr true) step.precondition
      · exact ((pairProjection_realizable (integerMatrices rows columns workspace) (integerMatrices rows rows workspace) false).withArguments
          step.inputDomains (MultiTape.oneTape (.inr false)) (by intros; rfl)).withPrecondition step.precondition (by intros; trivial)
      · exact ((pairProjection_realizable (integerMatrices rows columns workspace) (integerMatrices rows rows workspace) true).withArguments
          step.inputDomains (MultiTape.oneTape (.inr false)) (by intros; rfl)).withPrecondition step.precondition (by intros; trivial))
  apply executed.withSpecification step.precondition step.compute (by intros; assumption)
  intro sizes arguments valid
  have permitted : updateAllowed rows columns workspace pivots sizes
      (fun original => arguments (.inl original)) (arguments (.inr false)) (arguments (.inr true)) := valid
  simp only [step, arrayFoldStep, update, dite_eq_left permitted, Computation.onResults]

private def initialAllowed (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes) :=
  ∃ selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows),
    ∃ pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns),
      successorValues pivots sizes (selected false) = selectedRows ∧
      selected true = (fun index => pivotColumns index) ∧
      (∀ index, 0 < initial.1.val (selectedRows index.castSucc) (pivotColumns index)) ∧
      (∀ row column : Fin (MvPolynomial.eval sizes pivots), column < row →
        initial.1.val (selectedRows row.castSucc) (pivotColumns column) = 0) ∧
      (∀ row column, (initial.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
      (∀ row column, (initial.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width)

private def invariant (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes)
    (count : ℕ) (state : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes) :=
  ∀ selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows),
    ∀ pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns),
      successorValues pivots sizes (selected false) = selectedRows →
      selected true = (fun index => pivotColumns index) →
      (state.1.val, state.2.val) = IntegerMatrix.hermiteIncomingPrefix selectedRows pivotColumns count initial.1.val initial.2.val

private theorem starts (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes) :
    invariant rows columns width pivots sizes selected initial 0 initial := by
  unfold invariant
  intro selectedRows pivotColumns rowEquation columnEquation
  rfl

private theorem permits (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes)
    (valid : initialAllowed rows columns width pivots sizes selected initial)
    (index : Fin (MvPolynomial.eval sizes pivots))
    (before : invariant rows columns width pivots sizes selected initial index.val state) :
    updateAllowed rows columns (hermiteIncomingWorkspace width pivots) pivots sizes selected state index := by
  obtain ⟨selectedRows, pivotColumns, rowEquation, columnEquation, positive, upper, matrixBound, basisBound⟩ := valid
  exact hermiteIncomingWithinAllowed_of_prefix rows columns width pivots sizes
    (updateArguments rows columns (hermiteIncomingWorkspace width pivots) pivots sizes selected state index)
    selectedRows pivotColumns rowEquation columnEquation initial.1.val initial.2.val positive upper matrixBound basisBound
    (before selectedRows pivotColumns rowEquation columnEquation)

private theorem preserves (rows columns width pivots : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : ∀ name, (context rows columns pivots name).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)).Carrier sizes)
    (valid : initialAllowed rows columns width pivots sizes selected initial)
    (index : Fin (MvPolynomial.eval sizes pivots))
    (before : invariant rows columns width pivots sizes selected initial index.val state) :
    invariant rows columns width pivots sizes selected initial (index.val + 1)
      (update rows columns (hermiteIncomingWorkspace width pivots) pivots sizes selected state index) := by
  have permitted := permits rows columns width pivots sizes selected initial state valid index before
  simp only [update, dite_eq_left permitted]
  intro selectedRows pivotColumns rowEquation columnEquation
  have narrowed := hermiteIncomingStageWithin_correct rows columns (hermiteIncomingWorkspace width pivots) pivots sizes
    ⟨updateArguments rows columns (hermiteIncomingWorkspace width pivots) pivots sizes selected state index, permitted⟩
  have advanced := hermiteIncomingStage_prefix rows columns (hermiteIncomingWorkspace width pivots) pivots sizes
    ⟨updateArguments rows columns (hermiteIncomingWorkspace width pivots) pivots sizes selected state index, permitted.choose⟩
    selectedRows rowEquation initial.1.val initial.2.val
    (by simpa only [updateArguments, columnEquation] using before selectedRows pivotColumns rowEquation columnEquation)
  dsimp only [updateArguments] at advanced
  simp only [columnEquation] at advanced
  exact narrowed.trans advanced

private noncomputable def controllerFold (rows columns width pivots : MvPolynomial Parameter ℕ) :=
  arrayFold (context rows columns pivots) (arrayPosition pivots)
    (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)) pivots
    (fun sizes selected array initial => array = id ∧ initialAllowed rows columns width pivots sizes selected initial)
    (update rows columns (hermiteIncomingWorkspace width pivots) pivots)

private theorem controllerFold_realizable (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (controllerFold rows columns width pivots).Realizable := by
  apply arrayFold_realizable (context rows columns pivots) (arrayPosition pivots)
    (hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)) pivots
    (fun sizes selected array initial => array = id ∧ initialAllowed rows columns width pivots sizes selected initial)
    (update rows columns (hermiteIncomingWorkspace width pivots) pivots)
    (updateAllowed rows columns (hermiteIncomingWorkspace width pivots) pivots)
    (update_realizable rows columns (hermiteIncomingWorkspace width pivots) pivots)
    (fun sizes selected _array initial count state => invariant rows columns width pivots sizes selected initial count state)
  · intro sizes selected array initial _valid
    exact starts rows columns width pivots sizes selected initial
  · intro sizes selected array initial valid index state before
    rw [valid.1]
    exact permits rows columns width pivots sizes selected initial state valid.2 index before
  · intro sizes selected array initial valid index state before
    rw [valid.1]
    exact preserves rows columns width pivots sizes selected initial state valid.2 index before

/-- Traverse all old pivots with a capacity derived from the original input widths. -/
noncomputable def hermiteIncomingController (rows columns width pivots : MvPolynomial Parameter ℕ) :
    Computation Parameter (Bool ⊕ Unit) where
  inputDomains := Sum.elim (context rows columns pivots)
    (fun _ : Unit => hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots))
  outputDomain := hermiteColumnState rows columns (hermiteIncomingWorkspace width pivots)
  precondition sizes arguments := initialAllowed rows columns width pivots sizes
    (fun name => arguments (.inl name)) (arguments (.inr ()))
  compute sizes arguments := ArrayFold.prefixValue
    (update rows columns (hermiteIncomingWorkspace width pivots) pivots sizes (fun name => arguments.val (.inl name)))
    id (arguments.val (.inr ())) (MvPolynomial.eval sizes pivots)

/-- Positive upper pivot data at the original width permits the controller. -/
theorem hermiteIncomingController_permitted (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (hermiteIncomingController rows columns width pivots).Arguments sizes)
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns))
    (rowEquation : successorValues pivots sizes (arguments (.inl false)) = selectedRows)
    (columnEquation : arguments (.inl true) = (fun index => pivotColumns index))
    (positive : ∀ index, 0 < (arguments (.inr ())).1.val (selectedRows index.castSucc) (pivotColumns index))
    (upper : ∀ row column : Fin (MvPolynomial.eval sizes pivots), column < row →
      (arguments (.inr ())).1.val (selectedRows row.castSucc) (pivotColumns column) = 0)
    (matrixBound : ∀ row column, ((arguments (.inr ())).1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width)
    (basisBound : ∀ row column, ((arguments (.inr ())).2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) :
    (hermiteIncomingController rows columns width pivots).precondition sizes arguments :=
  ⟨selectedRows, pivotColumns, rowEquation, columnEquation, positive, upper, matrixBound, basisBound⟩

/-- Canonical position enumeration, traversal, and every fixed-workspace update are certified. -/
theorem hermiteIncomingController_realizable (rows columns width pivots : MvPolynomial Parameter ℕ) :
    (hermiteIncomingController rows columns width pivots).Realizable := by
  let computation := hermiteIncomingController rows columns width pivots
  let results (name : Bool ⊕ Bool) sizes
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((controllerFold rows columns width pivots).inputDomains name).Carrier sizes :=
    match name with
    | .inl original => arguments.val (.inl original)
    | .inr false => arguments.val (.inr ())
    | .inr true => id
  have complete := (controllerFold_realizable rows columns width pivots).onResults computation.inputDomains
    computation.precondition results (fun _ arguments => ⟨rfl, arguments.property⟩) (by
      intro name
      rcases name with original | choice
      · exact Realizable.argument computation.inputDomains (.inl original) computation.precondition
      · cases choice
        · exact Realizable.argument computation.inputDomains (.inr ()) computation.precondition
        · exact (arrayPositions_realizable pivots).onResults computation.inputDomains computation.precondition
            (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim))
  exact complete.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- The controller returns the complete mathematical incoming traversal with both actual matrices. -/
theorem hermiteIncomingController_correct (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingController rows columns width pivots).Arguments sizes //
      (hermiteIncomingController rows columns width pivots).precondition sizes arguments})
    (selectedRows : Fin (MvPolynomial.eval sizes pivots + 1) ↪ Fin (MvPolynomial.eval sizes rows))
    (pivotColumns : Fin (MvPolynomial.eval sizes pivots) ↪ Fin (MvPolynomial.eval sizes columns))
    (rowEquation : successorValues pivots sizes (arguments.val (.inl false)) = selectedRows)
    (columnEquation : arguments.val (.inl true) = (fun index => pivotColumns index)) :
    let result := (hermiteIncomingController rows columns width pivots).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteIncomingPrefix selectedRows pivotColumns
      (MvPolynomial.eval sizes pivots) (arguments.val (.inr ())).1.val (arguments.val (.inr ())).2.val := by
  have complete := ArrayFold.prefix_invariant
    (update rows columns (hermiteIncomingWorkspace width pivots) pivots sizes (fun name => arguments.val (.inl name)))
    (id : Fin (MvPolynomial.eval sizes pivots) → Fin (MvPolynomial.eval sizes pivots)) (arguments.val (.inr ()))
    (invariant rows columns width pivots sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ())))
    (starts rows columns width pivots sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ())))
    (fun index state before => preserves rows columns width pivots sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr ())) state arguments.property index before) (MvPolynomial.eval sizes pivots) le_rfl
  exact complete selectedRows pivotColumns rowEquation columnEquation

/-- The complete traversal preserves the actual presentation and unimodular left basis. -/
theorem hermiteIncomingController_preserves (rows columns width pivots : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteIncomingController rows columns width pivots).Arguments sizes //
      (hermiteIncomingController rows columns width pivots).precondition sizes arguments})
    (original : Matrix (Fin (MvPolynomial.eval sizes rows)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (right : Matrix (Fin (MvPolynomial.eval sizes columns)) (Fin (MvPolynomial.eval sizes columns)) ℤ)
    (equation : (arguments.val (.inr ())).2.val * original * right = (arguments.val (.inr ())).1.val)
    (unit : IsUnit (arguments.val (.inr ())).2.val.det) :
    let result := (hermiteIncomingController rows columns width pivots).compute sizes arguments
    result.2.val * original * right = result.1.val ∧ IsUnit result.2.val.det := by
  obtain ⟨selectedRows, pivotColumns, rowEquation, columnEquation, _rest⟩ := arguments.property
  have actual := hermiteIncomingController_correct rows columns width pivots sizes arguments
    selectedRows pivotColumns rowEquation columnEquation
  have mathematical := IntegerMatrix.hermiteIncomingPrefix_preserves selectedRows pivotColumns
    (MvPolynomial.eval sizes pivots) (arguments.val (.inr ())).1.val original
    (arguments.val (.inr ())).2.val right equation unit
  constructor
  · exact (congrArg (fun basis => basis * original * right) (congrArg Prod.snd actual)).trans
      (mathematical.1.trans (congrArg Prod.fst actual).symm)
  · exact (congrArg (fun basis => IsUnit basis.det) (congrArg Prod.snd actual)).mpr mathematical.2

end Polytime2.Computation.Realizable.Internal
