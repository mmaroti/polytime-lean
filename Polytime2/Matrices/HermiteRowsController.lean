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

import Polytime2.Computation.Specification
import Polytime2.Matrices.HermiteRowsStep
import Polytime2.Arrays.FoldContract
import Polytime2.Arrays.BoundedPositions
import Polytime2.Matrices.Identity

/-! # Complete fixed-workspace outer Hermite row traversal

Traverse the canonical row coordinates. Each state is exactly the corresponding
mathematical prefix of the immutable original input, and both matrices stay in
one original-input-derived workspace.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def stateDomain (rows columns width : MvPolynomial Parameter ℕ) :=
  (integerHermiteRowsStep rows columns width).outputDomain

private def values (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (stateDomain rows columns width).Carrier sizes) :
    IntegerMatrix.HermiteRowState (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) :=
  ((state.1.1.val, state.1.2.val), state.2)

private def updateArguments (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (stateDomain rows columns width).Carrier sizes) (source : (boundedIndex rows).Carrier sizes) :
    (integerHermiteRowsStep rows columns width).Arguments sizes :=
  fun _ name => match name with | 0 => (state.2, source) | 1 => state.1.1 | 2 => state.1.2

private def allowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (_original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (state : (stateDomain rows columns width).Carrier sizes) (source : (boundedIndex rows).Carrier sizes) :=
  (integerHermiteRowsStep rows columns width).precondition sizes (updateArguments rows columns width sizes state source)

private noncomputable def update (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (state : (stateDomain rows columns width).Carrier sizes) (source : (boundedIndex rows).Carrier sizes) :=
  ArrayFold.extend (allowed rows columns width sizes original)
    (fun state source valid => (integerHermiteRowsStep rows columns width).compute sizes
      ⟨updateArguments rows columns width sizes state source, valid⟩) state source

private theorem update_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (fun _ : Unit => integerMatrices rows columns width) (boundedIndex rows) (stateDomain rows columns width)
      (allowed rows columns width) (update rows columns width)).Realizable := by
  apply arrayFoldStep_of_partial_realizable
  let state := stateDomain rows columns width
  let step := arrayFoldStep (fun _ : Unit => integerMatrices rows columns width) (boundedIndex rows) state
    (allowed rows columns width) (update rows columns width)
  let capacity := hermiteRowsWorkspace width rows
  let matrix := integerMatrices rows columns capacity
  let basis := integerMatrices rows rows capacity
  let metadata := hermitePivotSelection rows columns
  let fields : Fin 3 → EncodedDomain Parameter
    | 0 => metadata.prod (boundedIndex rows) | 1 => matrix | 2 => basis
  have source := Realizable.argument step.inputDomains (.inr true) step.precondition
  have pair := (Realizable.argument step.inputDomains (.inr false) step.precondition).fst
  have recordReady := Realizable.recordOutputs step.inputDomains 3 fields step.precondition
    (fun name sizes arguments => updateArguments rows columns width sizes
      (arguments.val (.inr false)) (arguments.val (.inr true)) () name) (by
        intro name
        fin_cases name
        · exact (((Realizable.argument step.inputDomains (.inr false) step.precondition).snd).prodMk source)
        · exact pair.fst
        · exact pair.snd)
  exact (integerHermiteRowsStep_realizable rows columns width).onResults step.inputDomains step.precondition
    (fun _ sizes arguments => updateArguments rows columns width sizes
      (arguments.val (.inr false)) (arguments.val (.inr true)) ())
    (by intro sizes arguments; exact arguments.property) (by intro name; cases name; exact recordReady)

private def invariant (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (count : ℕ) (state : (stateDomain rows columns width).Carrier sizes) : Prop :=
  ∃ within : count ≤ MvPolynomial.eval sizes rows,
    values rows columns width sizes state = (IntegerMatrix.hermiteRowsPrefix (original ()).val count within).val

private def initialAllowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (initial : (stateDomain rows columns width).Carrier sizes) :=
  values rows columns width sizes initial =
    (IntegerMatrix.hermiteRowsPrefix (original ()).val 0 (Nat.zero_le _)).val

private theorem permits (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (source : Fin (MvPolynomial.eval sizes rows)) (state : (stateDomain rows columns width).Carrier sizes)
    (before : invariant rows columns width sizes original source.val state) :
    allowed rows columns width sizes original state source := by
  obtain ⟨within, same⟩ := before
  exact ⟨original (), same⟩

private theorem preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (original : ∀ _ : Unit, (integerMatrices rows columns width).Carrier sizes)
    (source : Fin (MvPolynomial.eval sizes rows)) (state : (stateDomain rows columns width).Carrier sizes)
    (before : invariant rows columns width sizes original source.val state) :
    invariant rows columns width sizes original (source.val + 1) (update rows columns width sizes original state source) := by
  classical
  have valid := permits rows columns width sizes original source state before
  obtain ⟨within, same⟩ := before
  refine ⟨source.isLt, ?_⟩
  dsimp only [update]
  rw [ArrayFold.extend_of_allowed valid]
  exact integerHermiteRowsStep_correct rows columns width sizes
    ⟨updateArguments rows columns width sizes state source, valid⟩ (original ()) same

private noncomputable def controllerFold (rows columns width : MvPolynomial Parameter ℕ) :=
  arrayFold (fun _ : Unit => integerMatrices rows columns width) (boundedIndex rows) (stateDomain rows columns width) rows
    (fun sizes original array initial => array = id ∧ initialAllowed rows columns width sizes original initial)
    (update rows columns width)

private theorem controllerFold_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (controllerFold rows columns width).Realizable := by
  apply arrayFold_realizable (fun _ : Unit => integerMatrices rows columns width) (boundedIndex rows)
    (stateDomain rows columns width) rows
    (fun sizes original array initial => array = id ∧ initialAllowed rows columns width sizes original initial)
    (update rows columns width) (allowed rows columns width) (update_realizable rows columns width)
    (fun sizes original _array _initial count state => invariant rows columns width sizes original count state)
  · intro sizes original array initial valid
    exact ⟨Nat.zero_le _, valid.2⟩
  · intro sizes original array initial valid index state before
    rw [valid.1]
    exact permits rows columns width sizes original index state before
  · intro sizes original array initial valid index state before
    rw [valid.1]
    exact preserves rows columns width sizes original index state before

/-- Traverse all rows from the canonical initial state at one fixed polynomial width. -/
noncomputable def hermiteRowsController (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter (Unit ⊕ Unit) :=
  (controllerFold rows columns width).onResults
    (Sum.elim (fun _ => integerMatrices rows columns width) (fun _ => stateDomain rows columns width))
    (fun sizes arguments => initialAllowed rows columns width sizes (fun _ => arguments (.inl ())) (arguments (.inr ())))
    (fun name _ arguments => match name with
      | .inl _ => arguments.val (.inl ())
      | .inr false => arguments.val (.inr ())
      | .inr true => id)
    (by intro sizes arguments; exact ⟨rfl, arguments.property⟩)

/-- The outer fold includes canonical coordinate preparation and all transition costs. -/
theorem hermiteRowsController_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (hermiteRowsController rows columns width).Realizable := by
  let computation := hermiteRowsController rows columns width
  apply (controllerFold_realizable rows columns width).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | .inl _ => arguments.val (.inl ())
      | .inr false => arguments.val (.inr ())
      | .inr true => id) (by intro sizes arguments; exact ⟨rfl, arguments.property⟩)
  intro name
  rcases name with singleton | choice
  · exact Realizable.argument computation.inputDomains (.inl ()) computation.precondition
  · cases choice
    · exact Realizable.argument computation.inputDomains (.inr ()) computation.precondition
    · exact (arrayBoundedPositions_realizable rows).onResults computation.inputDomains computation.precondition
        (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)

/-- The complete runtime row controller returns the mathematical Hermite row sweep. -/
theorem hermiteRowsController_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteRowsController rows columns width).Arguments sizes //
      (hermiteRowsController rows columns width).precondition sizes arguments}) :
    let result := (hermiteRowsController rows columns width).compute sizes arguments
    (((result.1.1.val, result.1.2.val), result.2) : IntegerMatrix.HermiteRowState
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)) =
      IntegerMatrix.hermiteRowsSweep (arguments.val (.inl ())).val := by
  have reached := ArrayFold.prefix_invariant (update rows columns width sizes (fun _ => arguments.val (.inl ())))
    (id : Fin (MvPolynomial.eval sizes rows) → Fin (MvPolynomial.eval sizes rows)) (arguments.val (.inr ()))
    (invariant rows columns width sizes (fun _ => arguments.val (.inl ())))
    ⟨Nat.zero_le _, arguments.property⟩
    (fun index state before => preserves rows columns width sizes (fun _ => arguments.val (.inl ())) index state before)
  obtain ⟨within, same⟩ := reached
  exact same

private noncomputable def initial (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := integerMatrices rows columns width
  outputDomain := stateDomain rows columns width
  precondition _ _ := True
  compute sizes arguments :=
    let state := (IntegerMatrix.hermiteRowsPrefix (arguments.val ()).val 0 (Nat.zero_le _)).val
    let bounded := hermiteRowsWorkspace_bound rows columns width sizes (arguments.val ()).val
      (arguments.val ()).property 0 (Nat.zero_le _)
    ((⟨state.1.1, bounded.1⟩, ⟨state.1.2, bounded.2⟩), state.2)

private theorem initial_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (initial rows columns width).Realizable := by
  let computation := initial rows columns width
  let capacity := hermiteRowsWorkspace width rows
  have matrixReady := integerMatrixResize_realizable rows columns width capacity
  have identity := (integerIdentity_realizable rows).onResults computation.inputDomains computation.precondition
    (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  have basisReady := identity.followedBy (integerMatrixResize_realizable rows rows 1 capacity) rfl (by
    intro sizes arguments valid
    exact (hermiteRowsWorkspace_bound rows columns width sizes (arguments ()).val
      (arguments ()).property 0 (Nat.zero_le _)).2)
  have boundedMatrix := matrixReady.withPrecondition computation.precondition (by
    intro sizes arguments valid
    exact (hermiteRowsWorkspace_bound rows columns width sizes (arguments ()).val
      (arguments ()).property 0 (Nat.zero_le _)).1)
  have metadata := (hermitePivotSelectionEmpty_realizable rows columns).onResults computation.inputDomains computation.precondition
    (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim)
  exact ((boundedMatrix.prodMk basisReady).prodMk metadata).withSpecification computation.precondition computation.compute (by intros; trivial) (by intros; rfl)

/-- Complete integer row normalization with actual basis and pivot embeddings.
The original matrix bound is the only input requirement; all storage is derived. -/
private noncomputable def sweepImplementation (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (hermiteRowsController rows columns width).onResults (fun _ => integerMatrices rows columns width) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl _ => arguments.val ()
      | .inr _ => (initial rows columns width).compute sizes arguments)
    (by intros; rfl)

/-- Initial widening, identity, empty metadata, row enumeration, and the complete fold are realized. -/
private theorem sweepImplementation_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (sweepImplementation rows columns width).Realizable := by
  apply (hermiteRowsController_realizable rows columns width).onResults
    (fun _ : Unit => integerMatrices rows columns width) (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl _ => arguments.val ()
      | .inr _ => (initial rows columns width).compute sizes arguments)
    (by intros; rfl)
  intro name
  cases name
  · exact Realizable.argument (fun _ : Unit => integerMatrices rows columns width) () (fun _ _ => True)
  · exact initial_realizable rows columns width

/-- The public runtime sweep equals the complete mathematical row traversal. -/
private theorem sweepImplementation_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (sweepImplementation rows columns width).Arguments sizes //
      (sweepImplementation rows columns width).precondition sizes arguments}) :
    let result := (sweepImplementation rows columns width).compute sizes arguments
    (((result.1.1.val, result.1.2.val), result.2) : IntegerMatrix.HermiteRowState
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)) = IntegerMatrix.hermiteRowsSweep (arguments.val ()).val :=
  hermiteRowsController_correct rows columns width sizes
    ⟨(fun name => match name with
      | .inl _ => arguments.val ()
      | .inr _ => (initial rows columns width).compute sizes arguments), by rfl⟩

/-- The complete mathematical row traversal, with its actual basis and pivots. -/
noncomputable def integerHermiteRows (rows columns width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => integerMatrices rows columns width)
    (((integerMatrices rows columns (hermiteRowsWorkspace width rows)).prod
      (integerMatrices rows rows (hermiteRowsWorkspace width rows))).prod (hermitePivotSelection rows columns))
    (fun _ _ => True) (fun _ result => ((result.1.1.val, result.1.2.val), result.2))
    (fun _ arguments => IntegerMatrix.hermiteRowsSweep (arguments.val ()).val)
    (fun sizes arguments => ⟨(sweepImplementation rows columns width).compute sizes arguments,
      sweepImplementation_correct rows columns width sizes arguments⟩)

theorem integerHermiteRows_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (integerHermiteRows rows columns width).Realizable := by
  apply (sweepImplementation_realizable rows columns width).specificationBy
  · intro sizes
    exact (Subtype.val_injective.prodMap Subtype.val_injective).prodMap Function.injective_id
  · intro sizes arguments valid
    exact sweepImplementation_correct rows columns width sizes ⟨arguments, valid⟩

/-- Observe the complete mathematical traversal without expanding the controller. -/
theorem integerHermiteRows_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRows rows columns width).Arguments sizes //
      (integerHermiteRows rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRows rows columns width).compute sizes arguments
    (((result.1.1.val, result.1.2.val), result.2) : IntegerMatrix.HermiteRowState
      (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns)) = IntegerMatrix.hermiteRowsSweep (arguments.val ()).val := by
  exact specificationBy_correct _ (integerHermiteRows rows columns width).outputDomain _
    (fun _ result => ((result.1.1.val, result.1.2.val), result.2)) _ _ sizes arguments

/-- Full sweep correctness includes actual presentation, unimodularity, and normalized active pivots. -/
theorem integerHermiteRows_specification (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteRows rows columns width).Arguments sizes //
      (integerHermiteRows rows columns width).precondition sizes arguments}) :
    let result := (integerHermiteRows rows columns width).compute sizes arguments
    IntegerMatrix.HermiteRowPrefix (arguments.val ()).val (MvPolynomial.eval sizes rows)
      ((result.1.1.val, result.1.2.val), result.2) := by
  dsimp only
  rw [integerHermiteRows_correct]
  exact IntegerMatrix.hermiteRowsSweep_correct (arguments.val ()).val

end Polytime2.Computation
