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

import Polytime2.Matrices.HermiteColumnUpdate
import Polytime2.Matrices.HermiteColumnTraversalMath
import Polytime2.Arrays.BoundedPositions

/-! # A certified bounded Hermite column controller

Visit every row in increasing order and skip the source. The fixed matrix and
basis workspace is derived from the original width and row count. Agreement
with the mathematical prefix supplies every update's logical narrowing proof;
the runtime performs no coefficient-bound checks. The initial matrix and basis
are already widened here; a public preparation wrapper can derive that storage.
This controller reduces one column, not a complete Hermite or Smith form.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Derived workspace for all prefixes of one column traversal. -/
noncomputable def hermiteColumnWorkspace (rows width : MvPolynomial Parameter ℕ) := width + rows * (2 * width + 2)

private def stateValues (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) := (state.1.val, state.2.val)

private def initialAllowed (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes) :=
  0 < initial.1.val (context false) (context true) ∧
    (∀ row column, (initial.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, (initial.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width)

private def prefixInvariant (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes)
    (count : ℕ) (state : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes) :=
  stateValues rows columns (hermiteColumnWorkspace rows width) sizes state =
    IntegerMatrix.hermiteColumnPrefix (rows := MvPolynomial.eval sizes rows)
      (context false) (context true) count initial.1.val initial.2.val

private theorem prefix_starts (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (initial : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes) :
    prefixInvariant rows columns width sizes context initial 0 initial := rfl

private theorem prefix_permits (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes)
    (valid : initialAllowed rows columns width sizes context initial) (index : Fin (MvPolynomial.eval sizes rows))
    (invariant : prefixInvariant rows columns width sizes context initial index.val state) :
    hermiteColumnUpdateAllowed rows columns width (hermiteColumnWorkspace rows width) sizes context state index := by
  intro different
  have positive := (IntegerMatrix.hermiteColumnPrefix_entries (rows := MvPolynomial.eval sizes rows)
    (Column := Fin (MvPolynomial.eval sizes columns)) (context false) (context true) index.val initial.1.val initial.2.val valid.1).1
  have bounds := IntegerMatrix.hermiteColumnPrefix_bound (rows := MvPolynomial.eval sizes rows)
    (Column := Fin (MvPolynomial.eval sizes columns)) (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width)
    (MvPolynomial.eval sizes width) (context false) (context true) index.val initial.1.val initial.2.val valid.1
    (fun row => valid.2.1 row (context true)) valid.2.1 valid.2.2
  have pivotBound := (IntegerMatrix.hermiteColumnSweep_pivot_le
    (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
    (context false) (context true) (IntegerMatrix.hermiteColumnTargets (context false) index.val)
    (IntegerMatrix.hermiteColumnTargets_excluded (context false) index.val) initial.1.val initial.2.val valid.1).trans_lt
      (valid.2.1 (context false) (context true))
  have targetExcluded : index ∉ IntegerMatrix.hermiteColumnTargets (context false) index.val := by
    simp [IntegerMatrix.hermiteColumnTargets_mem]
  have targetBound : ((IntegerMatrix.hermiteColumnPrefix (context false) (context true) index.val initial.1.val initial.2.val).1
      index (context true)).natAbs < 2 ^ MvPolynomial.eval sizes width := by
    rw [IntegerMatrix.hermiteColumnPrefix, IntegerMatrix.hermiteColumnSweep_other
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (context false) index different (context true) (context true) _ targetExcluded initial.1.val initial.2.val]
    exact valid.2.1 index (context true)
  have room : MvPolynomial.eval sizes width + index.val * (2 * MvPolynomial.eval sizes width + 2) +
      (2 * MvPolynomial.eval sizes width + 2) ≤ MvPolynomial.eval sizes (hermiteColumnWorkspace rows width) := by
    have budget := Nat.mul_le_mul_right (2 * MvPolynomial.eval sizes width + 2) (Nat.succ_le_of_lt index.isLt)
    simp only [hermiteColumnWorkspace, map_add, map_mul, map_ofNat] at *
    nlinarith
  have matrixEqual := congrArg Prod.fst invariant
  have basisEqual := congrArg Prod.snd invariant
  change state.1.val = _ at matrixEqual
  change state.2.val = _ at basisEqual
  change ((context false ≠ index ∧ 0 < state.1.val (context false) (context true)) ∧
    (state.1.val (context false) (context true)).natAbs < 2 ^ MvPolynomial.eval sizes width ∧
    (state.1.val index (context true)).natAbs < 2 ^ MvPolynomial.eval sizes width ∧
    ∃ logicalWidth : ℕ, (∀ row column, (state.1.val row column).natAbs < 2 ^ logicalWidth) ∧
      (∀ row column, (state.2.val row column).natAbs < 2 ^ logicalWidth) ∧
      logicalWidth + (2 * MvPolynomial.eval sizes width + 2) ≤ MvPolynomial.eval sizes (hermiteColumnWorkspace rows width))
  rw [matrixEqual, basisEqual]
  exact ⟨⟨different.symm, positive⟩, pivotBound, targetBound,
    MvPolynomial.eval sizes width + index.val * (2 * MvPolynomial.eval sizes width + 2), bounds.1, bounds.2, room⟩

private theorem prefix_preserves (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)).Carrier sizes)
    (valid : initialAllowed rows columns width sizes context initial) (index : Fin (MvPolynomial.eval sizes rows))
    (invariant : prefixInvariant rows columns width sizes context initial index.val state) :
    prefixInvariant rows columns width sizes context initial (index.val + 1)
      (hermiteColumnUpdate rows columns width (hermiteColumnWorkspace rows width) sizes context state index) := by
  have permitted := prefix_permits rows columns width sizes context initial state valid index invariant
  unfold prefixInvariant
  rw [IntegerMatrix.hermiteColumnPrefix_succ]
  by_cases same : index = context false
  · simp only [ite_eq_left same, hermiteColumnUpdate]
    exact invariant
  · rw [ite_eq_right same]
    have computed := hermiteColumnUpdate_correct rows columns width (hermiteColumnWorkspace rows width)
      sizes context state index same permitted
    exact computed.trans (congrArg (fun matrices => IntegerMatrix.hermiteRowStep
      (Row := Fin (MvPolynomial.eval sizes rows)) (Column := Fin (MvPolynomial.eval sizes columns))
      (context false) index (context true) matrices.1 matrices.2) invariant)

private noncomputable def controllerFold (rows columns width : MvPolynomial Parameter ℕ) :=
  arrayFold (hermiteColumnContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)) rows
    (fun sizes context array initial => array = id ∧ initialAllowed rows columns width sizes context initial)
    (hermiteColumnUpdate rows columns width (hermiteColumnWorkspace rows width))

private theorem controllerFold_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (controllerFold rows columns width).Realizable := by
  apply arrayFold_realizable (hermiteColumnContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (hermiteColumnWorkspace rows width)) rows
    (fun sizes context array initial => array = id ∧ initialAllowed rows columns width sizes context initial)
    (hermiteColumnUpdate rows columns width (hermiteColumnWorkspace rows width))
    (hermiteColumnUpdateAllowed rows columns width (hermiteColumnWorkspace rows width))
    (hermiteColumnUpdate_realizable rows columns width (hermiteColumnWorkspace rows width))
    (fun sizes context _array initial count state => prefixInvariant rows columns width sizes context initial count state)
  · intro sizes context array initial _valid
    exact prefix_starts rows columns width sizes context initial
  · intro sizes context array initial valid index state invariant
    rw [valid.1]
    exact prefix_permits rows columns width sizes context initial state valid.2 index invariant
  · intro sizes context array initial valid index state invariant
    rw [valid.1]
    exact prefix_preserves rows columns width sizes context initial state valid.2 index invariant

/-- Traverse one column using a fixed polynomial workspace and canonical row enumeration. -/
noncomputable def hermiteColumnController (rows columns width : MvPolynomial Parameter ℕ) :
    Computation Parameter (Bool ⊕ Unit) where
  inputDomains := Sum.elim (hermiteColumnContext rows columns)
    (fun _ : Unit => hermiteColumnState rows columns (hermiteColumnWorkspace rows width))
  outputDomain := hermiteColumnState rows columns (hermiteColumnWorkspace rows width)
  precondition sizes arguments := initialAllowed rows columns width sizes (fun name => arguments (.inl name)) (arguments (.inr ()))
  compute sizes arguments := ArrayFold.prefixValue
    (hermiteColumnUpdate rows columns width (hermiteColumnWorkspace rows width) sizes (fun name => arguments.val (.inl name)))
    id (arguments.val (.inr ())) (MvPolynomial.eval sizes rows)

theorem hermiteColumnController_realizable (rows columns width : MvPolynomial Parameter ℕ) :
    (hermiteColumnController rows columns width).Realizable := by
  let computation := hermiteColumnController rows columns width
  let results (name : Bool ⊕ Bool) sizes
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((controllerFold rows columns width).inputDomains name).Carrier sizes :=
    match name with
    | .inl original => arguments.val (.inl original)
    | .inr false => arguments.val (.inr ())
    | .inr true => id
  have complete := (controllerFold_realizable rows columns width).onResults computation.inputDomains computation.precondition results
    (fun _ arguments => ⟨rfl, arguments.property⟩) (by
      intro name
      rcases name with original | choice
      · exact Realizable.argument computation.inputDomains (.inl original) computation.precondition
      · cases choice
        · exact Realizable.argument computation.inputDomains (.inr ()) computation.precondition
        · exact (arrayBoundedPositions_realizable rows).onResults computation.inputDomains computation.precondition
            (fun impossible => impossible.elim) (by intros; trivial) (fun impossible => impossible.elim))
  exact complete.withSpecification computation.precondition computation.compute (by intros; assumption) (by intros; rfl)

/-- The runtime controller agrees with the mathematical traversal after every row. -/
theorem hermiteColumnController_correct (rows columns width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (hermiteColumnController rows columns width).Arguments sizes //
      (hermiteColumnController rows columns width).precondition sizes arguments}) :
    let result := (hermiteColumnController rows columns width).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.hermiteColumnPrefix
      (rows := MvPolynomial.eval sizes rows) ((arguments.val (.inl false))) ((arguments.val (.inl true)))
      (MvPolynomial.eval sizes rows) (arguments.val (.inr ())).1.val (arguments.val (.inr ())).2.val := by
  have invariant := ArrayFold.prefix_invariant
    (hermiteColumnUpdate rows columns width (hermiteColumnWorkspace rows width) sizes (fun name => arguments.val (.inl name)))
    (id : Fin (MvPolynomial.eval sizes rows) → Fin (MvPolynomial.eval sizes rows)) (arguments.val (.inr ()))
    (prefixInvariant rows columns width sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ())))
    (prefix_starts rows columns width sizes (fun name => arguments.val (.inl name)) (arguments.val (.inr ())))
    (fun index state valid => prefix_preserves rows columns width sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr ())) state arguments.property index valid) (MvPolynomial.eval sizes rows) le_rfl
  exact invariant

end Polytime2.Computation.Realizable.Internal
