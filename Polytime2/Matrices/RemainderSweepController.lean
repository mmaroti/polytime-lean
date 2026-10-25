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

import Polytime2.Matrices.IntegerEuclideanReduction
import Polytime2.Matrices.IntegerPairNarrow
import Polytime2.Matrices.HermiteColumnUpdate
import Polytime2.Matrices.EuclideanSweepMath
import Polytime2.Arrays.FoldContract

/-! # Fixed-pivot Euclidean remainder sweeps

Reduce distinct selected target rows against one positive source pivot. The
source is excluded from the targets. Every prefix and both actual matrices fit
the same derived width, independently of the number of selected rows.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private def updateArguments (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (target : (boundedIndex rows).Carrier sizes) :
    (integerRowRemainderWithLeft rows columns workspace).Arguments sizes
  | 0 => context false | 1 => target | 2 => context true | 3 => state.1 | 4 => state.2

private def updateAllowed (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (target : (boundedIndex rows).Carrier sizes) :=
  context false ≠ target ∧ 0 < state.1.val (context false) (context true) ∧
    let result := IntegerMatrix.rowRemainderWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (context false) target (context true) state.1.val state.2.val
    (∀ row column, (result.1 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace) ∧
    (∀ row column, (result.2 row column).natAbs < 2 ^ MvPolynomial.eval sizes workspace)

private noncomputable def update (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (target : (boundedIndex rows).Carrier sizes) :
    (hermiteColumnState rows columns workspace).Carrier sizes :=
  ArrayFold.extend (updateAllowed rows columns workspace sizes context)
    (fun state target valid =>
      let result := IntegerMatrix.rowRemainderWithLeft
        (Row := Fin (MvPolynomial.eval sizes rows)) (context false) target (context true) state.1.val state.2.val
      (⟨result.1, valid.2.2.1⟩, ⟨result.2, valid.2.2.2⟩)) state target

private theorem update_realizable (rows columns workspace : MvPolynomial Parameter ℕ) :
    (arrayFoldStep (hermiteColumnContext rows columns) (boundedIndex rows) (hermiteColumnState rows columns workspace)
      (updateAllowed rows columns workspace) (update rows columns workspace)).Realizable := by
  apply arrayFoldStep_of_partial_realizable
  let step := arrayFoldStep (hermiteColumnContext rows columns) (boundedIndex rows) (hermiteColumnState rows columns workspace)
    (updateAllowed rows columns workspace) (update rows columns workspace)
  have raw := (integerRowRemainderWithLeft_realizable rows columns workspace).onResults
    step.inputDomains step.precondition
    (fun name sizes arguments => updateArguments rows columns workspace sizes
      (fun original => arguments.val (.inl original)) (arguments.val (.inr false)) (arguments.val (.inr true)) name)
    (by intro sizes arguments; exact ⟨arguments.property.1, arguments.property.2.1⟩) (by
      intro name
      fin_cases name
      · exact Realizable.argument step.inputDomains (.inl false) step.precondition
      · exact Realizable.argument step.inputDomains (.inr true) step.precondition
      · exact Realizable.argument step.inputDomains (.inl true) step.precondition
      · exact (Realizable.argument step.inputDomains (.inr false) step.precondition).fst
      · exact (Realizable.argument step.inputDomains (.inr false) step.precondition).snd)
  have observed (sizes : Parameter → ℕ) (arguments : step.Arguments sizes)
      (valid : step.precondition sizes arguments) := integerRowRemainderWithLeft_correct rows columns workspace sizes
    ⟨(fun name => updateArguments rows columns workspace sizes
      (fun original => arguments (.inl original)) (arguments (.inr false)) (arguments (.inr true)) name),
      ⟨valid.1, valid.2.1⟩⟩
  have narrowed := raw.followedBy
    (integerMatrixPairNarrow_realizable rows columns rows rows (2 * workspace + 1) (2 * workspace + 1) workspace
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)
      (by intro sizes; simp only [map_add, map_mul, map_ofNat, map_one]; omega)) rfl
    (by
      intro sizes arguments valid
      have actual := observed sizes arguments valid
      have first := congrArg Prod.fst actual
      have second := congrArg Prod.snd actual
      dsimp only at first second
      change (∀ row column, _) ∧ (∀ row column, _)
      constructor
      · intro row column
        exact lt_of_eq_of_lt (congrArg Int.natAbs (congrFun (congrFun first row) column))
          (valid.2.2.1 row column)
      · intro row column
        exact lt_of_eq_of_lt (congrArg Int.natAbs (congrFun (congrFun second row) column))
          (valid.2.2.2 row column))
  apply narrowed.withSpecification _ _ (by intros; assumption)
  intro sizes arguments valid
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst (observed sizes arguments valid)
  · exact congrArg Prod.snd (observed sizes arguments valid)

private theorem update_correct (rows columns workspace : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (state : (hermiteColumnState rows columns workspace).Carrier sizes) (target : (boundedIndex rows).Carrier sizes)
    (valid : updateAllowed rows columns workspace sizes context state target) :
    let result := update rows columns workspace sizes context state target
    (result.1.val, result.2.val) = IntegerMatrix.rowRemainderWithLeft
      (Row := Fin (MvPolynomial.eval sizes rows)) (context false) target (context true) state.1.val state.2.val := by
  simp only [update, ArrayFold.extend_of_allowed valid]
  rfl

private def initialAllowed (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (targets : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes) :=
  (List.ofFn targets).Nodup ∧ context false ∉ List.ofFn targets ∧
    0 < initial.1.val (context false) (context true) ∧
    (∀ row column, (initial.1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
    (∀ row column, (initial.2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width)

private def invariant (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (targets : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial : (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes) (count : ℕ)
    (state : (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes) :=
  (state.1.val, state.2.val) = IntegerMatrix.rowRemainderSweep
    (Row := Fin (MvPolynomial.eval sizes rows)) (context false) (context true)
    ((List.ofFn targets).take count) initial.1.val initial.2.val

private theorem permits (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (targets : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes)
    (valid : initialAllowed rows columns width length sizes context targets initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (before : invariant rows columns width length sizes context targets initial index.val state) :
    updateAllowed rows columns (2 * width + 1) sizes context state (targets index) := by
  have excluded : context false ∉ (List.ofFn targets).take index.val :=
    fun member => valid.2.1 (List.mem_of_mem_take member)
  have prefixFormula := (IntegerMatrix.rowRemainderSweep_apply (Row := Fin (MvPolynomial.eval sizes rows))
    (context false) (context true) _ valid.1.take excluded initial.1.val initial.2.val).1 (context false) (context true)
  have sourceUnchanged := (congrFun (congrFun (congrArg Prod.fst before) (context false)) (context true)).trans
    (by simpa only [ite_eq_right excluded] using prefixFormula)
  have next := IntegerMatrix.rowRemainderSweep_prefix_succ (Row := Fin (MvPolynomial.eval sizes rows))
    (context false) (context true) targets valid.1 valid.2.1 index initial.1.val initial.2.val
  have moved := congrArg (fun pair => IntegerMatrix.rowRemainderWithLeft
    (Row := Fin (MvPolynomial.eval sizes rows)) (context false) (targets index) (context true) pair.1 pair.2) before
  have nextEquation := moved.trans next.symm
  have nextExcluded : context false ∉ (List.ofFn targets).take (index.val + 1) :=
    fun member => valid.2.1 (List.mem_of_mem_take member)
  have bounds := IntegerMatrix.rowRemainderSweep_bound (Row := Fin (MvPolynomial.eval sizes rows))
    (MvPolynomial.eval sizes width) (MvPolynomial.eval sizes width) (context false) (context true)
    ((List.ofFn targets).take (index.val + 1)) valid.1.take nextExcluded initial.1.val initial.2.val valid.2.2.2.1 valid.2.2.2.2
  have capacity : MvPolynomial.eval sizes (2 * width + 1) = 2 * MvPolynomial.eval sizes width + 1 := by simp
  refine ⟨?_, lt_of_lt_of_eq valid.2.2.1 sourceUnchanged.symm, ?_, ?_⟩
  · intro same
    exact valid.2.1 (List.mem_ofFn.mpr ⟨index, same.symm⟩)
  · intro row column
    have sameEntry := congrFun (congrFun (congrArg Prod.fst nextEquation) row) column
    exact lt_of_eq_of_lt (congrArg Int.natAbs sameEntry) (by simpa only [capacity] using bounds.1 row column)
  · intro row column
    have sameEntry := congrFun (congrFun (congrArg Prod.snd nextEquation) row) column
    exact lt_of_eq_of_lt (congrArg Int.natAbs sameEntry) (by
      have basisCapacity : MvPolynomial.eval sizes (2 * width + 1) =
          MvPolynomial.eval sizes width + MvPolynomial.eval sizes width + 1 := by
        rw [capacity]
        omega
      simpa only [basisCapacity] using bounds.2 row column)

private theorem preserves (rows columns width length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (context : ∀ name, (hermiteColumnContext rows columns name).Carrier sizes)
    (targets : ((boundedIndex rows).arrayOfLength length).Carrier sizes)
    (initial state : (hermiteColumnState rows columns (2 * width + 1)).Carrier sizes)
    (valid : initialAllowed rows columns width length sizes context targets initial)
    (index : Fin (MvPolynomial.eval sizes length))
    (before : invariant rows columns width length sizes context targets initial index.val state) :
    invariant rows columns width length sizes context targets initial (index.val + 1)
      (update rows columns (2 * width + 1) sizes context state (targets index)) := by
  have actual := update_correct rows columns (2 * width + 1) sizes context state (targets index)
    (permits rows columns width length sizes context targets initial state valid index before)
  have moved := congrArg (fun pair => IntegerMatrix.rowRemainderWithLeft
    (Row := Fin (MvPolynomial.eval sizes rows)) (context false) (targets index) (context true) pair.1 pair.2) before
  exact actual.trans (moved.trans (IntegerMatrix.rowRemainderSweep_prefix_succ
    (Row := Fin (MvPolynomial.eval sizes rows)) (context false) (context true) targets valid.1 valid.2.1
    index initial.1.val initial.2.val).symm)

/-- Normalize a distinct target-row array in one fixed polynomial workspace. -/
noncomputable def remainderSweepController (rows columns width length : MvPolynomial Parameter ℕ) :=
  arrayFold (hermiteColumnContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (2 * width + 1)) length (initialAllowed rows columns width length)
    (update rows columns (2 * width + 1))

/-- Every prefix uses the original-input additive width bound. -/
theorem remainderSweepController_realizable (rows columns width length : MvPolynomial Parameter ℕ) :
    (remainderSweepController rows columns width length).Realizable := by
  apply arrayFold_realizable (hermiteColumnContext rows columns) (boundedIndex rows)
    (hermiteColumnState rows columns (2 * width + 1)) length (initialAllowed rows columns width length)
    (update rows columns (2 * width + 1)) (updateAllowed rows columns (2 * width + 1))
    (update_realizable rows columns (2 * width + 1)) (invariant rows columns width length)
  · intros; rfl
  · intro sizes context targets initial valid index state before
    exact permits rows columns width length sizes context targets initial state valid index before
  · intro sizes context targets initial valid index state before
    exact preserves rows columns width length sizes context targets initial state valid index before

/-- The controller requires only distinct nonsource targets and original-width positive-pivot data. -/
theorem remainderSweepController_precondition (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : (remainderSweepController rows columns width length).Arguments sizes) :
    (remainderSweepController rows columns width length).precondition sizes arguments ↔
      (List.ofFn (arguments (.inr true))).Nodup ∧ arguments (.inl false) ∉ List.ofFn (arguments (.inr true)) ∧
      0 < (arguments (.inr false)).1.val (arguments (.inl false)) (arguments (.inl true)) ∧
      (∀ row column, ((arguments (.inr false)).1.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) ∧
      (∀ row column, ((arguments (.inr false)).2.val row column).natAbs < 2 ^ MvPolynomial.eval sizes width) := Iff.rfl

/-- The realized array fold is exactly the complete mathematical remainder sweep. -/
theorem remainderSweepController_correct (rows columns width length : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (remainderSweepController rows columns width length).Arguments sizes //
      (remainderSweepController rows columns width length).precondition sizes arguments}) :
    let result := (remainderSweepController rows columns width length).compute sizes arguments
    (result.1.val, result.2.val) = IntegerMatrix.rowRemainderSweep
      (Row := Fin (MvPolynomial.eval sizes rows)) (arguments.val (.inl false)) (arguments.val (.inl true))
      (List.ofFn (arguments.val (.inr true))) (arguments.val (.inr false)).1.val (arguments.val (.inr false)).2.val := by
  have complete := ArrayFold.prefix_invariant
    (update rows columns (2 * width + 1) sizes (fun name => arguments.val (.inl name)))
    (arguments.val (.inr true)) (arguments.val (.inr false))
    (invariant rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false))) (by rfl)
    (fun index state before => preserves rows columns width length sizes (fun name => arguments.val (.inl name))
      (arguments.val (.inr true)) (arguments.val (.inr false)) state arguments.property index before)
  have takeAll : (List.ofFn (arguments.val (.inr true))).take (MvPolynomial.eval sizes length) =
      List.ofFn (arguments.val (.inr true)) := by simp
  simpa only [invariant, takeAll, remainderSweepController, arrayFold] using complete

end Polytime2.Computation.Realizable.Internal
