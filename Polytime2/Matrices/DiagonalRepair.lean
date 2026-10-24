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

import Polytime2.Matrices.DiagonalSelectedRepair
import Polytime2.Matrices.DiagonalStorePair

/-! # One complete fixed-workspace diagonal repair

Given a positive diagonal whose total product has a polynomial bit bound,
select a failing adjacent pair, update both accumulated bases, and store the
new natural diagonal entries. The product bound proves that the lcm fits the
diagonal workspace; the prefix bound proves that both bases fit their workspace.
These bounds are logical invariants, not runtime tests.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def repairInputs (length productWidth basisWidth : MvPolynomial Parameter ℕ) :=
  (diagonalSelectedRepair length (productWidth + 1) basisWidth).inputDomains

private def repairAllowed (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (repairInputs length productWidth basisWidth name).Carrier sizes) :=
  (diagonalSelectedRepair length (productWidth + 1) basisWidth).precondition sizes arguments ∧
    (∀ index, 0 < (arguments 0 index).val) ∧
    (∏ index, (arguments 0 index).val) ≤ 2 ^ MvPolynomial.eval sizes productWidth

private theorem repairLcmFits (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (repairInputs length productWidth basisWidth name).Carrier sizes //
      repairAllowed length productWidth basisWidth sizes arguments}) :
    ((diagonalSelectedRepair length (productWidth + 1) basisWidth).compute sizes
      ⟨arguments.val, arguments.property.1⟩).2.1.2.val.natAbs < 2 ^ MvPolynomial.eval sizes (productWidth + 1) := by
  let result := (diagonalSelectedRepair length (productWidth + 1) basisWidth).compute sizes
    ⟨arguments.val, arguments.property.1⟩
  let diagonal := fun index => (arguments.val 0 index).val
  have selected := diagonalSelectedRepair_coordinates length (productWidth + 1) basisWidth sizes
    ⟨arguments.val, arguments.property.1⟩
  have adjacent := (IntegerMatrix.diagonalViolation_some _ _ _ selected.symm).1
  have different : result.1.1 ≠ result.1.2 := by
    intro same
    have values := congrArg Fin.val same
    change result.1.2.val = result.1.1.val + 1 at adjacent
    omega
  have positive := IntegerMatrix.diagonalNormalizePair_positive diagonal arguments.property.2.1 result.1.1 result.1.2
  have productBound : (∏ index, IntegerMatrix.diagonalNormalizePair diagonal result.1.1 result.1.2 index) ≤
      2 ^ MvPolynomial.eval sizes productWidth := by
    rw [IntegerMatrix.diagonalNormalizePair_product diagonal result.1.1 result.1.2 different]
    exact arguments.property.2.2
  have entryBound := IntegerMatrix.diagonalEntries_bound (MvPolynomial.eval sizes productWidth)
    (IntegerMatrix.diagonalNormalizePair diagonal result.1.1 result.1.2) positive productBound result.1.2
  have values := diagonalSelectedRepair_values length (productWidth + 1) basisWidth sizes
    ⟨arguments.val, arguments.property.1⟩
  change result.2.1.2.val.natAbs < _
  rw [values.2, Int.natAbs_natCast]
  simpa only [IntegerMatrix.diagonalNormalizePair, Function.update_self, map_add, map_one] using entryBound

private noncomputable def repairHost (length productWidth basisWidth : MvPolynomial Parameter ℕ) :=
  Sum.elim (repairInputs length productWidth basisWidth)
    (fun _ : Unit => (diagonalSelectedRepair length (productWidth + 1) basisWidth).outputDomain)

private def repairStoreAllowed (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ) (arguments : ∀ name, (repairHost length productWidth basisWidth name).Carrier sizes) :=
  (arguments (.inr ())).2.1.2.val.natAbs < 2 ^ MvPolynomial.eval sizes (productWidth + 1)

private noncomputable def repairStoreArguments (length productWidth basisWidth : MvPolynomial Parameter ℕ)
    (name : Fin 5) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ name, (repairHost length productWidth basisWidth name).Carrier sizes //
      repairStoreAllowed length productWidth basisWidth sizes arguments}) :
    ((diagonalStorePair length (productWidth + 1)).inputDomains name).Carrier sizes :=
  match name with
  | 0 => (arguments.val (.inr ())).1.1
  | 1 => (arguments.val (.inr ())).1.2
  | 2 => arguments.val (.inl 0)
  | 3 => (arguments.val (.inr ())).2.1.1
  | 4 => (arguments.val (.inr ())).2.1.2

private noncomputable def repairStore (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3 ⊕ Unit) where
  inputDomains := repairHost length productWidth basisWidth
  outputDomain := ((binaryNaturalsOfWidth (productWidth + 1)).arrayOfLength length).prod
    ((integerMatrices length length basisWidth).prod (integerMatrices length length basisWidth))
  precondition := repairStoreAllowed length productWidth basisWidth
  compute sizes arguments := ((diagonalStorePair length (productWidth + 1)).compute sizes
    ⟨(fun name => repairStoreArguments length productWidth basisWidth name sizes arguments), arguments.property⟩,
    (arguments.val (.inr ())).2.2)

private theorem repairStore_realizable (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (repairStore length productWidth basisWidth).Realizable := by
  let computation := repairStore length productWidth basisWidth
  let width := productWidth + 1
  let coordinates := (boundedIndex length).prod (boundedIndex length)
  let values := (integerGcdLcm width).outputDomain
  let bases := (integerMatrices length length basisWidth).prod (integerMatrices length length basisWidth)
  have result := Realizable.argument computation.inputDomains (.inr ()) computation.precondition
  have pair := result.followedBy (pairProjection_realizable coordinates (values.prod bases) false) rfl (by intros; trivial)
  have core := result.followedBy (pairProjection_realizable coordinates (values.prod bases) true) rfl (by intros; trivial)
  have scalars := core.followedBy (pairProjection_realizable values bases false) rfl (by intros; trivial)
  have basis := core.followedBy (pairProjection_realizable values bases true) rfl (by intros; trivial)
  have stored := (diagonalStorePair_realizable length width).onResults computation.inputDomains computation.precondition
    (repairStoreArguments length productWidth basisWidth) (fun _ arguments => arguments.property) (by
      intro name
      fin_cases name
      · exact pair.followedBy (pairProjection_realizable (boundedIndex length) (boundedIndex length) false) rfl (by intros; trivial)
      · exact pair.followedBy (pairProjection_realizable (boundedIndex length) (boundedIndex length) true) rfl (by intros; trivial)
      · exact Realizable.argument computation.inputDomains (.inl 0) computation.precondition
      · exact scalars.followedBy (pairProjection_realizable (binaryIntegers width) (binaryIntegers (2 * width)) false) rfl
          (by intros; trivial)
      · exact scalars.followedBy (pairProjection_realizable (binaryIntegers width) (binaryIntegers (2 * width)) true) rfl
          (by intros; trivial))
  have complete := Realizable.pairOutputs computation.inputDomains
    ((binaryNaturalsOfWidth width).arrayOfLength length) bases computation.precondition _ _ stored basis
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

private noncomputable def repairPrepared (length productWidth basisWidth : MvPolynomial Parameter ℕ) :=
  (diagonalSelectedRepair length (productWidth + 1) basisWidth).withPrecondition
    (repairAllowed length productWidth basisWidth) (fun _ _ valid => valid.1)

/-- Perform one effective repair of the diagonal and both fixed-width bases. -/
noncomputable def diagonalRepair (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 3) :=
  (repairPrepared length productWidth basisWidth).letThen (repairStore length productWidth basisWidth)
    (fun _ => rfl) rfl (fun sizes arguments valid => repairLcmFits length productWidth basisWidth sizes ⟨arguments, valid⟩)

theorem diagonalRepair_realizable (length productWidth basisWidth : MvPolynomial Parameter ℕ) :
    (diagonalRepair length productWidth basisWidth).Realizable := by
  have prepared := (diagonalSelectedRepair_realizable length (productWidth + 1) basisWidth).withPrecondition
    (repairAllowed length productWidth basisWidth) (fun _ _ valid => valid.1)
  exact prepared.letThen (repairStore_realizable length productWidth basisWidth) (fun _ => rfl) rfl
    (fun sizes arguments valid => repairLcmFits length productWidth basisWidth sizes ⟨arguments, valid⟩)

/-- The stored natural array is exactly the mathematical pair normalization. -/
theorem diagonalRepair_diagonal (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalRepair length productWidth basisWidth).Arguments sizes //
      (diagonalRepair length productWidth basisWidth).precondition sizes arguments}) :
    let selected := (diagonalSelectedRepair length (productWidth + 1) basisWidth).compute sizes
      ⟨arguments.val, arguments.property.1⟩
    (fun index => (((diagonalRepair length productWidth basisWidth).compute sizes arguments).1 index).val) =
      IntegerMatrix.diagonalNormalizePair (fun index => (arguments.val 0 index).val) selected.1.1 selected.1.2 := by
  let selected := (diagonalSelectedRepair length (productWidth + 1) basisWidth).compute sizes
    ⟨arguments.val, arguments.property.1⟩
  let storedArguments : (diagonalStorePair length (productWidth + 1)).Arguments sizes
    | 0 => selected.1.1
    | 1 => selected.1.2
    | 2 => arguments.val 0
    | 3 => selected.2.1.1
    | 4 => selected.2.1.2
  have stored := diagonalStorePair_values length (productWidth + 1) sizes
    ⟨storedArguments, repairLcmFits length productWidth basisWidth sizes arguments⟩
  have values := diagonalSelectedRepair_values length (productWidth + 1) basisWidth sizes
    ⟨arguments.val, arguments.property.1⟩
  change selected.2.1.1.val = _ ∧ selected.2.1.2.val = _ at values
  change (fun index => (((diagonalRepair length productWidth basisWidth).compute sizes arguments).1 index).val) =
    Function.update (Function.update (fun index => (arguments.val 0 index).val)
      selected.1.1 selected.2.1.1.val.natAbs) selected.1.2 selected.2.1.2.val.natAbs at stored
  rw [values.1, values.2, Int.natAbs_natCast, Int.natAbs_natCast] at stored
  exact stored

/-- The complete realized state update agrees with one step of the pure cleanup loop. -/
theorem diagonalRepair_correct (length productWidth basisWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalRepair length productWidth basisWidth).Arguments sizes //
      (diagonalRepair length productWidth basisWidth).precondition sizes arguments}) :
    let result := (diagonalRepair length productWidth basisWidth).compute sizes arguments
    ((fun index => (result.1 index).val), (result.2.1.val, result.2.2.val)) =
      IntegerMatrix.diagonalCleanupWithBases 1 (fun index => (arguments.val 0 index).val)
        (arguments.val 1).val (arguments.val 2).val := by
  have selected := diagonalSelectedRepair_coordinates length (productWidth + 1) basisWidth sizes
    ⟨arguments.val, arguments.property.1⟩
  have diagonal := diagonalRepair_diagonal length productWidth basisWidth sizes arguments
  have bases := diagonalSelectedRepair_bases length (productWidth + 1) basisWidth sizes
    ⟨arguments.val, arguments.property.1⟩
  rw [IntegerMatrix.diagonalCleanupWithBases, ← selected]
  exact Prod.ext diagonal bases

end Polytime2.Computation.Realizable.Internal
