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

import Polytime2.Matrices.NaturalDiagonalSearch
import Polytime2.Arrays.SearchCoordinates

/-! # Actual adjacent coordinates for a diagonal repair

For a bounded natural diagonal that fails the adjacent divisibility condition,
return the first failing coordinate and its genuine successor. Reuse the
certified optional search and the shared coordinate extraction rules. The
result agrees exactly with the pair selected by the mathematical cleanup loop.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private theorem diagonalRepairCoordinates_valid (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (naturalDiagonalSearch length width).Arguments sizes)
    (failure : ¬IntegerMatrix.diagonalDivisibilityChain (fun index => ((arguments ()) index).val)) :
    (arraySearchAdjacentPair length).precondition sizes
      (fun _ => (naturalDiagonalSearch length width).compute sizes ⟨arguments, trivial⟩) := by
  change ((naturalDiagonalSearch length width).compute sizes ⟨arguments, trivial⟩).isSome ∧ _
  cases found : (naturalDiagonalSearch length width).compute sizes ⟨arguments, trivial⟩ with
  | none =>
    exact False.elim (failure ((IntegerMatrix.diagonalViolation_none _).mp
      ((naturalDiagonalSearch_none length width sizes (arguments ())).mp found)))
  | some first =>
    refine ⟨rfl, ?_⟩
    intro index same
    have equal := Option.some.inj same
    subst index
    obtain ⟨second, adjacent, _failure⟩ := naturalDiagonalSearch_found length width sizes (arguments ()) first found
    rw [← adjacent]
    exact second.isLt

/-- Select actual repair coordinates whenever the diagonal is not a divisibility chain. -/
noncomputable def diagonalRepairCoordinates (length width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((naturalDiagonalSearch length width).withPrecondition
    (fun _ arguments => ¬IntegerMatrix.diagonalDivisibilityChain (fun index => ((arguments ()) index).val))
    (by intros; trivial)).followedBy (arraySearchAdjacentPair length) rfl
      (fun sizes arguments failure => diagonalRepairCoordinates_valid length width sizes arguments failure)

theorem diagonalRepairCoordinates_realizable (length width : MvPolynomial Parameter ℕ) :
    (diagonalRepairCoordinates length width).Realizable :=
  ((naturalDiagonalSearch_realizable length width).withPrecondition
    (fun _ arguments => ¬IntegerMatrix.diagonalDivisibilityChain (fun index => ((arguments ()) index).val))
    (by intros; trivial)).followedBy (arraySearchAdjacentPair_realizable length) rfl
      (fun sizes arguments failure => diagonalRepairCoordinates_valid length width sizes arguments failure)

/-- The realized coordinate selection implements the pure cleanup schedule. -/
theorem diagonalRepairCoordinates_spec (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalRepairCoordinates length width).Arguments sizes //
      (diagonalRepairCoordinates length width).precondition sizes arguments}) :
    some ((diagonalRepairCoordinates length width).compute sizes arguments) =
      IntegerMatrix.diagonalViolation (fun index => ((arguments.val ()) index).val) := by
  let searched := (naturalDiagonalSearch length width).compute sizes ⟨arguments.val, trivial⟩
  have valid := diagonalRepairCoordinates_valid length width sizes arguments.val arguments.property
  let pair := (arraySearchAdjacentPair length).compute sizes ⟨(fun _ => searched), valid⟩
  have values := arraySearchAdjacentPair_values length sizes ⟨(fun _ => searched), valid⟩
  change searched = some pair.1 ∧ pair.2.val = pair.1.val + 1 ∧ pair.1 ≠ pair.2 at values
  have next : pair.1.val + 1 < MvPolynomial.eval sizes length := by
    rw [← values.2.1]
    exact pair.2.isLt
  have schedule := naturalDiagonalSearch_pair length width sizes (arguments.val ())
  change searched.bind _ = _ at schedule
  rw [values.1] at schedule
  change (if next : pair.1.val + 1 < MvPolynomial.eval sizes length then
    some (pair.1, (⟨pair.1.val + 1, next⟩ : Fin (MvPolynomial.eval sizes length))) else none) =
      IntegerMatrix.diagonalViolation (fun index => ((arguments.val ()) index).val) at schedule
  rw [dite_eq_left next] at schedule
  have pairEqual : (pair.1, (⟨pair.1.val + 1, next⟩ : Fin (MvPolynomial.eval sizes length))) = pair := by
    apply Prod.ext rfl
    exact Fin.ext values.2.1.symm
  rw [pairEqual] at schedule
  exact schedule

/-- A known search result identifies the first returned repair coordinate. -/
theorem diagonalRepairCoordinates_first (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalRepairCoordinates length width).Arguments sizes //
      (diagonalRepairCoordinates length width).precondition sizes arguments})
    (index : Fin (MvPolynomial.eval sizes length))
    (found : (naturalDiagonalSearch length width).compute sizes ⟨arguments.val, trivial⟩ = some index) :
    ((diagonalRepairCoordinates length width).compute sizes arguments).1 = index :=
  Option.some.inj ((Option.some_get _).trans found)

/-- The selected coordinates are adjacent and their entries fail divisibility. -/
theorem diagonalRepairCoordinates_correct (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalRepairCoordinates length width).Arguments sizes //
      (diagonalRepairCoordinates length width).precondition sizes arguments}) :
    let pair := (diagonalRepairCoordinates length width).compute sizes arguments
    pair.2.val = pair.1.val + 1 ∧
      ¬((arguments.val ()) pair.1).val ∣ ((arguments.val ()) pair.2).val :=
  IntegerMatrix.diagonalViolation_some _ _ _ (diagonalRepairCoordinates_spec length width sizes arguments).symm

end Polytime2.Computation
