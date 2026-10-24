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

import Polytime2.Matrices.IntegerLeadingBlock
import Polytime2.Matrices.IntegerRectangularHermite
import Polytime2.Matrices.RectangularDiagonalCleanup

/-! # Divisibility cleanup of a full positive rectangular diagonal

Read the active diagonal of the supplied full matrix and invoke the existing
certified rectangular cleanup. The mathematical input is exactly a positive
active diagonal, with rank bounded by both dimensions. Both actual cleanup
bases and the full Smith diagonal are returned.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private def allowed (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : Unit → (integerMatrices rows columns width).Carrier sizes) : Prop :=
  ∃ _within : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows ∧
      MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns,
    ∃ diagonal : Fin (MvPolynomial.eval sizes rank) → ℕ, (∀ index, 0 < diagonal index) ∧
      (arguments ()).val = IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal

private noncomputable def read (rows columns rank width : MvPolynomial Parameter ℕ) :=
  ((integerMatrixLeadingBlock rows columns rank width).withPrecondition (allowed rows columns rank width)
    (fun _ _ valid => valid.choose)).followedBy (integerMatrixDiagonalMagnitudes rank width) rfl (by intros; trivial)

private theorem read_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (read rows columns rank width).Realizable :=
  ((integerMatrixLeadingBlock_realizable rows columns rank width).withPrecondition (allowed rows columns rank width)
    (fun _ _ valid => valid.choose)).followedBy (integerMatrixDiagonalMagnitudes_realizable rank width) rfl (by intros; trivial)

private theorem read_matches (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (read rows columns rank width).Arguments sizes //
      (read rows columns rank width).precondition sizes arguments})
    (diagonal : Fin (MvPolynomial.eval sizes rank) → ℕ)
    (equation : (arguments.val ()).val =
      IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal) :
    (fun index => ((read rows columns rank width).compute sizes arguments index).val) = diagonal := by
  funext index
  change ((arguments.val ()).val (Fin.castLE arguments.property.choose.1 index)
    (Fin.castLE arguments.property.choose.2 index)).natAbs = diagonal index
  have same := congrArg (fun matrix => (matrix (Fin.castLE arguments.property.choose.1 index)
    (Fin.castLE arguments.property.choose.2 index)).natAbs) equation
  exact same.trans (by simp [IntegerMatrix.rectangularDiagonal, index.isLt])

private theorem permitted (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (read rows columns rank width).Arguments sizes)
    (valid : (read rows columns rank width).precondition sizes arguments) :
    (rectangularPositiveDiagonalCleanup rows columns rank width).precondition sizes
      (fun _ => (read rows columns rank width).compute sizes ⟨arguments, valid⟩) := by
  obtain ⟨within, diagonal, positive, equation⟩ := valid
  have same := read_matches rows columns rank width sizes ⟨arguments, ⟨within, diagonal, positive, equation⟩⟩ diagonal equation
  refine ⟨?_, within.1, within.2⟩
  intro index
  have entry := congrFun same index
  rw [entry]
  exact positive index

/-- Clean the active divisibility chain of a full positive rectangular diagonal. -/
noncomputable def integerRectangularCleanup (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (read rows columns rank width).followedBy (rectangularPositiveDiagonalCleanup rows columns rank width) rfl
    (permitted rows columns rank width)

/-- Active entry reads, bounded cleanup, rectangular construction, and full bases are certified. -/
theorem integerRectangularCleanup_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanup rows columns rank width).Realizable :=
  (read_realizable rows columns rank width).followedBy (rectangularPositiveDiagonalCleanup_realizable rows columns rank width)
    rfl (permitted rows columns rank width)

/-- Mathematical rank bounds and a positive active diagonal suffice for cleanup. -/
theorem integerRectangularCleanup_permitted (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerRectangularCleanup rows columns rank width).Arguments sizes)
    (rowBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows)
    (columnBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes columns)
    (diagonal : Fin (MvPolynomial.eval sizes rank) → ℕ) (positive : ∀ index, 0 < diagonal index)
    (equation : (arguments ()).val =
      IntegerMatrix.rectangularDiagonal (MvPolynomial.eval sizes rows) (MvPolynomial.eval sizes columns) diagonal) :
    (integerRectangularCleanup rows columns rank width).precondition sizes arguments :=
  ⟨⟨rowBound, columnBound⟩, diagonal, positive, equation⟩

/-- The cleanup result satisfies the full Smith contract for the supplied matrix. -/
theorem integerRectangularCleanup_isSmithForm (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanup rows columns rank width).Arguments sizes //
      (integerRectangularCleanup rows columns rank width).precondition sizes arguments}) :
    let result := (integerRectangularCleanup rows columns rank width).compute sizes arguments
    IntegerMatrix.IsSmithForm (arguments.val ()).val result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval sizes rank) := by
  have valid := permitted rows columns rank width sizes arguments.val arguments.property
  have form := rectangularPositiveDiagonalCleanup_isSmithForm rows columns rank width sizes
    ⟨fun _ => (read rows columns rank width).compute sizes arguments, valid⟩
  obtain ⟨within, diagonal, positive, equation⟩ := arguments.property
  have entries := read_matches rows columns rank width sizes arguments diagonal equation
  rw [entries, ← equation] at form
  exact form

/-- One full cleanup capacity depending on host rows and entry width, not active rank. -/
noncomputable def rectangularCleanupOutputWidth (rows width : MvPolynomial Parameter ℕ) :=
  positiveDiagonalProductWidth rows width + positiveDiagonalBasisWidth rows width + 3

private theorem outputFits (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanup rows columns rank width).Arguments sizes //
      (integerRectangularCleanup rows columns rank width).precondition sizes arguments}) :
    let result := (integerRectangularCleanup rows columns rank width).compute sizes arguments
    let bound := 2 ^ MvPolynomial.eval sizes (rectangularCleanupOutputWidth rows width)
    (∀ row column, (result.1.val row column).natAbs < bound) ∧
    (∀ row column, (result.2.1.val row column).natAbs < bound) ∧
    (∀ row column, (result.2.2.val row column).natAbs < bound) := by
  have rankBound : MvPolynomial.eval sizes rank ≤ MvPolynomial.eval sizes rows := arguments.property.choose.1
  have productLe : MvPolynomial.eval sizes (positiveDiagonalProductWidth rank width) ≤
      MvPolynomial.eval sizes (positiveDiagonalProductWidth rows width) := by
    simp only [positiveDiagonalProductWidth, map_add, map_mul]
    gcongr
  have basisLe : MvPolynomial.eval sizes (positiveDiagonalBasisWidth rank width) ≤
      MvPolynomial.eval sizes (positiveDiagonalBasisWidth rows width) := by
    simp [positiveDiagonalBasisWidth, positiveDiagonalBudget, positiveDiagonalProductWidth, diagonalCleanupWorkspace]
    gcongr
  have matrixCapacity : MvPolynomial.eval sizes ((positiveDiagonalProductWidth rank width + 1) + 1) ≤
      MvPolynomial.eval sizes (rectangularCleanupOutputWidth rows width) := by
    simp only [rectangularCleanupOutputWidth, map_add, map_one, MvPolynomial.eval_ofNat]
    omega
  have basisCapacity : MvPolynomial.eval sizes (positiveDiagonalBasisWidth rank width + 1) ≤
      MvPolynomial.eval sizes (rectangularCleanupOutputWidth rows width) := by
    simp only [rectangularCleanupOutputWidth, map_add, map_one, MvPolynomial.eval_ofNat]
    omega
  let result := (integerRectangularCleanup rows columns rank width).compute sizes arguments
  exact ⟨fun row column => (result.1.property row column).trans_le (pow_le_pow_right₀ (by decide) matrixCapacity),
    fun row column => (result.2.1.property row column).trans_le (pow_le_pow_right₀ (by decide) basisCapacity),
    fun row column => (result.2.2.property row column).trans_le (pow_le_pow_right₀ (by decide) basisCapacity)⟩

/-- Full diagonal cleanup at one host-derived output width, independent of active rank. -/
noncomputable def integerRectangularCleanupAtRank (rows columns rank width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := (integerRectangularCleanup rows columns rank width).inputDomains
  outputDomain := (integerMatrices rows columns (rectangularCleanupOutputWidth rows width)).prod
    ((integerMatrices rows rows (rectangularCleanupOutputWidth rows width)).prod
      (integerMatrices columns columns (rectangularCleanupOutputWidth rows width)))
  precondition := (integerRectangularCleanup rows columns rank width).precondition
  compute sizes arguments :=
    let result := (integerRectangularCleanup rows columns rank width).compute sizes arguments
    (⟨result.1.val, (outputFits rows columns rank width sizes arguments).1⟩,
      ⟨result.2.1.val, (outputFits rows columns rank width sizes arguments).2.1⟩,
      ⟨result.2.2.val, (outputFits rows columns rank width sizes arguments).2.2⟩)

/-- Cleanup and resizing all full matrices reuse existing certified operations. -/
theorem integerRectangularCleanupAtRank_realizable (rows columns rank width : MvPolynomial Parameter ℕ) :
    (integerRectangularCleanupAtRank rows columns rank width).Realizable := by
  let computation := integerRectangularCleanupAtRank rows columns rank width
  let matrixWidth := (positiveDiagonalProductWidth rank width + 1) + 1
  let basisWidth := positiveDiagonalBasisWidth rank width + 1
  let target := rectangularCleanupOutputWidth rows width
  have actual := integerRectangularCleanup_realizable rows columns rank width
  have bases := actual.snd
  have matrixReady := actual.fst.followedBy (integerMatrixResize_realizable rows columns matrixWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).1)
  have leftReady := bases.fst.followedBy (integerMatrixResize_realizable rows rows basisWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).2.1)
  have rightReady := bases.snd.followedBy (integerMatrixResize_realizable columns columns basisWidth target) rfl (by
    intro sizes arguments valid
    exact (outputFits rows columns rank width sizes ⟨arguments, valid⟩).2.2)
  exact matrixReady.prodMk (leftReady.prodMk rightReady)

/-- Returning the host-derived width preserves the full Smith contract. -/
theorem integerRectangularCleanupAtRank_isSmithForm (rows columns rank width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerRectangularCleanupAtRank rows columns rank width).Arguments sizes //
      (integerRectangularCleanupAtRank rows columns rank width).precondition sizes arguments}) :
    let result := (integerRectangularCleanupAtRank rows columns rank width).compute sizes arguments
    IntegerMatrix.IsSmithForm (arguments.val ()).val result.1.val result.2.1.val result.2.2.val (MvPolynomial.eval sizes rank) := by
  have form := integerRectangularCleanup_isSmithForm rows columns rank width sizes arguments
  exact form

end Polytime2.Computation
