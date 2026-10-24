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

import Polytime2.Matrices.IntegerIsDiagonal
import Polytime2.Matrices.HermiteRowsController
import Polytime2.Matrices.HermiteAlternatingBounds
import Polytime2.Matrices.IntegerResize

/-! # A certified conditional alternating Hermite pair

Run a row sweep and test its matrix for diagonality. A diagonal result keeps
its left basis and the identity right basis. Otherwise run the transpose-dual
sweep and retain both actual bases. Temporary widths are derived internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def firstWidth (dimension width : MvPolynomial Parameter ℕ) := hermiteRowsWorkspace width dimension
private noncomputable def secondWidth (dimension width : MvPolynomial Parameter ℕ) := hermiteRowsWorkspace (firstWidth dimension width) dimension
private noncomputable def capacity (dimension width : MvPolynomial Parameter ℕ) := 1 + firstWidth dimension width + secondWidth dimension width
private noncomputable def context (dimension width : MvPolynomial Parameter ℕ) : Unit → EncodedDomain Parameter :=
  fun _ => (integerHermiteRows dimension dimension width).outputDomain
private noncomputable def resultDomain (dimension width : MvPolynomial Parameter ℕ) :=
  (integerMatrices dimension dimension (capacity dimension width)).prod
    ((integerMatrices dimension dimension (firstWidth dimension width)).prod
      (integerMatrices dimension dimension (capacity dimension width)))

private noncomputable def firstMatrix (dimension width : MvPolynomial Parameter ℕ) :=
  (pairProjection ((integerMatrices dimension dimension (firstWidth dimension width)).prod
    (integerMatrices dimension dimension (firstWidth dimension width))) (hermitePivotSelection dimension dimension) false).followedBy
    (pairProjection (integerMatrices dimension dimension (firstWidth dimension width))
      (integerMatrices dimension dimension (firstWidth dimension width)) false) rfl (by intros; trivial)

private theorem firstMatrix_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (firstMatrix dimension width).Realizable :=
  (pairProjection_realizable _ (hermitePivotSelection dimension dimension) false).fst

private noncomputable def secondSweep (dimension width : MvPolynomial Parameter ℕ) :=
  ((firstMatrix dimension width).followedBy (integerMatrixTranspose dimension dimension (firstWidth dimension width))
    rfl (by intros; trivial)).followedBy
    (integerHermiteRows dimension dimension (firstWidth dimension width)) rfl (by intros; trivial)

private theorem secondSweep_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (secondSweep dimension width).Realizable :=
  ((firstMatrix_realizable dimension width).followedBy
    (integerMatrixTranspose_realizable dimension dimension (firstWidth dimension width)) rfl (by intros; trivial)).followedBy
    (integerHermiteRows_realizable dimension dimension (firstWidth dimension width)) rfl (by intros; trivial)

private noncomputable def stopped (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := context dimension width
  outputDomain := resultDomain dimension width
  precondition _ _ := True
  compute sizes arguments :=
    ((integerMatrixWiden dimension dimension (firstWidth dimension width) (1 + secondWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)).compute sizes
        ⟨fun _ => (arguments.val ()).1.1, trivial⟩,
    (arguments.val ()).1.2,
    (integerMatrixWiden dimension dimension 1 (firstWidth dimension width + secondWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)).compute sizes
        ⟨fun _ => (integerIdentity dimension).compute sizes ⟨(fun name => nomatch name), trivial⟩, trivial⟩)

private theorem stopped_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (stopped dimension width).Realizable := by
  have matrix := (firstMatrix_realizable dimension width).followedBy
    (integerMatrixWiden_realizable dimension dimension (firstWidth dimension width) (1 + secondWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)) rfl (by intros; trivial)
  let firstDomain := integerMatrices dimension dimension (firstWidth dimension width)
  have identity := (integerIdentity_realizable dimension).onResults (context dimension width) (fun _ _ => True)
    (fun name => nomatch name) (by intros; trivial) (fun name => nomatch name)
  have right := identity.followedBy (integerMatrixWiden_realizable dimension dimension 1
    (firstWidth dimension width + secondWidth dimension width) (capacity dimension width)
    (by dsimp [capacity]; ring)) rfl (by intros; trivial)
  exact matrix.prodMk (((pairProjection_realizable (firstDomain.prod firstDomain) (hermitePivotSelection dimension dimension) false).snd).prodMk right)

private noncomputable def continued (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := context dimension width
  outputDomain := resultDomain dimension width
  precondition _ _ := True
  compute sizes arguments :=
    let second := (secondSweep dimension width).compute sizes arguments
    ((integerMatrixWiden dimension dimension (secondWidth dimension width) (1 + firstWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)).compute sizes
        ⟨fun _ => ⟨second.1.1.val.transpose, fun row column => second.1.1.property column row⟩, trivial⟩,
    (arguments.val ()).1.2,
    (integerMatrixWiden dimension dimension (secondWidth dimension width) (1 + firstWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)).compute sizes
        ⟨fun _ => ⟨second.1.2.val.transpose, fun row column => second.1.2.property column row⟩, trivial⟩)

private theorem continued_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (continued dimension width).Realizable := by
  have pair := (secondSweep_realizable dimension width).fst
  have matrix := ((pair.fst).followedBy
    (integerMatrixTranspose_realizable dimension dimension (secondWidth dimension width)) rfl (by intros; trivial)).followedBy
    (integerMatrixWiden_realizable dimension dimension (secondWidth dimension width) (1 + firstWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)) rfl (by intros; trivial)
  let firstDomain := integerMatrices dimension dimension (firstWidth dimension width)
  have right := ((pair.snd).followedBy
    (integerMatrixTranspose_realizable dimension dimension (secondWidth dimension width)) rfl (by intros; trivial)).followedBy
    (integerMatrixWiden_realizable dimension dimension (secondWidth dimension width) (1 + firstWidth dimension width)
      (capacity dimension width) (by dsimp [capacity]; ring)) rfl (by intros; trivial)
  exact matrix.prodMk (((pairProjection_realizable (firstDomain.prod firstDomain) (hermitePivotSelection dimension dimension) false).snd).prodMk right)

private noncomputable def finish (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains := context dimension width
  outputDomain := resultDomain dimension width
  precondition _ _ := True
  compute sizes arguments := by
    classical
    exact if (integerMatrixIsDiagonal dimension (firstWidth dimension width)).compute sizes
      ⟨fun _ => (arguments.val ()).1.1, trivial⟩ = true then
    (stopped dimension width).compute sizes arguments else (continued dimension width).compute sizes arguments

private theorem finish_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (finish dimension width).Realizable := by
  have guard := (firstMatrix_realizable dimension width).followedBy
    (integerMatrixIsDiagonal_realizable dimension (firstWidth dimension width)) rfl (by intros; trivial)
  have ready := Realizable.conditional (context dimension width) (resultDomain dimension width) (fun _ _ => True)
    (fun sizes arguments => (integerMatrixIsDiagonal dimension (firstWidth dimension width)).compute sizes
      ⟨fun _ => (arguments.val ()).1.1, trivial⟩)
    (stopped dimension width).compute (continued dimension width).compute
    guard (stopped_realizable dimension width) (continued_realizable dimension width)
  apply ready.withSpecification (fun _ _ => True) (finish dimension width).compute (by intros; trivial)
  intro sizes arguments valid
  dsimp only [finish]
  split_ifs <;> rfl

/-- One conditional row/column pair, retaining both actual bases. -/
noncomputable def integerHermiteAlternatingStepRaw (dimension width : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (integerHermiteRows dimension dimension width).followedBy (finish dimension width) rfl (by intros; trivial)

/-- Both sweeps, the early stopping test, and full result construction are realized. -/
theorem integerHermiteAlternatingStepRaw_realizable (dimension width : MvPolynomial Parameter ℕ) :
    (integerHermiteAlternatingStepRaw dimension width).Realizable :=
  (integerHermiteRows_realizable dimension dimension width).followedBy (finish_realizable dimension width) rfl (by intros; trivial)

/-- The conditional runtime pair is exactly the mathematical alternating step. -/
theorem integerHermiteAlternatingStepRaw_correct (dimension width : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : {arguments : (integerHermiteAlternatingStepRaw dimension width).Arguments sizes //
      (integerHermiteAlternatingStepRaw dimension width).precondition sizes arguments}) :
    let result := (integerHermiteAlternatingStepRaw dimension width).compute sizes arguments
    (result.1.val, result.2.1.val, result.2.2.val) =
      IntegerMatrix.hermiteAlternatingStep (arguments.val ()).val := by
  classical
  let first := (integerHermiteRows dimension dimension width).compute sizes arguments
  have firstCorrect := integerHermiteRows_correct dimension dimension width sizes arguments
  have secondCorrect := integerHermiteRows_correct dimension dimension (firstWidth dimension width) sizes
    ⟨fun _ => ⟨first.1.1.val.transpose, fun row column => first.1.1.property column row⟩, trivial⟩
  dsimp only [IntegerMatrix.hermiteAlternatingStep]
  rw [← firstCorrect]
  dsimp only
  have guard := integerMatrixIsDiagonal_correct dimension (firstWidth dimension width) sizes first.1.1
  change (let result := if (integerMatrixIsDiagonal dimension (firstWidth dimension width)).compute sizes ⟨fun _ => first.1.1, trivial⟩ = true then
      (stopped dimension width).compute sizes ⟨fun _ => first, trivial⟩ else
      (continued dimension width).compute sizes ⟨fun _ => first, trivial⟩;
    (result.1.val, result.2.1.val, result.2.2.val)) =
    (if ∀ row column, row ≠ column → first.1.1.val row column = 0 then
      (first.1.1.val, first.1.2.val, 1) else
      ((IntegerMatrix.hermiteRowsSweep first.1.1.val.transpose).1.1.transpose,
        first.1.2.val, (IntegerMatrix.hermiteRowsSweep first.1.1.val.transpose).1.2.transpose))
  by_cases diagonal : ∀ row column, row ≠ column → first.1.1.val row column = 0
  · have accepted := guard.mpr diagonal
    rw [ite_eq_left accepted, ite_eq_left diagonal]
    rfl
  · have rejected : (integerMatrixIsDiagonal dimension (firstWidth dimension width)).compute sizes
        ⟨fun _ => first.1.1, trivial⟩ ≠ true := fun accepted => diagonal (guard.mp accepted)
    rw [ite_eq_right rejected, ite_eq_right diagonal]
    dsimp only at secondCorrect
    rw [← secondCorrect]
    rfl

end Polytime2.Computation
