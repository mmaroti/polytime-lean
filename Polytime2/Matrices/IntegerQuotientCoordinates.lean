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

import Polytime2.Matrices.IntegerMulVec
import Polytime2.Matrices.IntegerRowDiagonal
import Polytime2.Arrays.CyclicCoordinates
import Polytime2.Matrices.SmithCoordinates

/-! # Cyclic coordinates for a supplied diagonal presentation

Input a rectangular integer diagonal, a square integer left transformation,
and a target vector, each with its own magnitude width. Apply the left matrix
and return the actual cyclic/free coordinates given by the diagonal
magnitudes. The construction is total; its quotient interpretation uses a
Smith presentation. All temporary widths are derived internally.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.IntegerMatrix

/-- The zero-extended diagonal magnitudes are exactly the torsion/free Smith moduli. -/
theorem rowDiagonal_natAbs_eq_diagonalModulus {rows columns : ℕ}
    (diagonal : Matrix (Fin rows) (Fin columns) ℤ) (rank : ℕ)
    (smith : IsSmithDiagonal diagonal rank) (row : Fin rows) :
    (rowDiagonal diagonal row).natAbs = diagonalModulus diagonal rank smith.1 row := by
  by_cases active : row.val < rank
  · have within : row.val < columns := active.trans_le (smith.1.trans (Nat.min_le_right _ _))
    simp [rowDiagonal, diagonalModulus, active, within]
  · unfold diagonalModulus rowDiagonal
    simp only [active, ↓reduceDIte]
    split
    · rw [smith.2.2.1 row _ (by omega)]
      rfl
    · rfl

end Polytime2.IntegerMatrix

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def inputs (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :
    Fin 3 → EncodedDomain Parameter
  | 0 => integerMatrices rows columns diagonalWidth
  | 1 => integerMatrices rows rows basisWidth
  | 2 => (binaryIntegers valueWidth).arrayOfLength rows

private noncomputable def moduli (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :=
  ((integerMatrixRowDiagonal rows columns diagonalWidth).withArguments
    (inputs rows columns diagonalWidth basisWidth valueWidth) (MultiTape.oneTape 0) (by intros; rfl)).followedBy
    (mapArray (binaryIntegers diagonalWidth) (binaryNaturalsOfWidth diagonalWidth) rows
      (fun sizes value => (integerMagnitude diagonalWidth).compute sizes ⟨fun _ => value, trivial⟩)) rfl (by intros; trivial)

private theorem moduli_realizable (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :
    (moduli rows columns diagonalWidth basisWidth valueWidth).Realizable :=
  ((integerMatrixRowDiagonal_realizable rows columns diagonalWidth).withArguments
    (inputs rows columns diagonalWidth basisWidth valueWidth) (MultiTape.oneTape 0) (by intros; rfl)).followedBy
    (mapArray_realizable (binaryIntegers diagonalWidth) (binaryNaturalsOfWidth diagonalWidth) rows
      (fun sizes value => (integerMagnitude diagonalWidth).compute sizes ⟨fun _ => value, trivial⟩)
      (integerMagnitude_realizable diagonalWidth)) rfl (by intros; trivial)

private noncomputable def transported (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :=
  (integerMatrixMulVec rows rows basisWidth valueWidth).onResults
    (inputs rows columns diagonalWidth basisWidth valueWidth) (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => arguments.val 1 | true => arguments.val 2) (by intros; trivial)

private theorem transported_realizable (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :
    (transported rows columns diagonalWidth basisWidth valueWidth).Realizable := by
  apply (integerMatrixMulVec_realizable rows rows basisWidth valueWidth).onResults
    (inputs rows columns diagonalWidth basisWidth valueWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact Realizable.argument _ (1 : Fin 3) _
  · exact Realizable.argument _ (2 : Fin 3) _

/-- Apply a supplied left matrix and reduce to the actual diagonal cyclic/free coordinates. -/
private noncomputable def implementation
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  (integerCyclicCoordinates rows diagonalWidth (rows + basisWidth + valueWidth)).onResults
    (inputs rows columns diagonalWidth basisWidth valueWidth) (fun _ _ => True)
    (fun choice sizes arguments => match choice with
      | false => (moduli rows columns diagonalWidth basisWidth valueWidth).compute sizes arguments
      | true => (transported rows columns diagonalWidth basisWidth valueWidth).compute sizes arguments) (by intros; trivial)

/-- Matrix-vector multiplication, diagonal reads, and coordinate normalization compose. -/
private theorem implementation_realizable
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :
    (implementation rows columns diagonalWidth basisWidth valueWidth).Realizable := by
  apply (integerCyclicCoordinates_realizable rows diagonalWidth (rows + basisWidth + valueWidth)).onResults
    (inputs rows columns diagonalWidth basisWidth valueWidth) (fun _ _ => True) _ (by intros; trivial)
  intro choice
  cases choice
  · exact moduli_realizable rows columns diagonalWidth basisWidth valueWidth
  · exact transported_realizable rows columns diagonalWidth basisWidth valueWidth

/-- Every reported modulus is exactly the supplied diagonal magnitude. -/
private theorem implementation_modulus
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (implementation rows columns diagonalWidth basisWidth valueWidth).Arguments sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) :
    ((implementation rows columns diagonalWidth basisWidth valueWidth).compute sizes
      ⟨arguments, trivial⟩ row).1.val = (IntegerMatrix.rowDiagonal (arguments 0).val row).natAbs := by
  exact congrArg Fin.val (integerCyclicCoordinates_modulus rows diagonalWidth
    (rows + basisWidth + valueWidth) sizes
    (fun choice => match choice with
      | false => (moduli rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩
      | true => (transported rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩) row)

/-- Every actual coordinate is the image of the transformed target entry. -/
private theorem implementation_value
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (implementation rows columns diagonalWidth basisWidth valueWidth).Arguments sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) :
    let result := (implementation rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩ row
    result.2.val = ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod result.1.val) :=
  integerCyclicCoordinates_correct rows diagonalWidth (rows + basisWidth + valueWidth) sizes
    (fun choice => match choice with
      | false => (moduli rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩
      | true => (transported rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩) row

private theorem implementation_observe
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (implementation rows columns diagonalWidth basisWidth valueWidth).Arguments sizes) :
    (fun row =>
      let result := (implementation rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩ row
      (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus)) =
      (fun row =>
        let modulus := (IntegerMatrix.rowDiagonal (arguments 0).val row).natAbs
        ⟨modulus, ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod modulus)⟩) := by
  funext row
  exact (congrArg (Sigma.mk _) (implementation_value rows columns diagonalWidth basisWidth valueWidth sizes arguments row)).trans
    (congrArg (fun modulus : ℕ => (⟨modulus,
      ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod modulus)⟩ : (modulus : ℕ) × ZMod modulus))
      (implementation_modulus rows columns diagonalWidth basisWidth valueWidth sizes arguments row))

/-- The actual cyclic/free coordinate map for the supplied diagonal and left
matrix. The mathematical observation forgets all storage bounds. -/
noncomputable def integerMatrixCyclicCoordinates
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  specificationBy (inputs rows columns diagonalWidth basisWidth valueWidth)
    ((boundedCyclic diagonalWidth (diagonalWidth + (rows + basisWidth + valueWidth))).arrayOfLength rows)
    (fun _ _ => True)
    (fun _ result row => (⟨(result row).1.val, (result row).2.val⟩ : (modulus : ℕ) × ZMod modulus))
    (fun _ arguments row =>
      let modulus := (IntegerMatrix.rowDiagonal (arguments.val 0).val row).natAbs
      ⟨modulus, ((arguments.val 1).val.mulVec (fun row => (arguments.val 2 row).val) row : ZMod modulus)⟩)
    (fun sizes arguments => ⟨(implementation rows columns diagonalWidth basisWidth valueWidth).compute sizes arguments,
      implementation_observe rows columns diagonalWidth basisWidth valueWidth sizes arguments.val⟩)

theorem integerMatrixCyclicCoordinates_realizable
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Realizable := by
  apply (implementation_realizable rows columns diagonalWidth basisWidth valueWidth).specificationBy
  · intro sizes
    exact Function.Injective.piMap (fun _ => Fin.val_injective.sigma_map (fun _ => Subtype.val_injective))
  · intro sizes arguments valid
    exact implementation_observe rows columns diagonalWidth basisWidth valueWidth sizes arguments

/-- All moduli and group elements agree with the ordinary mathematical map. -/
theorem integerMatrixCyclicCoordinates_observe
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Arguments sizes) :
    (fun row =>
      let result := (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩ row
      (⟨result.1.val, result.2.val⟩ : (modulus : ℕ) × ZMod modulus)) =
      (fun row =>
        let modulus := (IntegerMatrix.rowDiagonal (arguments 0).val row).natAbs
        ⟨modulus, ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod modulus)⟩) := by
  exact specificationBy_correct _ (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).outputDomain _
    (fun _ result row => (⟨(result row).1.val, (result row).2.val⟩ : (modulus : ℕ) × ZMod modulus)) _ _ sizes ⟨arguments, trivial⟩

/-- Every reported modulus is exactly the supplied diagonal magnitude. -/
theorem integerMatrixCyclicCoordinates_modulus
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Arguments sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) :
    ((integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).compute sizes
      ⟨arguments, trivial⟩ row).1.val = (IntegerMatrix.rowDiagonal (arguments 0).val row).natAbs :=
  congrArg Sigma.fst (congrFun
    (integerMatrixCyclicCoordinates_observe rows columns diagonalWidth basisWidth valueWidth sizes arguments) row)

/-- Every actual coordinate is the image of the transformed target entry. -/
theorem integerMatrixCyclicCoordinates_value
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Arguments sizes)
    (row : Fin (MvPolynomial.eval sizes rows)) :
    let result := (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩ row
    result.2.val = ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod result.1.val) := by
  have observed := congrFun
    (integerMatrixCyclicCoordinates_observe rows columns diagonalWidth basisWidth valueWidth sizes arguments) row
  exact (congrArg (fun pair : (modulus : ℕ) × ZMod modulus => pair.2 =
    ((arguments 1).val.mulVec (fun row => (arguments 2 row).val) row : ZMod pair.1)) observed).mpr rfl

/-- Vanishing is precisely divisibility by the zero-extended diagonal. -/
theorem integerMatrixCyclicCoordinates_zero_iff
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Arguments sizes) :
    (∀ row, ((integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).compute sizes
      ⟨arguments, trivial⟩ row).2.val = 0) ↔
      ∀ row, IntegerMatrix.rowDiagonal (arguments 0).val row ∣
        (arguments 1).val.mulVec (fun row => (arguments 2 row).val) row := by
  apply forall_congr'
  intro row
  rw [integerMatrixCyclicCoordinates_value]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, integerMatrixCyclicCoordinates_modulus]
  simp only [Int.natCast_dvd, Int.natAbs_dvd_natAbs]


/-- A supplied Smith diagonal gives exactly the mathematical torsion/free coordinate map. -/
theorem integerMatrixCyclicCoordinates_correct
    (rows columns diagonalWidth basisWidth valueWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).Arguments sizes)
    (rank : ℕ) (smith : IntegerMatrix.IsSmithDiagonal (arguments 0).val rank) :
    let result := (integerMatrixCyclicCoordinates rows columns diagonalWidth basisWidth valueWidth).compute sizes ⟨arguments, trivial⟩
    ∀ row, ∃ modulusEq : (result row).1.val = IntegerMatrix.diagonalModulus (arguments 0).val rank smith.1 row,
      ZMod.ringEquivCongr modulusEq (result row).2.val =
        IntegerMatrix.diagonalCoordinates (arguments 0).val rank smith.1
          ((arguments 1).val.mulVec (fun row => (arguments 2 row).val)) row := by
  dsimp only
  intro row
  have first := integerMatrixCyclicCoordinates_modulus rows columns diagonalWidth basisWidth valueWidth sizes arguments row
  have second := IntegerMatrix.rowDiagonal_natAbs_eq_diagonalModulus (arguments 0).val rank smith row
  refine ⟨first.trans second, ?_⟩
  rw [← ZMod.ringEquivCongr_ringEquivCongr_apply first second,
    integerMatrixCyclicCoordinates_value]
  rw [ZMod.ringEquivCongr_intCast first]
  exact ZMod.ringEquivCongr_intCast second _

end Polytime2.Computation
