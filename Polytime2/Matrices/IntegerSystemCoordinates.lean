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

import Polytime2.Matrices.IntegerSystemFeasible

/-! # Quotient coordinates from the complete Smith reduction

The returned cyclic/free coordinates agree with the cokernel isomorphism
obtained from the same deterministic Smith reduction.
-/

set_option backward.isDefEq.respectTransparency true

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- The executable result is the mathematical Smith quotient coordinate map. -/
theorem integerSystemQuotientCoordinates_correct
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (arguments : ∀ choice : Bool,
      (if choice then (binaryIntegers targetWidth).arrayOfLength rows
        else integerMatrices rows columns matrixWidth).Carrier sizes) :
    let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
      ⟨fun _ => arguments false, trivial⟩
    let form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
      ⟨fun _ => arguments false, trivial⟩
    let result := (integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩
    ∀ row, ∃ modulusEq : (result row).1.val =
        IntegerMatrix.diagonalModulus smith.2.1.val smith.1.val form.2.2.2.1 row,
      ZMod.ringEquivCongr modulusEq (result row).2.val =
        IntegerMatrix.diagonalCoordinates smith.2.1.val smith.1.val form.2.2.2.1
          (smith.2.2.1.val.mulVec (fun row => (arguments true row).val)) row := by
  let smith := (integerSmithReduction rows columns matrixWidth).compute sizes
    ⟨fun _ => arguments false, trivial⟩
  have form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
    ⟨fun _ => arguments false, trivial⟩
  dsimp only
  intro row
  have observed := congrFun
    (integerSystemQuotientCoordinates_observe rows columns matrixWidth targetWidth sizes arguments) row
  have first := congrArg Sigma.fst observed
  have second := IntegerMatrix.rowDiagonal_natAbs_eq_diagonalModulus smith.2.1.val smith.1.val form.2.2.2 row
  have value := (congrArg (fun pair : (modulus : ℕ) × ZMod modulus => pair.2 =
    (smith.2.2.1.val.mulVec (fun row => (arguments true row).val) row : ZMod pair.1)) observed).mpr rfl
  dsimp only at first value
  refine ⟨first.trans second, ?_⟩
  exact (congrArg (ZMod.ringEquivCongr (first.trans second)) value).trans
    (ZMod.ringEquivCongr_intCast (first.trans second) _)


/-- The computed coordinates vanish exactly for targets in the integer image. -/
theorem integerSystemQuotientCoordinates_zero_iff
    (rows columns matrixWidth targetWidth : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : ∀ choice : Bool,
      (if choice then (binaryIntegers targetWidth).arrayOfLength rows
        else integerMatrices rows columns matrixWidth).Carrier sizes) :
    (∀ row, ((integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
      ⟨arguments, trivial⟩ row).2.val = 0) ↔
      ∃ values, (arguments false).val.mulVec values = fun row => (arguments true row).val := by
  let result := (integerSmithReduction rows columns matrixWidth).compute sizes
    ⟨fun _ => arguments false, trivial⟩
  have form := integerSmithReduction_isSmithForm rows columns matrixWidth sizes
    ⟨fun _ => arguments false, trivial⟩
  have normalized :
      (∀ row, ((integerSystemQuotientCoordinates rows columns matrixWidth targetWidth).compute sizes
        ⟨arguments, trivial⟩ row).2.val = 0) ↔
        ∀ row, IntegerMatrix.rowDiagonal result.2.1.val row ∣
          result.2.2.1.val.mulVec (fun row => (arguments true row).val) row := by
    apply forall_congr'
    intro row
    have observed := congrFun
      (integerSystemQuotientCoordinates_observe rows columns matrixWidth targetWidth sizes arguments) row
    have modulus := congrArg Sigma.fst observed
    have value := (congrArg (fun pair : (modulus : ℕ) × ZMod modulus => pair.2 =
      (result.2.2.1.val.mulVec (fun row => (arguments true row).val) row : ZMod pair.1)) observed).mpr rfl
    dsimp only at value modulus
    rw [value, ZMod.intCast_zmod_eq_zero_iff_dvd, modulus]
    simp only [Int.natCast_dvd, Int.natAbs_dvd_natAbs]
    rfl
  have diagonal := IntegerMatrix.diagonalFeasible_iff_rowDiagonal result.2.1.val result.1.val form.2.2.2
    (result.2.2.1.val.mulVec (fun row => (arguments true row).val))
  have equivalent := IntegerMatrix.smithFeasible_iff (arguments false).val result.2.1.val
    result.2.2.1.val result.2.2.2.val result.1.val form (fun row => (arguments true row).val)
  have criterion := normalized.trans (diagonal.symm.trans equivalent.symm)
  exact criterion

end Polytime2.Computation
