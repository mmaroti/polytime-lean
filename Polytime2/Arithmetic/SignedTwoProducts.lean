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

import Polytime2.Arithmetic.SignedMultiplication
import Polytime2.Arithmetic.SignedAddition
import Polytime2.Arithmetic.SignedBounds
import Polytime2.Arithmetic.SignedWidth

/-! # Two-term integer linear combinations

All four inputs have magnitude width `w`; the result `p*x + q*y` has derived
width `2*w+1`. Independent coefficient and value widths `c,v` instead give
width `c+v+1`, using derived widening and exact narrowing. All variants reuse
existing certified multiplication and addition.
-/

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

noncomputable def integerTwoProducts (width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 4) where
  inputDomains _ := binaryIntegers width
  outputDomain := binaryIntegers (2 * width + 1)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val 0).val * (arguments.val 1).val +
    (arguments.val 2).val * (arguments.val 3).val, by
      simpa only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat] using
        IntegerArithmetic.twoProducts_bound (MvPolynomial.eval sizes width) _ _ _ _
          (arguments.val 0).property (arguments.val 1).property
          (arguments.val 2).property (arguments.val 3).property⟩

theorem integerTwoProducts_realizable (width : MvPolynomial Parameter ℕ) :
    (integerTwoProducts width).Realizable := by
  let inputs := (integerTwoProducts width).inputDomains
  let product (choice : Bool) sizes (arguments : {arguments : (integerTwoProducts width).Arguments sizes // True}) :=
    (integerMultiply width).compute sizes
      ⟨(fun name => if choice then (if name then arguments.val 3 else arguments.val 2)
        else (if name then arguments.val 1 else arguments.val 0)), trivial⟩
  have ready (choice : Bool) :
      (Computation.mk inputs (binaryIntegers (2 * width)) (fun _ _ => True) (product choice)).Realizable := by
    have selected := (integerMultiply_realizable width).onArguments inputs (fun _ _ => True)
      (fun name => if choice then (if name then 3 else 2)
        else (if name then 1 else 0)) (by
        intro name
        cases choice <;> cases name
        · rfl
        · rfl
        · rfl
        · rfl) (by intros; trivial)
    exact selected.withSpecification (fun _ _ => True) (product choice)
      (by intros; trivial) (by intro sizes arguments valid; cases choice <;> rfl)
  have added := (integerAdd_realizable (2 * width)).onResults inputs (fun _ _ => True) product
    (by intros; trivial) ready
  exact added.withSpecification (fun _ _ => True) (integerTwoProducts width).compute
    (by intros; trivial) (by intros; rfl)

/-- Coefficients and values may have independent mathematical magnitude widths. -/
noncomputable def integerTwoProductsAtWidths (coefficientWidth valueWidth : MvPolynomial Parameter ℕ) :
    Computation Parameter (Fin 4) where
  inputDomains | 0 | 2 => binaryIntegers coefficientWidth | 1 | 3 => binaryIntegers valueWidth
  outputDomain := binaryIntegers (coefficientWidth + valueWidth + 1)
  precondition _ _ := True
  compute sizes arguments := ⟨(arguments.val 0).val * (arguments.val 1).val +
    (arguments.val 2).val * (arguments.val 3).val, by
      simpa only [map_add, map_one] using
        IntegerArithmetic.twoProducts_bound_of_widths (MvPolynomial.eval sizes coefficientWidth)
          (MvPolynomial.eval sizes valueWidth) _ _ _ _ (arguments.val 0).property
          (arguments.val 1).property (arguments.val 2).property (arguments.val 3).property⟩

theorem integerTwoProductsAtWidths_realizable (coefficientWidth valueWidth : MvPolynomial Parameter ℕ) :
    (integerTwoProductsAtWidths coefficientWidth valueWidth).Realizable := by
  let computation := integerTwoProductsAtWidths coefficientWidth valueWidth
  let inputs := computation.inputDomains
  let capacity := coefficientWidth + valueWidth
  have coefficientWiden := Realizable.Internal.integerWidenTo_realizable coefficientWidth valueWidth capacity rfl
  have valueWiden := Realizable.Internal.integerWidenTo_realizable valueWidth coefficientWidth capacity (by dsimp [capacity]; ring)
  let widened (name : Fin 4) sizes (arguments : {arguments : computation.Arguments sizes // True}) :
      (binaryIntegers capacity).Carrier sizes := match name with
    | 0 => (Realizable.Internal.integerWidenTo coefficientWidth valueWidth capacity rfl).compute sizes
        ⟨(fun _ => arguments.val 0), trivial⟩
    | 1 => (Realizable.Internal.integerWidenTo valueWidth coefficientWidth capacity (by dsimp [capacity]; ring)).compute sizes
        ⟨(fun _ => arguments.val 1), trivial⟩
    | 2 => (Realizable.Internal.integerWidenTo coefficientWidth valueWidth capacity rfl).compute sizes
        ⟨(fun _ => arguments.val 2), trivial⟩
    | 3 => (Realizable.Internal.integerWidenTo valueWidth coefficientWidth capacity (by dsimp [capacity]; ring)).compute sizes
        ⟨(fun _ => arguments.val 3), trivial⟩
  have ready (name : Fin 4) :
      (Computation.mk inputs (binaryIntegers capacity) (fun _ _ => True) (widened name)).Realizable := by
    fin_cases name
    · exact coefficientWiden.withArguments inputs (MultiTape.oneTape 0) (fun _ => rfl)
    · exact valueWiden.withArguments inputs (MultiTape.oneTape 1) (fun _ => rfl)
    · exact coefficientWiden.withArguments inputs (MultiTape.oneTape 2) (fun _ => rfl)
    · exact valueWiden.withArguments inputs (MultiTape.oneTape 3) (fun _ => rfl)
  have combined := (integerTwoProducts_realizable capacity).onResults inputs (fun _ _ => True) widened
    (by intros; trivial) ready
  have narrowed := combined.followedBy
    (Realizable.Internal.integerNarrowAtWidths_realizable (2 * capacity + 1)
      (coefficientWidth + valueWidth + 1) (by
        intro sizes
        dsimp [capacity]
        simp only [map_add, map_one, map_mul, MvPolynomial.eval_ofNat]
        omega)) rfl (by
          intro sizes arguments valid
          change ((arguments 0).val * (arguments 1).val + (arguments 2).val * (arguments 3).val).natAbs < _
          simpa only [map_add, map_one] using
            IntegerArithmetic.twoProducts_bound_of_widths (MvPolynomial.eval sizes coefficientWidth)
              (MvPolynomial.eval sizes valueWidth) _ _ _ _ (arguments 0).property
              (arguments 1).property (arguments 2).property (arguments 3).property)
  exact narrowed.withSpecification (fun _ _ => True) computation.compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
