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

import Polytime2.Arrays.Operations
import Polytime2.Arithmetic.SignedWidth

/-! # Storing two repaired entries in the natural diagonal

Given two coordinates, the original bounded natural array, and two signed
replacement words, store their natural magnitudes. The second word may use
twice the diagonal width; its magnitude must fit the diagonal width before
narrowing. Two existing array updates perform the replacement, with the second
write taking precedence if the coordinates coincide.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation.Realizable.Internal

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Replace two natural entries with magnitudes of the supplied signed words. -/
noncomputable def diagonalStorePair (length width : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 5) where
  inputDomains name := match name with
    | 0 | 1 => boundedIndex length
    | 2 => (binaryNaturalsOfWidth width).arrayOfLength length
    | 3 => binaryIntegers width
    | 4 => binaryIntegers (2 * width)
  outputDomain := (binaryNaturalsOfWidth width).arrayOfLength length
  precondition sizes arguments := (arguments 4).val.natAbs < 2 ^ MvPolynomial.eval sizes width
  compute _ arguments := Function.update
    (Function.update (arguments.val 2) (arguments.val 0)
      ⟨(arguments.val 3).val.natAbs, (arguments.val 3).property⟩)
    (arguments.val 1) ⟨(arguments.val 4).val.natAbs, arguments.property⟩

theorem diagonalStorePair_realizable (length width : MvPolynomial Parameter ℕ) :
    (diagonalStorePair length width).Realizable := by
  let computation := diagonalStorePair length width
  have firstMagnitude := ((integerMagnitude_realizable width).withArguments computation.inputDomains
    (MultiTape.oneTape 3) (fun _ => rfl)).withPrecondition computation.precondition (by intros; trivial)
  have secondWord := ((integerNarrowAtWidths_realizable (2 * width) width
    (by intro sizes; simp only [map_mul, map_ofNat]; omega)).withArguments computation.inputDomains
      (MultiTape.oneTape 4) (fun _ => rfl)).withPrecondition computation.precondition (by
        intro sizes arguments valid
        exact valid)
  have secondMagnitude := secondWord.followedBy (integerMagnitude_realizable width) rfl (by intros; trivial)
  let firstResults (name : Fin 3) (sizes : Parameter → ℕ)
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((arrayUpdate (binaryNaturalsOfWidth width) length).inputDomains name).Carrier sizes :=
    match name with
    | 0 => arguments.val 0
    | 1 => arguments.val 2
    | 2 => ⟨(arguments.val 3).val.natAbs, (arguments.val 3).property⟩
  have firstUpdated := (arrayUpdate_realizable (binaryNaturalsOfWidth width) length).onResults
    computation.inputDomains computation.precondition firstResults (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact firstMagnitude)
  let secondResults (name : Fin 3) (sizes : Parameter → ℕ)
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :
      ((arrayUpdate (binaryNaturalsOfWidth width) length).inputDomains name).Carrier sizes :=
    match name with
    | 0 => arguments.val 1
    | 1 => Function.update (arguments.val 2) (arguments.val 0)
        ⟨(arguments.val 3).val.natAbs, (arguments.val 3).property⟩
    | 2 => ⟨(arguments.val 4).val.natAbs, arguments.property⟩
  have complete := (arrayUpdate_realizable (binaryNaturalsOfWidth width) length).onResults
    computation.inputDomains computation.precondition secondResults (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact firstUpdated
      · exact secondMagnitude)
  exact complete.withSpecification computation.precondition computation.compute
    (by intros; assumption) (by intros; rfl)

/-- Storing changes exactly the two selected mathematical entries. -/
theorem diagonalStorePair_values (length width : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (diagonalStorePair length width).Arguments sizes //
      (diagonalStorePair length width).precondition sizes arguments}) :
    (fun index => ((diagonalStorePair length width).compute sizes arguments index).val) =
      Function.update (Function.update (fun index => (arguments.val 2 index).val)
        (arguments.val 0) (arguments.val 3).val.natAbs) (arguments.val 1) (arguments.val 4).val.natAbs := by
  change (Fin.val ∘ Function.update (Function.update (arguments.val 2) (arguments.val 0) _)
    (arguments.val 1) _) = _
  rw [Function.comp_update, Function.comp_update]
  rfl

end Polytime2.Computation.Realizable.Internal
