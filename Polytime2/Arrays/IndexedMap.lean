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

import Polytime2.Computation.Conditional
import Polytime2.Computation.Constant
import Polytime2.Arrays.Operations
import Polytime2.Encoding.BoundedUnary
import Polytime2.Primitives.FiniteOperations
import Polytime2.Primitives.ConstantOperations

/-! # Indexed finite operations through mathematical certificates -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

noncomputable section IndexedComputations

/-- Arguments are the index, immutable array, and finite scalar parameter. -/
def indexedMap (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : parameterDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim →
      elementDomain.Carrier Empty.elim) : Computation Parameter (Fin 3) where
  inputDomains
    | 0 => EncodedDomain.boundedIndex length
    | 1 => elementDomain.constant.arrayOfLength length
    | 2 => parameterDomain.constant
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition _ _ := True
  compute _ arguments := Function.update (arguments.val 1)
    (arguments.val 0)
    (operation (arguments.val 2)
      (arguments.val 1 (arguments.val 0)))

/-- Two fixed maps act sequentially on selected coordinates in an active prefix.
Arguments are the first index, second index, active count, and immutable array.
Coincident indices apply the second map to the first map's result. -/
def catalogueMaps (elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (first second : elementDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim) :
    Computation Parameter (Fin 4) where
  inputDomains
    | 0 | 1 => EncodedDomain.boundedIndex length
    | 2 => EncodedDomain.boundedUnary length
    | 3 => elementDomain.constant.arrayOfLength length
  outputDomain := elementDomain.constant.arrayOfLength length
  precondition _ arguments :=
    (arguments 0).val < (arguments 2).val ∧ (arguments 1).val < (arguments 2).val
  compute _ arguments :=
    let firstIndex := arguments.val 0
    let secondIndex := arguments.val 1
    let middle := Function.update (arguments.val 3) firstIndex (first (arguments.val 3 firstIndex))
    Function.update middle secondIndex (second (middle secondIndex))

theorem indexedMap_realizable (parameterDomain elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (operation : parameterDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim →
      elementDomain.Carrier Empty.elim) :
    (indexedMap parameterDomain elementDomain length operation).Realizable := by
  let computation := indexedMap parameterDomain elementDomain length operation
  have lookup := (arrayLookup_realizable elementDomain.constant length).onArguments computation.inputDomains computation.precondition
    (fun choice => match choice with | false => 0 | true => 1) (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have mapped := ((finiteTable_realizable parameterDomain elementDomain elementDomain operation).withConstantSizes).onResults
    computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
      | false => arguments.val 2
      | true => arguments.val 1 (arguments.val 0))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument computation.inputDomains 2 computation.precondition
      · exact lookup)
  exact (arrayUpdate_realizable elementDomain.constant length).onResults
    computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 0
      | 1 => arguments.val 1
      | 2 => operation (arguments.val 2)
          (arguments.val 1 (arguments.val 0)))
    (by intros; trivial) (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact mapped)

theorem catalogueMaps_realizable (elementDomain : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ)
    (first second : elementDomain.Carrier Empty.elim → elementDomain.Carrier Empty.elim) :
    (catalogueMaps elementDomain length first second).Realizable := by
  let computation := catalogueMaps elementDomain length first second
  let singleton : EncodedDomain Empty := EncodedDomain.fixed (Equiv.refl (Fin 1))
  have unitReady := ((constant_realizable singleton (fun _ => (0 : Fin 1))).withConstantSizes).onResults
    computation.inputDomains computation.precondition (fun impossible => impossible.elim)
    (by intros; trivial) (fun impossible => impossible.elim)
  have firstReady := (indexedMap_realizable singleton elementDomain length
    (fun _ value => first value)).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with | 0 => arguments.val 0 | 1 => arguments.val 3 | 2 => (0 : Fin 1))
    (by intros; trivial)
    (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 0 computation.precondition
      · exact Realizable.argument computation.inputDomains 3 computation.precondition
      · exact unitReady)
  exact (indexedMap_realizable singleton elementDomain length
    (fun _ value => second value)).onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | 0 => arguments.val 1
      | 1 => Function.update (arguments.val 3)
          (arguments.val 0)
          (first (arguments.val 3 (arguments.val 0)))
      | 2 => (0 : Fin 1))
    (by intros; trivial)
    (by
      intro name
      fin_cases name
      · exact Realizable.argument computation.inputDomains 1 computation.precondition
      · exact firstReady
      · exact unitReady)

end IndexedComputations
end Polytime2.Computation
