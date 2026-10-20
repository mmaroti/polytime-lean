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

import Polytime2.Arrays.NamedTransform
import Polytime2.Computation.Conditional

/-! # Applying a certified operation to every pair of array elements -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- A rectangular product map supports independent runtime array lengths and
size-dependent element widths. False is the row array, true the column array. -/
noncomputable def arrayProductMap (source target : EncodedDomain.{0, 0} Parameter)
    (rows columns : Parameter)
    (operation : ∀ sizes, source.Carrier sizes → source.Carrier sizes → target.Carrier sizes) :
    Computation Parameter Bool where
  inputDomains choice := source.array (if choice then columns else rows)
  outputDomain := (target.array columns).array rows
  precondition _ _ := True
  compute sizes arguments := fun row column => operation sizes
    (arguments.val false row) (arguments.val true column)

theorem arrayProductMap_realizable (source target : EncodedDomain.{0, 0} Parameter)
    (rows columns : Parameter)
    (operation : ∀ sizes, source.Carrier sizes → source.Carrier sizes → target.Carrier sizes)
    (step : (Computation.mk (fun _ : Bool => source) target (fun _ _ => True)
      (fun sizes arguments => operation sizes (arguments.val false) (arguments.val true))).Realizable) :
    (arrayProductMap source target rows columns operation).Realizable := by
  let computation := arrayProductMap source target rows columns operation
  let innerContext : Unit → EncodedDomain.{0, 0} Parameter := fun _ => source
  let innerOperation sizes (context : ∀ name, (innerContext name).Carrier sizes) value :=
    operation sizes (context ()) value
  let innerStep := arrayTransformStep innerContext source target innerOperation
  have innerStepReady : innerStep.Realizable := step.onResults innerStep.inputDomains innerStep.precondition
    (fun choice _ arguments => if choice then arguments.val (.inr ()) else arguments.val (.inl ()))
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact Realizable.argument innerStep.inputDomains (.inl ()) innerStep.precondition
      · exact Realizable.argument innerStep.inputDomains (.inr ()) innerStep.precondition)
  have innerReady := arrayTransformAtParameter_realizable innerContext source target columns innerOperation innerStepReady
  let outerContext : Unit → EncodedDomain.{0, 0} Parameter := fun _ => source.array columns
  let outerOperation sizes (context : ∀ name, (outerContext name).Carrier sizes) value :=
    fun column => operation sizes value (context () column)
  let outerStep := arrayTransformStep outerContext source (target.array columns) outerOperation
  have outerStepReady : outerStep.Realizable := innerReady.onResults outerStep.inputDomains outerStep.precondition
    (fun name _ arguments => match name with
      | .inl _ => arguments.val (.inr ())
      | .inr _ => arguments.val (.inl ())) (by intros; trivial) (by
        intro name
        cases name with
        | inl singleton => cases singleton; exact Realizable.argument outerStep.inputDomains (.inr ()) outerStep.precondition
        | inr singleton => cases singleton; exact Realizable.argument outerStep.inputDomains (.inl ()) outerStep.precondition)
  have outerReady := arrayTransformAtParameter_realizable outerContext source (target.array columns) rows outerOperation outerStepReady
  exact outerReady.onResults computation.inputDomains computation.precondition
    (fun name _ arguments => match name with
      | .inl _ => arguments.val true
      | .inr _ => arguments.val false) (by intros; trivial) (by
        intro name
        cases name with
        | inl singleton => cases singleton; exact Realizable.argument computation.inputDomains true computation.precondition
        | inr singleton => cases singleton; exact Realizable.argument computation.inputDomains false computation.precondition)

end Polytime2.Computation
