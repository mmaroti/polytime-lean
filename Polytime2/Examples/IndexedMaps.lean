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

import Polytime2.Arrays.IndexedMap

/-! # Indexed finite maps and sequential catalogue operations -/

namespace Polytime2.Examples.IndexedMaps

open Polytime2.Computation

noncomputable section IndexedExamples

private def boolean : EncodedDomain Empty := EncodedDomain.booleans
private def length : MvPolynomial Unit ℕ := 3
private def sizes : Unit → ℕ := fun _ => 3
private def toggle := indexedMap boolean boolean length
  (fun parameter value => Bool.xor parameter value)
private def toggleArguments : toggle.Arguments sizes
  | 0 => ⟨1, by norm_num [length]⟩
  | 1 => fun _ => false
  | 2 => true
private theorem toggleAdmissible : toggle.precondition sizes toggleArguments := by
  trivial

example : toggle.Realizable := indexedMap_realizable _ _ _ _
example : toggle.compute sizes ⟨toggleArguments, toggleAdmissible⟩
    ⟨1, by norm_num [length]⟩ = true := rfl
example : toggle.compute sizes ⟨toggleArguments, toggleAdmissible⟩
    ⟨0, by norm_num [length]⟩ = false := rfl

private def twice := catalogueMaps boolean length (fun value => !value) (fun value => !value)
private def catalogueArguments : twice.Arguments sizes
  | 0 | 1 => ⟨1, by norm_num [length]⟩
  | 2 => ⟨2, by norm_num [length]⟩
  | 3 => fun _ => false
private theorem catalogueAdmissible : twice.precondition sizes catalogueArguments := by
  change 1 < 2 ∧ 1 < 2
  norm_num [length]

example : twice.Realizable := catalogueMaps_realizable _ _ _ _

-- Coincident coordinates apply both toggles sequentially.
example : twice.compute sizes ⟨catalogueArguments, catalogueAdmissible⟩
    ⟨1, by norm_num [length]⟩ = false := rfl

-- Coordinate two lies outside the active prefix and remains unchanged.
example : twice.compute sizes ⟨catalogueArguments, catalogueAdmissible⟩
    ⟨2, by norm_num [length]⟩ = false := rfl

-- Singleton scalar parameters and array elements occupy zero bits.
example : (indexedMap (EncodedDomain.fixed (Equiv.refl (Fin 1)))
    (EncodedDomain.fixed (Equiv.refl (Fin 1))) length
    (fun _ value => value)).Realizable := indexedMap_realizable _ _ _ _

end IndexedExamples
end Polytime2.Examples.IndexedMaps
