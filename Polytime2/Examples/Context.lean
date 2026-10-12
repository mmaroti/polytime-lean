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

import Polytime2.Complexity
import Polytime2.Context
import Polytime2.BinaryAddition

/-! # Arithmetic with arbitrary preserved caller tapes

An addition routine owns three tapes in a larger collection. Its caller may
retain arbitrary contents and head positions on every other tape.
-/

namespace Polytime2.Examples.Context

open MultiTape
open Binary (word value)
open BinaryAddition (frame)

example (wiring : Fin 3 ↪ Fin 4) :
    ComputesWithContext (Context := fun _ : Unit → ℕ => Tapes (fun _ : Fin 4 => Binary.Symbol))
      (MultiTape.wire wiring BinaryAddition.machine) (.inl false) (.inr 1)
      (fun _ caller operands tapes =>
        (∃ old, old.length = operands.1.length ∧
          (fun name => tapes (wiring name)) =
            frame [3] (word operands.1 ++ [0]) [3] (word operands.2 ++ [0]) [3] (old ++ [0, 0])) ∧
        ∀ name, name ∉ Set.range wiring → tapes name = caller name)
      (fun sizes caller output tapes =>
        (∃ left right bits, value bits = output ∧ bits.length ≤ sizes () + 1 ∧
          (fun name => tapes (wiring name)) =
            frame [3] (word left ++ [0]) [3] (word right ++ [0]) [3] (word bits ++ [0])) ∧
        ∀ name, name ∉ Set.range wiring → tapes name = caller name)
      (fun sizes (operands : List Bool × List Bool) =>
        operands.2.length = operands.1.length ∧ operands.1.length ≤ sizes ())
      (fun _ operands => value operands.1 + value operands.2) :=
  Computes.wireWithContext (Alphabet := fun _ : Fin 4 => Binary.Symbol) wiring BinaryAddition.contract

end Polytime2.Examples.Context
