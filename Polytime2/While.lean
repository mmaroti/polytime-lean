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

/-! # Guard-driven loop controllers

The guard leaves its result under the tape heads. A decreasing measure is
mathematical proof data only: the machine never reads a measure or a fuel bound.
The controller construction uses independent multi-tape execution semantics.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape names; symbolLevel: alphabets; guardLevel, bodyLevel: controllers.
universe tapeLevel symbolLevel guardLevel bodyLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {Guard : Type guardLevel} {Body : Type bodyLevel}

def whileMachine (guard : Machine Alphabet Guard) (body : Machine Alphabet Body)
    (guardEntry : Guard) (bodyEntry : Body) (result : Symbols Alphabet → Bool) :
    Machine Alphabet (Sum Guard Body)
  | .inl state, symbols => match guard state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none => if result symbols then some (.inr bodyEntry, stationary symbols) else none
  | .inr state, symbols => match body state symbols with
    | some (next, actions) => some (.inr next, actions)
    | none => some (.inl guardEntry, stationary symbols)

end Polytime2.MultiTape
