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

/-! # Branching on finitely many scanned symbols

An arbitrary predicate on the scanned symbols is a fixed finite table when
the alphabets and tape set are finite. More expensive guards must first be
computed by a certified machine. Selection and the common exit each cost one
stationary transition; only the selected controller executes.
-/

namespace Polytime2.MultiTape

-- tapeLevel: tape names; symbolLevel: alphabets; firstLevel, secondLevel: controllers.
universe tapeLevel symbolLevel firstLevel secondLevel

variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {First : Type firstLevel} {Second : Type secondLevel}

def branchMachine (condition : Symbols Alphabet → Bool)
    (first : Machine Alphabet First) (second : Machine Alphabet Second)
    (firstEntry : First) (secondEntry : Second) : Machine Alphabet (Sum Unit (Sum First Second))
  | .inl (), symbols => if condition symbols then
      some (.inr (.inl firstEntry), stationary symbols)
    else some (.inr (.inr secondEntry), stationary symbols)
  | .inr (.inl state), symbols =>
    (first state symbols).map fun command => (.inr (.inl command.1), command.2)
  | .inr (.inr state), symbols =>
    (second state symbols).map fun command => (.inr (.inr command.1), command.2)

end Polytime2.MultiTape
