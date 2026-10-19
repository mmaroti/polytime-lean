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

import Polytime2.Machine.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

/-! # Internal polynomial certificates for machine simulation

The same machine and natural-coefficient polynomial work for all size
assignments and all tapes satisfying the mathematical precondition. No
behavior is required outside that precondition. This transport predicate is
internal to the simulator; public computations use `Computation.Realizable`.
-/

namespace Polytime2.MultiTape

-- parameterLevel: size names; tapeLevel: tape names; symbolLevel: alphabets.
-- stateLevel: the finite controller carrier.
universe parameterLevel tapeLevel symbolLevel stateLevel

variable {Parameter : Type parameterLevel}
variable {TapeName : Type tapeLevel}
variable {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]
variable {State : Type stateLevel}

/-- Internal simulator transport with an existential polynomial transition bound. -/
def Internal.Realizes [Fintype Parameter] [Fintype TapeName]
    [∀ name, Fintype (Alphabet name)] [Fintype State]
    (machine : Machine Alphabet State) (entry exit : State)
    (precondition : (Parameter → ℕ) → Tapes Alphabet → Prop)
    (postcondition : (Parameter → ℕ) → Tapes Alphabet → Tapes Alphabet → Prop) : Prop :=
  (∀ symbols, machine exit symbols = none) ∧
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment initial, precondition assignment initial →
        ∃ ticks final, ticks ≤ MvPolynomial.eval assignment bound ∧
          Steps machine ticks (entry, initial) (exit, final) ∧
          postcondition assignment initial final

end Polytime2.MultiTape
