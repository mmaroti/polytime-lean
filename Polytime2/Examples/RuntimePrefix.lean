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

import Polytime2.Arrays.PrefixFlags
import Polytime2.Matrices.HermiteStageController
import Polytime2.TM0.Computation

/-! # Runtime prefixes inside fixed-length traversals

Prefix lengths zero, two, and three use the same three-element storage.
An unselected stage token retains its accumulator even when the underlying
stage's source and target coincide, so it requires no stage-admissibility proof.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Examples.RuntimePrefix

open Polytime2.Computation Polytime2.Computation.Realizable.Internal

example {Parameter : Type} [Fintype Parameter] (length : MvPolynomial Parameter ℕ) :
    (arrayPrefixFlags length).TM0Realizable := (arrayPrefixFlags_realizable length).tm0

example {Parameter : Type} [Fintype Parameter] (rows columns workspace : MvPolynomial Parameter ℕ) :
    (hermiteStageSelectedUpdate rows columns workspace).TM0Realizable :=
  (hermiteStageSelectedUpdate_realizable rows columns workspace).tm0

example :
    (arrayPrefixFlags (Parameter := Empty) 3).compute Empty.elim
      ⟨(fun _ => ⟨2, by norm_num⟩), trivial⟩ ⟨0, by norm_num⟩ = true ∧
    (arrayPrefixFlags (Parameter := Empty) 3).compute Empty.elim
      ⟨(fun _ => ⟨2, by norm_num⟩), trivial⟩ ⟨2, by norm_num⟩ = false ∧
    (arrayPrefixFlags (Parameter := Empty) 3).compute Empty.elim
      ⟨(fun _ => ⟨0, by norm_num⟩), trivial⟩ ⟨0, by norm_num⟩ = false ∧
    (arrayPrefixFlags (Parameter := Empty) 3).compute Empty.elim
      ⟨(fun _ => ⟨3, by norm_num⟩), trivial⟩ ⟨2, by norm_num⟩ = true := by
  change decide ((0 : ℕ) < 2) = true ∧ decide ((2 : ℕ) < 2) = false ∧
    decide ((0 : ℕ) < 0) = false ∧ decide ((2 : ℕ) < 3) = true
  decide

example : ArrayFold.prefixValue (fun value (token : Bool × ℕ) => if token.1 then value + token.2 else value)
    (fun index : Fin 3 => (decide (index.val < 2), index.val + 1)) 0 3 = 3 := by
  calc
    _ = ArrayFold.prefixValue (fun value token : ℕ => value + token) (fun index : Fin 3 => index.val + 1) 0 (min 3 2) :=
      ArrayFold.prefix_guarded (fun value token : ℕ => value + token) (fun index : Fin 3 => index.val + 1) 0 2 3 (by decide)
    _ = 3 := by decide +kernel

private noncomputable def skippedArguments : (hermiteStageSelectedUpdate (Parameter := Empty) 1 1 0).Arguments Empty.elim
  | .inl 0 | .inl 1 | .inl 2 => ⟨0, by norm_num⟩
  | .inr false => (⟨0, by intros; simp⟩, ⟨0, by intros; simp⟩)
  | .inr true => (false, ⟨0, by norm_num⟩)

private theorem skippedValid :
    (hermiteStageSelectedUpdate (Parameter := Empty) 1 1 0).precondition Empty.elim skippedArguments := by
  intro impossible
  change false = true at impossible
  cases impossible

example : (hermiteStageSelectedUpdate (Parameter := Empty) 1 1 0).compute Empty.elim
    ⟨skippedArguments, skippedValid⟩ = skippedArguments (.inr false) := rfl

end Polytime2.Examples.RuntimePrefix
