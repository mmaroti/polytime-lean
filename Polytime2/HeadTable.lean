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

/-! # Fixed tables on symbols under the heads

Finite-field arithmetic, scalar copying, and scalar tests use a table on
the fixed finite product of tape alphabets. One transition writes its result
without moving any head. This grants no access to cells away from the heads.
-/

namespace Polytime2.HeadTable

open MultiTape

-- tapeLevel: tape names; symbolLevel: their alphabets; parameterLevel: runtime size names.
universe tapeLevel symbolLevel parameterLevel
variable {TapeName : Type tapeLevel} {Alphabet : TapeName → Type symbolLevel}
variable [∀ name, Inhabited (Alphabet name)]

def machine (table : Symbols Alphabet → Symbols Alphabet) : Machine Alphabet Bool :=
  fun finished symbols => if finished then none else some (true, fun name => (table symbols name, none))

theorem steps (table : Symbols Alphabet → Symbols Alphabet) (initial : Tapes Alphabet) :
    Steps (machine table) 1 (false, initial)
      (true, fun name => (initial name).write (table (read initial) name)) := by
  exact .next rfl (.zero _)

theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter] [Fintype TapeName]
    [∀ name, Fintype (Alphabet name)] (table : Symbols Alphabet → Symbols Alphabet) :
    Realizes (machine table) false true (fun (_assignment : Parameter → ℕ) _ => True)
      (fun _ initial final => final = fun name => (initial name).write (table (read initial) name)) := by
  refine ⟨by intro symbols; rfl, 1, ?_⟩
  intro assignment initial _valid
  exact ⟨1, _, by simp, steps table initial, rfl⟩

end Polytime2.HeadTable
