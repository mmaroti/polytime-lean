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

import Polytime2.Arithmetic.ScanMath
import Polytime2.Machine.CallingConvention
import Polytime2.Primitives.SymbolScan

/-! # Shared immutable-input finite-memory scanning

The source fixes the width and remains unchanged. Every output bit is written
regardless of old contents; both heads return without boundary markers.
Clearing and binary shifts use the same scan with different finite memories.
-/

namespace Polytime2.RestoringScan

open MultiTape CallingConvention
open Binary (Symbol data word)
open Copy (frame)

-- memoryLevel: the finite specialization-dependent controller memory.
universe memoryLevel
variable {Memory : Type memoryLevel}

abbrev Alphabet := fun _ : Bool => Symbol
abbrev State (Memory : Type memoryLevel) := Sum Memory (Memory × Bool)
abbrev run := @BinaryScan.run

variable (update : Memory → Bool → Memory × Bool)

def machine : Machine Alphabet (State Memory)
  | .inl memory, symbols =>
    if symbols false = 0 then
      some (.inr (memory, false), fun name => (symbols name, some .left))
    else
      let next := update memory (symbols false == 2)
      some (.inl next.1, fun name =>
        (if name then data next.2 else symbols false, some .right))
  | .inr (memory, finished), symbols =>
    if finished then none
    else if symbols false = 0 then
      some (.inr (memory, true), fun name => (symbols name, some .right))
    else some (.inr (memory, false), fun name => (symbols name, some .left))

/-- A full immutable-input scan, including empty words and arbitrary output. -/
theorem steps (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length)
    (sourceLeft sourceRight targetLeft targetRight : List Symbol) :
    Steps (machine update) (2 * bits.length + 2)
      (.inl memory, frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
        (0 :: targetLeft) (old ++ 0 :: targetRight))
      (.inr ((run update memory bits).1, true),
        frame (0 :: sourceLeft) (word bits ++ 0 :: sourceRight)
          (0 :: targetLeft) (word (run update memory bits).2 ++ 0 :: targetRight)) := by
  exact SymbolScan.steps update Binary.data memory bits old sameLength
    sourceLeft sourceRight targetLeft targetRight

/-- The complete output is overwritten while the complete source and every
surrounding blank remain unchanged throughout execution. -/
theorem runs (memory : Memory) (bits : List Bool) (old : List Symbol)
    (sameLength : old.length = bits.length) :
    Runs (fun _ : Bool => bits.length) (fun name => !name) (machine update)
      (2 * bits.length + 2) (.inl memory) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (old ++ [0]))
      (.inr ((run update memory bits).1, true)) (fun _ => 0)
      (frame [0] (word bits ++ [0]) [0] (word (run update memory bits).2 ++ [0])) := by
  exact SymbolScan.runs update Binary.data memory bits old sameLength

end Polytime2.RestoringScan
