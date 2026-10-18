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

import Polytime2.StandardBinaryMultiplication

/-! # Multiplication from blank output and scratch regions -/

namespace Polytime2.Examples.Multiplication

open StandardBinaryMultiplication

#guard Binary.value (finish [true, false, true, true, false, false, false]
  [true, false, true].reverse
  (List.replicate 7 false)) = 65

-- The same finite controller handles different factor and multiplier widths.
example :
    let factor := [true, false, true, true, false, false, false]
    let input := [true, false, true]
    let empty : List Binary.Symbol := List.replicate 7 0
    CallingConvention.Runs (widths 3 7) readOnly machine 224 entry (fun _ => 0)
      (initialFrame input factor empty empty empty 2) exit (fun _ => 0)
      (frame (CallingConvention.buffer (Binary.word input)) factor
        (finish factor input.reverse (List.replicate 7 false), Binary.word (List.replicate 7 false),
          Binary.word (List.replicate 7 false), Binary.data false)) := by
  exact runs [true, false, true] [true, false, true, true, false, false, false]
    (List.replicate 7 0) (List.replicate 7 0) (List.replicate 7 0) rfl rfl rfl 2

-- Even empty operands overwrite the flag and restore all heads.
example : CallingConvention.Runs (widths 0 0) readOnly machine 14 entry (fun _ => 0)
    (initialFrame [] [] [] [] [] 2) exit (fun _ => 0)
    (frame (CallingConvention.buffer []) [] ([], [], [], Binary.data false)) :=
  runs [] [] [] [] [] rfl rfl rfl 2

-- No body call occurs for an empty multiplier; cleanup still initializes scratch.
example : CallingConvention.Runs (widths 0 2) readOnly machine 26 entry (fun _ => 0)
    (initialFrame [] [true, true] [0, 2] [2, 0] [0, 0] 2) exit (fun _ => 0)
    (frame (CallingConvention.buffer []) [true, true]
      ([false, false], Binary.word [false, false], Binary.word [false, false], Binary.data false)) :=
  runs [] [true, true] [0, 2] [2, 0] [0, 0] rfl rfl rfl 2

example : Fintype State := inferInstance

end Polytime2.Examples.Multiplication
