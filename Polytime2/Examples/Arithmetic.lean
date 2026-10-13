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

import Polytime2.AddMultiply
import Polytime2.BinarySubtraction
import Polytime2.StandardBinaryDecrement
import Polytime2.StandardBinaryIncrement
import Polytime2.StandardCounterZero

/-! # Composed arithmetic boundary cases

Separate immutable operands share a fixed-capacity intermediate sum. Output
and scratch regions may initially be blank or contain arbitrary old symbols.
-/

namespace Polytime2.Examples.Arithmetic

#guard Binary.value (AddMultiply.product
  [true, true, true, false, false, false, false]
  [true, false, false, false, false, false, false] [true, false, true, true]
  (List.replicate 7 0) (List.replicate 7 0) 2) = 104

-- The final subtraction bit is the borrow; lower bits retain their capacity.
#guard BinarySubtraction.subtract [true, true, false] [true, false, true] =
  [false, true, true, true]
#guard BinarySubtraction.subtract [true, false, true] [true, true, false] =
  [false, true, false, false]
#guard BinarySubtraction.subtract [true, false, true] [true, false, true] =
  [false, false, false, false]
#guard BinarySubtraction.subtract [] [] = [false]

-- The complete composition accepts blank output and an arbitrary old carry.
example :
    let left := [true, true, true, false, false, false, false]
    let right := [true, false, false, false, false, false, false]
    let multiplier := [true, false, true, true]
    let empty : List Binary.Symbol := List.replicate 7 0
    CallingConvention.Runs (AddMultiply.widths 7 4) AddMultiply.readOnly AddMultiply.machine
      297 AddMultiply.entry (fun _ => 0)
      (AddMultiply.frame left right multiplier empty empty empty empty 2 2)
      AddMultiply.exit (fun _ => 0)
      (AddMultiply.frame left right multiplier
        (Binary.word (AddMultiply.product left right multiplier empty empty 2))
        (Binary.word (AddMultiply.sum left right))
        (Binary.word (List.replicate 7 false)) (Binary.word (List.replicate 7 false))
        (Binary.data false) (Binary.data false)) := by
  exact AddMultiply.runs [true, true, true, false, false, false, false]
    [true, false, false, false, false, false, false] [true, false, true, true] rfl
    (List.replicate 7 0) (List.replicate 7 0) (List.replicate 7 0) (List.replicate 7 0)
    rfl rfl rfl rfl 2 2 (by decide)

-- Zero-width words still initialize both flags and all scratch.
example : CallingConvention.Runs (AddMultiply.widths 0 0) AddMultiply.readOnly AddMultiply.machine
    17 AddMultiply.entry (fun _ => 0) (AddMultiply.frame [] [] [] [] [] [] [] 2 2)
    AddMultiply.exit (fun _ => 0)
    (AddMultiply.frame [] [] [] [] [] [] [] (Binary.data false) (Binary.data false)) :=
  AddMultiply.runs [] [] [] rfl [] [] [] [] rfl rfl rfl rfl 2 2 (by decide)

-- Decrement writes through blank digits and propagates a borrow across zeros.
example : CallingConvention.Runs (fun _ : Bool => 4) (fun name => !name)
    StandardBinaryDecrement.machine 11 StandardBinaryDecrement.entry (fun _ => 0)
    (Copy.frame [0] (Binary.word [false, false, false, true] ++ [0]) [0] [0, 2, 0, 0, 0])
    StandardBinaryDecrement.exit (fun _ => 0)
    (Copy.frame [0] (Binary.word [false, false, false, true] ++ [0]) [0]
      (Binary.word [true, true, true, false] ++ [0])) :=
  StandardBinaryDecrement.runs [false, false, false, true] [0, 2, 0, 0] rfl

example : CallingConvention.Runs (fun _ : Bool => 0) (fun name => !name)
    StandardBinaryDecrement.machine 3 StandardBinaryDecrement.entry (fun _ => 0)
    (Copy.frame [0] [0] [0] [0]) StandardBinaryDecrement.exit (fun _ => 0)
    (Copy.frame [0] [0] [0] [0]) := StandardBinaryDecrement.runs [] [] rfl

example : Fintype AddMultiply.State := inferInstance

-- Fixed constants overwrite arbitrary old contents without a source.
example : CallingConvention.Runs (fun _ : Unit => 2) (fun _ => false)
    (StandardConstant.machine [false, true]) 5 (false, 2) (fun _ => 0)
    (fun _ => CallingConvention.buffer [0, 2]) (true, 0) (fun _ => 0)
    (fun _ => CallingConvention.buffer (Binary.word [false, true])) :=
  StandardConstant.runs [false, true] [0, 2] rfl

-- An empty encoded constant needs no data cells and still has a restoring exit.
example : CallingConvention.Runs (fun _ : Unit => 0) (fun _ => false)
    (StandardConstant.machine []) 1 (false, 0) (fun _ => 0)
    (fun _ => CallingConvention.buffer []) (true, 0) (fun _ => 0)
    (fun _ => CallingConvention.buffer []) := StandardConstant.runs [] [] rfl

-- Counter capacity is retained on overflow; no digit is appended.
#guard BinaryScan.run BinaryScan.increment true [true, true, true] =
  (true, [false, false, false])
#guard BinaryScan.run BinaryScan.increment true [false, false, true] =
  (false, [true, false, true])
#guard BinaryScan.run BinaryScan.increment true [] = (true, [])
#guard StandardBinaryIncrement.next () (fun _ => 3) (7 : Fin 8) = 0
#guard StandardBinaryIncrement.next () (fun _ => 0) (0 : Fin 1) = 0

end Polytime2.Examples.Arithmetic
