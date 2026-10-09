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

import Polytime.AddressLookupMachine
import Polytime.RetainedLookupMachine
import Polytime.HeaderReturnMachine
import Polytime.RetainedWriteMachine
import Polytime.HeaderIncrementMachine
import Polytime.HeaderGuardMachine
import Polytime.HeaderResetMachine
import Polytime.HeaderScalarMachine
import Polytime.HeaderMoveMachine

/-! # Checked address preparation and prepared-frame lookup -/

namespace Polytime.Examples.AddressPreparation

open TupleMachine

example : Fintype CounterMachine.State := inferInstance
example : Fintype AddressMachine.State := inferInstance
example (width : ℕ) : Fintype (AddressLookupMachine.State width) := inferInstance

/-- Observe the incremented counter and its retained start marker/context. -/
def increment (width value : ℕ) (left right : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run CounterMachine.machine (3 * width + 3)
    (Tape.configuration 0 (3 :: left) (word (Binary.digits width value) ++ right))).map
    fun final => ((List.range (width + right.length)).map final.Tape.right₀.nth,
      (List.range (left.length + 1)).map final.Tape.left.nth)

#guard increment 4 0 [7, 4] [4, 7] = some ([2, 1, 1, 1, 4, 7], [3, 7, 4])
#guard increment 4 7 [7, 4] [4, 7] = some ([1, 1, 1, 2, 4, 7], [3, 7, 4])
#guard increment 4 14 [7, 4] [4, 7] = some ([2, 2, 2, 2, 4, 7], [3, 7, 4])
#guard increment 1 0 [7, 4] [4, 7] = some ([2, 4, 7], [3, 7, 4])

/-- Observe conversion, including consumed unary scratch and preserved contexts. -/
def convert (width value : ℕ) (left right : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run AddressMachine.machine ((value + 1) * (3 * width + 2 * value + 12))
    (Tape.configuration (.inl 3) (3 :: (UnaryMachine.units value ++ 7 :: left))
      (word (Binary.digits width 0) ++ right))).map
    fun final => ((List.range (width + right.length)).map final.Tape.right₀.nth,
      (List.range (value + left.length + 2)).map final.Tape.left.nth)

#guard convert 0 0 [4, 7] [4, 7] = some ([4, 7], [3, 7, 4, 7])
#guard convert 4 0 [4, 7] [4, 7] = some ([1, 1, 1, 1, 4, 7], [3, 7, 4, 7])
#guard convert 4 15 [4, 7] [4, 7] =
  some ([2, 2, 2, 2, 4, 7], [3] ++ List.replicate 15 0 ++ [7, 4, 7])
#guard convert 5 8 [4, 7] [4, 7] =
  some ([1, 1, 1, 2, 1, 4, 7], [3] ++ List.replicate 8 0 ++ [7, 4, 7])

/-- Convert a unary address and read a complete field in the same frame. -/
def lookup (width : ℕ) (bits : List Bool) (index : Fin bits.length) (left right : List Symbol) :
    Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (AddressLookupMachine.machine (width := width)) (512 * (bits.length + 1) ^ 2)
    (Tape.configuration (.inl (.inl 3))
      (3 :: (List.replicate width 0 ++ UnaryMachine.units index.val ++ 7 :: left))
      (word (Binary.digits bits.length 0) ++ 4 :: (word bits ++ right)))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range left.length).map (fun position => final.Tape.left.nth (index.val + 1 + position)))

#guard lookup 3 [false, true, false, true, true, false] 0 [7, 3] [4, 7] =
  some ([1, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard lookup 3 [false, true, false, true, true, false] 3 [7, 3] [4, 7] =
  some ([2, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard lookup 3 [false, true, false, true, false, true, false, true, false, true, true]
    8 [4, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7], [4, 3])

/-- The same pipeline starting from the preparer's blank binary window. -/
def lookupFromBlank (width : ℕ) (bits : List Bool) (index : Fin bits.length)
    (left right : List Symbol) : Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (Tape.sequence AddressMachine.ZeroWindow.machine
      (AddressLookupMachine.machine (width := width)) (.inl (.inl 3))) (640 * (bits.length + 1) ^ 2)
    (Tape.configuration (.inl 0)
      (3 :: (List.replicate width 0 ++ UnaryMachine.units index.val ++ 7 :: left))
      (List.replicate bits.length 0 ++ 4 :: (word bits ++ right)))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range left.length).map (fun position => final.Tape.left.nth (index.val + 1 + position)))

#guard lookupFromBlank 3 [false, true, false, true, true, false] 0 [7, 3] [4, 7] =
  some ([1, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard lookupFromBlank 3 [false, true, false, true, true, false] 3 [7, 3] [4, 7] =
  some ([2, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard lookupFromBlank 3 [false, true, false, true, false, true, false, true, false, true, true]
    8 [4, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7], [4, 3])

/-- Start at the forward unary address rather than the binary scratch window. -/
def lookupForward (width : ℕ) (bits : List Bool) (index : Fin bits.length)
    (left right : List Symbol) : Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (Tape.sequence AddressLookupMachine.PositionCursor.machine
      (Tape.sequence AddressMachine.ZeroWindow.machine
        (AddressLookupMachine.machine (width := width)) (.inl (.inl 3))) (.inl 0))
    (704 * (bits.length + 1) ^ 2)
    (Tape.configuration (.inl 0) left
      (7 :: (UnaryMachine.units index.val ++ List.replicate width 0 ++ 3 ::
        (List.replicate bits.length 0 ++ 4 :: (word bits ++ right)))))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range left.length).map (fun position => final.Tape.left.nth (index.val + 1 + position)))

#guard lookupForward 3 [false, true, false, true, true, false] 0 [7, 3] [4, 7] =
  some ([1, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], [7, 3])
#guard lookupForward 3 [false, true, false, true, false, true, false, true, false, true, true]
    8 [4, 3] [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7], [4, 3])

/-- Read from the evaluator's result layout, retaining its counter fields. -/
def lookupEvaluated (width : ℕ) (bits : List Bool) (index : Fin bits.length)
    (retained right : List Symbol) (scratchSymbol : Symbol := 0)
    (window : List Symbol := List.replicate width 0) : Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (Tape.sequence RetainedLookupMachine.Entry.machine
      (Tape.sequence AddressMachine.ZeroWindow.machine
        (RetainedLookupMachine.machine (width := width)) (.inl (.inl 3))) (.inl 0))
    (1280 * (bits.length + retained.length + 1) ^ 2)
    (Tape.configuration (.inl 0) []
      (UnaryMachine.units index.val ++ 1 :: (retained ++ window ++ 3 ::
        (List.replicate bits.length scratchSymbol ++ 4 :: (word bits ++ right)))))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range (retained.length + index.val + 2)).map final.Tape.left.nth)

#guard lookupEvaluated 3 [false, true, false, true, true, false] 0
    (UnaryMachine.fields [0, 3, 5]) [4, 7] =
  some ([1, 2, 1], [1, 2, 1, 2, 2, 1, 4, 7], (UnaryMachine.fields [0, 3, 5]).reverse ++ [6, 7])
#guard lookupEvaluated 3 [false, true, false, true, false, true, false, true, false, true, true] 8
    (UnaryMachine.fields [2, 0, 4]) [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7],
    (UnaryMachine.fields [2, 0, 4]).reverse ++ 6 :: (List.replicate 8 0 ++ [7]))

-- The initializer also accepts the all-one counter left by the preceding read.
#guard lookupEvaluated 3 [false, true, false, true, false, true, false, true, false, true, true] 8
    (UnaryMachine.fields [2, 0, 4]) [4, 7] 2 =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7],
    (UnaryMachine.fields [2, 0, 4]).reverse ++ 6 :: (List.replicate 8 0 ++ [7]))

-- Reuse both an existing scalar output and the consumed binary counter.
#guard lookupEvaluated 3 [false, true, false, true, false, true, false, true, false, true, true] 8
    (UnaryMachine.fields [2, 0, 4]) [4, 7] 2 [2, 1, 1] =
  some ([1, 2, 2], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 4, 7],
    (UnaryMachine.fields [2, 0, 4]).reverse ++ 6 :: (List.replicate 8 0 ++ [7]))

/-- Observe the restored header and suffix, and confirm that left scratch is blank. -/
def returnHeader (values scratch : List ℕ) (address : ℕ) (suffix : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderReturnMachine.machine values.length)
    ((UnaryMachine.fields values).length + 3 * ((UnaryMachine.fields scratch).length + address) + 8)
    (Tape.configuration (Fin.last values.length, 0)
      ((UnaryMachine.fields values).reverse ++ (UnaryMachine.fields scratch).reverse ++
        6 :: (List.replicate address 0 ++ [7])) suffix)).map
    fun final => ((List.range ((UnaryMachine.fields values).length + suffix.length)).map final.Tape.right₀.nth,
      (List.range 8).map final.Tape.left.nth)

#guard returnHeader [0, 0, 3] [] 0 [2, 1, 2, 3, 2, 2, 4, 2, 1, 7] =
  some (UnaryMachine.fields [0, 0, 3] ++ [2, 1, 2, 3, 2, 2, 4, 2, 1, 7], List.replicate 8 0)
#guard returnHeader [2, 0, 4] [0, 3, 5] 8 [1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 7] =
  some (UnaryMachine.fields [2, 0, 4] ++ [1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 7], List.replicate 8 0)

/-- Observe the runtime replacement, updated array, and retained evaluator fields. -/
def writeEvaluated (width : ℕ) (replacement : BitVec width) (bits : List Bool)
    (index : Fin bits.length) (retained right : List Symbol) (inputSymbol : Symbol := 0) :
    Option (List Symbol × List Symbol × List Symbol) :=
  (Tape.run (Tape.sequence RetainedLookupMachine.Entry.machine
      (Tape.sequence AddressMachine.ZeroWindow.machine
        (RetainedWriteMachine.machine (width := width)) (.inl (.inl 3))) (.inl 0))
    (1024 * (bits.length + retained.length + 1) ^ 2)
    (Tape.configuration (.inl 0) []
      (UnaryMachine.units index.val ++ 1 :: (retained ++ word (List.ofFn (BoolTuple.fromBits replacement)) ++ 3 ::
        (List.replicate bits.length inputSymbol ++ 4 :: (word bits ++ right)))))).map
    fun final =>
      ((List.range width).map final.Tape.right₀.nth,
        (List.range (bits.length + right.length)).map
          (fun position => final.Tape.right₀.nth (width + bits.length + 2 + position)),
        (List.range (retained.length + index.val + 2)).map final.Tape.left.nth)

#guard writeEvaluated 3 (BitVec.ofNat 3 6) [false, true, false, true, true, false] 0
    (UnaryMachine.fields [0, 3, 5]) [4, 7] =
  some ([1, 2, 2], [1, 2, 2, 2, 2, 1, 4, 7], (UnaryMachine.fields [0, 3, 5]).reverse ++ [6, 7])
#guard writeEvaluated 3 (BitVec.ofNat 3 6) [false, true, false, true, true, false] 3
    (UnaryMachine.fields [2, 0, 4]) [4, 7] =
  some ([1, 2, 2], [1, 2, 1, 1, 2, 2, 4, 7],
    (UnaryMachine.fields [2, 0, 4]).reverse ++ 6 :: (List.replicate 3 0 ++ [7]))
#guard writeEvaluated 3 (BitVec.ofNat 3 5)
    [false, true, false, true, false, true, false, true, false, true, true] 8
    (UnaryMachine.fields [2, 0, 4]) [4, 7] 2 =
  some ([2, 1, 2], [1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 7],
    (UnaryMachine.fields [2, 0, 4]).reverse ++ 6 :: (List.replicate 8 0 ++ [7]))
#guard writeEvaluated 1 (BitVec.ofNat 1 1) [false] 0 (UnaryMachine.fields [0, 0, 1]) [4, 7] =
  some ([2], [2, 4, 7], (UnaryMachine.fields [0, 0, 1]).reverse ++ [6, 7])

/-- Observe the incremented unary header and unchanged frame suffix. -/
def incrementHeader (prior : List ℕ) (value : ℕ) (suffix : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderIncrementMachine.machine prior.length) (3 * (UnaryMachine.fields prior).length + 2)
    (Tape.configuration (.inl (Fin.last prior.length)) []
      (UnaryMachine.fields (prior ++ [value]) ++ suffix))).map fun final =>
    ((List.range ((UnaryMachine.fields (prior ++ [value + 1])).length + suffix.length)).map final.Tape.right₀.nth,
      (List.range 4).map final.Tape.left.nth)

#guard incrementHeader [] 0 [1, 3, 4, 7] =
  some (UnaryMachine.fields [1] ++ [1, 3, 4, 7], List.replicate 4 0)
#guard incrementHeader [0] 0 [2, 1, 3, 4, 7] =
  some (UnaryMachine.fields [0, 1] ++ [2, 1, 3, 4, 7], List.replicate 4 0)
#guard incrementHeader [2, 0] 3 [0, 3, 4, 7] =
  some (UnaryMachine.fields [2, 0, 4] ++ [0, 3, 4, 7], List.replicate 4 0)
#guard incrementHeader [3, 2] 0 [1, 2, 3, 4] =
  some (UnaryMachine.fields [3, 2, 1] ++ [1, 2, 3, 4], List.replicate 4 0)

/-- Observe the result bit, restored counters, suffix, and cleared left scratch. -/
def guardHeader (prior : List ℕ) (index limit : ℕ) (suffix : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderGuardMachine.machine prior.length)
    (2 * index ^ 2 + 10 * index + 2 * (UnaryMachine.fields prior).length + 8)
    (Tape.configuration (Fin.last prior.length, false, 0) []
      (UnaryMachine.fields (prior ++ [index, limit]) ++ suffix))).map fun final =>
    ((List.range ((UnaryMachine.fields (prior ++ [index, limit])).length + suffix.length + 1)).map
      final.Tape.right₀.nth, (List.range 4).map final.Tape.left.nth)

#guard guardHeader [] 0 0 [3, 4, 7] =
  some (data false :: (UnaryMachine.fields [0, 0] ++ [3, 4, 7]), List.replicate 4 0)
#guard guardHeader [0] 0 3 [2, 1, 3, 4, 7] =
  some (data true :: (UnaryMachine.fields [0, 0, 3] ++ [2, 1, 3, 4, 7]), List.replicate 4 0)
#guard guardHeader [2] 3 3 [0, 3, 4, 7] =
  some (data false :: (UnaryMachine.fields [2, 3, 3] ++ [0, 3, 4, 7]), List.replicate 4 0)
#guard guardHeader [0, 2] 3 5 [1, 2, 3, 4] =
  some (data true :: (UnaryMachine.fields [0, 2, 3, 5] ++ [1, 2, 3, 4]), List.replicate 4 0)

/-- Observe the reset counter, preserved neighboring fields, and frame suffix. -/
def resetHeader (prior : List ℕ) (value : ℕ) (suffix : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderResetMachine.machine prior.length)
    (value * (6 * (UnaryMachine.fields prior).length + 4) + 2 * (UnaryMachine.fields prior).length + 2)
    (Tape.configuration (.inl (Fin.last prior.length)) []
      (UnaryMachine.fields (prior ++ [value]) ++ suffix))).map fun final =>
    ((List.range ((UnaryMachine.fields (prior ++ [0])).length + suffix.length)).map final.Tape.right₀.nth,
      (List.range 4).map final.Tape.left.nth)

#guard resetHeader [] 0 [3, 4, 7] =
  some (UnaryMachine.fields [0] ++ [3, 4, 7], List.replicate 4 0)
#guard resetHeader [] 5 [1, 2, 3, 4] =
  some (UnaryMachine.fields [0] ++ [1, 2, 3, 4], List.replicate 4 0)
#guard resetHeader [0] 3 [0, 3, 4, 7] =
  some (UnaryMachine.fields [0, 0] ++ [0, 3, 4, 7], List.replicate 4 0)
#guard resetHeader [2, 0] 4 [1, 2, 3, 4, 7] =
  some (UnaryMachine.fields [2, 0, 0] ++ [1, 2, 3, 4, 7], List.replicate 4 0)
#guard resetHeader [2, 0] 0 [0, 3, 4, 7] =
  some (UnaryMachine.fields [2, 0, 0] ++ [0, 3, 4, 7], List.replicate 4 0)

/-- Observe a copied scalar before the preserved header and original scalar. -/
def copyHeaderScalar (values : List ℕ) {width : ℕ} (bits : BitVec width) (tail : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderScalarMachine.machine values.length width)
    (2 * (UnaryMachine.fields values).length + 4 * width + 5)
    (Tape.configuration (.inl (Fin.last values.length)) []
      (UnaryMachine.fields values ++ word (List.ofFn (BoolTuple.fromBits bits)) ++ tail))).map fun final =>
    ((List.range (2 * width + (UnaryMachine.fields values).length + tail.length)).map final.Tape.right₀.nth,
      (List.range 4).map final.Tape.left.nth)

#guard copyHeaderScalar [2, 0, 3] (BitVec.ofNat 3 5) [3, 4, 7] =
  some ([2, 1, 2] ++ UnaryMachine.fields [2, 0, 3] ++ [2, 1, 2, 3, 4, 7], List.replicate 4 0)
#guard copyHeaderScalar [0, 0, 0] (BitVec.ofNat 3 2) [] =
  some ([1, 2, 1] ++ UnaryMachine.fields [0, 0, 0] ++ [1, 2, 1], List.replicate 4 0)
#guard copyHeaderScalar [] (BitVec.ofNat 3 6) [0, 7] =
  some ([1, 2, 2, 1, 2, 2, 0, 7], List.replicate 4 0)
#guard copyHeaderScalar [2, 0] (BitVec.ofNat 0 0) [3, 4, 7] =
  some (UnaryMachine.fields [2, 0] ++ [3, 4, 7], List.replicate 4 0)
#guard copyHeaderScalar [] (BitVec.ofNat 0 0) [] = some ([], List.replicate 4 0)

/-- Observe runtime header relocation without changing the frame suffix. -/
def moveHeader (before after : List ℕ) (value : ℕ) (suffix : List Symbol) :
    Option (List Symbol × List Symbol) :=
  (Tape.run (HeaderMoveMachine.machine before.length)
    (128 * ((UnaryMachine.fields (before ++ value :: after)).length + 1) ^ 2)
    (Tape.configuration (.inl (Fin.last before.length, 0)) []
      (UnaryMachine.fields (before ++ value :: after) ++ suffix))).map fun final =>
    ((List.range ((UnaryMachine.fields (value :: before ++ after)).length + suffix.length)).map final.Tape.right₀.nth,
      (List.range 4).map final.Tape.left.nth)

#guard moveHeader [2] [1, 3] 0 [2, 1, 3, 2, 4, 1, 7] =
  some (UnaryMachine.fields [0, 2, 1, 3] ++ [2, 1, 3, 2, 4, 1, 7], List.replicate 4 0)
#guard moveHeader [0] [0, 3] 2 [0, 3, 4, 7] =
  some (UnaryMachine.fields [2, 0, 0, 3] ++ [0, 3, 4, 7], List.replicate 4 0)
#guard moveHeader [0] [0, 0] 0 [1, 2, 3, 4] =
  some (UnaryMachine.fields [0, 0, 0, 0] ++ [1, 2, 3, 4], List.replicate 4 0)
#guard moveHeader [1, 2] [] 3 [] =
  some (UnaryMachine.fields [3, 1, 2], List.replicate 4 0)
#guard moveHeader [] [] 0 [] = some (UnaryMachine.fields [0], List.replicate 4 0)

end Polytime.Examples.AddressPreparation
