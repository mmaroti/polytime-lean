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
import Polytime2.Gcd
import Polytime2.StandardBinaryRemainder
import Polytime2.StandardBinaryGuard
import Polytime2.StandardGcdStep
import Polytime2.StandardGcdMachine
import Polytime2.StandardGcd

/-! # Gcd boundary cases and bit-length progress

These checks exercise mathematical gcd, binary remainder, and the standard
separate-tape calling convention, including zero operands.
-/

namespace Polytime2.Examples.Gcd

#guard Gcd.run (0, 0) = 0
#guard Gcd.run (0, 37) = 37
#guard Gcd.run (37, 0) = 37
#guard Gcd.run (48, 18) = 6
#guard Gcd.run (18, 48) = 6
#guard Gcd.run (144, 89) = 1
#guard Gcd.run (2 ^ 64, 2 ^ 48) = 2 ^ 48
#guard Gcd.iterations (144, 89) = 10
#guard Gcd.iterations (2 ^ 64, 2 ^ 48) = 1

example (bits left right : ℕ) (capacity : left < 2 ^ bits ∧ right < 2 ^ bits) :
    Gcd.iterations (left, right) ≤ 2 * bits + 1 := Gcd.iterations_capacity bits (left, right) capacity

example (left right : ℕ) : Gcd.run (left, right) = Nat.gcd left right :=
  Gcd.run_correct (left, right)

#guard Binary.value (StandardBinaryRemainder.finish [true, false, true, false, false]
  [true, false, true, true, false].reverse
  (List.replicate 5 false, List.replicate 5 0, List.replicate 5 0, List.replicate 5 0, 0)).1 = 3
#guard Binary.value (StandardBinaryRemainder.finish [true, true, false, false]
  [false, true, true, false].reverse
  (List.replicate 4 false, List.replicate 4 0, List.replicate 4 0, List.replicate 4 0, 0)).1 = 0
#guard Binary.value (StandardBinaryRemainder.finish [true] []
  ([false], [0], [0], [0], 0)).1 = 0

-- The same fixed controller realizes 13 % 5 from entirely blank writable regions.
example :
    let dividend := [true, false, true, true, false]
    let divisor := [true, false, true, false, false]
    let empty : List Binary.Symbol := List.replicate 5 0
    let work : StandardBinaryRemainder.Workspace :=
      (List.replicate 5 false, empty, empty, empty, 0)
    CallingConvention.Runs (StandardBinaryRemainder.widths 5 5) StandardBinaryRemainder.readOnly
      StandardBinaryRemainder.machine 301
      StandardBinaryRemainder.entry (fun _ => 0)
      (StandardBinaryRemainder.initialFrame (CallingConvention.buffer (Binary.word dividend))
        divisor empty work)
      StandardBinaryRemainder.exit (fun _ => 0)
      (StandardBinaryRemainder.frame (CallingConvention.buffer (Binary.word dividend)) divisor
        (StandardBinaryRemainder.finish divisor dividend.reverse work)) := by
  exact StandardBinaryRemainder.runs [true, false, true, true, false]
    [true, false, true, false, false] (List.replicate 5 0) (List.replicate 5 0)
    (List.replicate 5 0) (List.replicate 5 0) rfl rfl rfl rfl 0

-- An empty counter still writes a one-bit false result from a blank output.
example : CallingConvention.Runs (StandardBinaryGuard.widths 0) StandardBinaryGuard.readOnly
    StandardBinaryGuard.machine 2 (false, 0) (fun _ => 0)
    (Copy.frame [0] [0] [0] [0, 0]) (false, 2) (fun _ => 0)
    (Copy.frame [0] [0] [0] [Binary.data false, 0]) :=
  StandardBinaryGuard.runs [] 0

-- One Euclidean step preserves both inputs and completely writes both outputs.
example :
    let left := [true, false, true, true, false]
    let right := [true, false, true, false, false]
    let empty : List Binary.Symbol := List.replicate 5 0
    let work : StandardGcdStep.Workspace :=
      (List.replicate 5 false, empty, empty, empty, 0)
    CallingConvention.Runs (StandardGcdStep.widths 5) StandardGcdStep.readOnly
      StandardGcdStep.machine 314 StandardGcdStep.entry (fun _ => 0)
      (StandardGcdStep.initialFrame left right work empty empty)
      StandardGcdStep.exit (fun _ => 0)
      (StandardGcdStep.frame left right (StandardBinaryRemainder.finish right left.reverse work)
        (Binary.word right)) := by
  exact StandardGcdStep.runs [true, false, true, true, false] [true, false, true, false, false]
    rfl (List.replicate 5 0) (List.replicate 5 0) (List.replicate 5 0)
    (List.replicate 5 0) (List.replicate 5 0) rfl rfl rfl rfl rfl 0

-- Empty operands still return canonical scratch and a false guard bit.
example : ∃ ticks finalLeft finalRight,
    ticks ≤ 56 ∧ finalLeft.length = 0 ∧ finalRight.length = 0 ∧
    CallingConvention.Runs (StandardGcdMachine.widths 0) (fun _ => false)
      StandardGcdMachine.machine ticks StandardGcdMachine.entry (fun _ => 0)
      (StandardGcdMachine.frame [] [] ((fun _ => []), 2) 0)
      StandardGcdMachine.exit (fun _ => 0)
      (StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch 0) (Binary.data false)) ∧
    Binary.value finalRight = 0 ∧ Binary.value finalLeft = 0 := by
  simpa using StandardGcdMachine.runs [] [] rfl ((fun _ => []), 2) (by intro name; rfl) 0 (by decide)

-- The complete private loop handles arbitrary blank words and an arbitrary old flag.
example : ∃ ticks finalLeft finalRight,
    ticks ≤ 4316 ∧ finalLeft.length = 5 ∧ finalRight.length = 5 ∧
    CallingConvention.Runs (StandardGcdMachine.widths 5) (fun _ => false)
      StandardGcdMachine.machine ticks StandardGcdMachine.entry (fun _ => 0)
      (StandardGcdMachine.frame [true, false, true, true, false] [true, false, true, false, false]
        ((fun _ => List.replicate 5 0), 2) 0)
      StandardGcdMachine.exit (fun _ => 0)
      (StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch 5) (Binary.data false)) ∧
    Binary.value finalRight = 0 ∧ Binary.value finalLeft = 1 := by
  simpa [Binary.value] using StandardGcdMachine.runs [true, false, true, true, false]
    [true, false, true, false, false] rfl ((fun _ => List.replicate 5 0), 2)
    (by intro name; rfl) 0 (by decide)

-- The public machine starts with blank scratch and a separate blank result.
example :
    let left := [true, false, true, true, false]
    let right := [true, false, true, false, false]
    let contents : Fin 12 → List Binary.Symbol := fun name =>
      List.replicate (StandardGcd.widths 5 name) 0
    let initial : MultiTape.Tapes StandardGcd.Alphabet := fun name =>
      if name = 9 then CallingConvention.buffer (Binary.word left)
      else if name = 10 then CallingConvention.buffer (Binary.word right)
      else CallingConvention.buffer (contents name)
    ∃ ticks finalLeft finalRight final,
      ticks ≤ 4355 ∧ finalLeft.length = 5 ∧ finalRight.length = 5 ∧
      CallingConvention.Runs (StandardGcd.widths 5) StandardGcd.readOnly StandardGcd.machine
        ticks StandardGcd.entry (fun _ => 0) initial StandardGcd.exit (fun _ => 0) final ∧
      Binary.value finalLeft = 1 ∧
      (∀ name : Fin 9, final (StandardGcd.kernelWiring name) =
        StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch 5)
          (Binary.data false) name) ∧
      final 11 = CallingConvention.buffer (Binary.word finalLeft) := by
  let contents : Fin 12 → List Binary.Symbol := fun name =>
    List.replicate (StandardGcd.widths 5 name) 0
  let initial : MultiTape.Tapes StandardGcd.Alphabet := fun name =>
    if name = 9 then CallingConvention.buffer (Binary.word [true, false, true, true, false])
    else if name = 10 then CallingConvention.buffer (Binary.word [true, false, true, false, false])
    else CallingConvention.buffer (contents name)
  have trace := StandardGcd.runs [true, false, true, true, false]
    [true, false, true, false, false] rfl (by decide) initial contents
    (by simp [initial]) (by simp [initial])
    (by
      intro name writable
      have excluded : name ≠ 9 ∧ name ≠ 10 := by
        simpa [StandardGcd.readOnly] using writable
      simp [initial, excluded.1, excluded.2])
    (by intro name writable; exact List.length_replicate)
  simpa [initial, contents, Binary.value] using trace

-- Zero-width operands also work through both input copies and result extraction.
example : ∃ ticks finalLeft finalRight final,
    ticks ≤ 65 ∧ finalLeft.length = 0 ∧ finalRight.length = 0 ∧
    CallingConvention.Runs (StandardGcd.widths 0) StandardGcd.readOnly StandardGcd.machine
      ticks StandardGcd.entry (fun _ => 0)
      (fun name => CallingConvention.buffer (List.replicate (StandardGcd.widths 0 name) 0))
      StandardGcd.exit (fun _ => 0) final ∧
    Binary.value finalLeft = 0 ∧
    (∀ name : Fin 9, final (StandardGcd.kernelWiring name) =
      StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch 0)
        (Binary.data false) name) ∧
    final 11 = CallingConvention.buffer (Binary.word finalLeft) := by
  simpa [Binary.value] using StandardGcd.runs [] [] rfl (by decide)
    (fun name => CallingConvention.buffer (List.replicate (StandardGcd.widths 0 name) 0))
    (fun name => List.replicate (StandardGcd.widths 0 name) 0) rfl rfl
    (by intro name writable; rfl) (by intro name writable; exact List.length_replicate)

-- A single finite controller handles every runtime width.
example : Fintype StandardGcd.State := inferInstance

end Polytime2.Examples.Gcd
