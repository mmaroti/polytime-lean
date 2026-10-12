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
import Polytime2.BinaryRemainder
import Polytime2.GcdMachine
import Polytime2.GcdExternal

/-! # Gcd boundary cases and bit-length progress

These checks exercise mathematical gcd, binary remainder, and complete external
input preparation and computation, including zero operands.
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

#guard Binary.value (BinaryRemainder.finish [true, false, true, false, false]
  [true, false, true, true, false].reverse (List.replicate 5 false)) = 3
#guard Binary.value (BinaryRemainder.finish [true, true, false, false]
  [false, true, true, false].reverse (List.replicate 4 false)) = 0
#guard Binary.value (BinaryRemainder.finish [true] [] [false]) = 0

-- The same fixed controller realizes 13 % 5 in a five-digit workspace.
example : ∃ ticks, ticks ≤ 233 ∧ MultiTape.Steps BinaryRemainder.machine ticks
    (BinaryRemainder.entry, BinaryRemainder.frame [3]
      (Binary.word [true, false, true, true, false] ++ [0])
      [true, false, true, false, false] (List.replicate 5 false))
    (BinaryRemainder.exit, BinaryRemainder.frame [3]
      (Binary.word [true, false, true, true, false] ++ [0])
      [true, false, true, false, false]
      (BinaryRemainder.finish [true, false, true, false, false]
        [true, false, true, true, false].reverse (List.replicate 5 false))) := by
  simpa using BinaryRemainder.steps [true, false, true, true, false]
    [true, false, true, false, false] (List.replicate 5 false)
    (by decide) (by decide) (by decide)

-- gcd(0,0) stops without calling the positive-divisor remainder routine.
-- Scratch and the previous flag need not start at zero.
example : ∃ ticks final, MultiTape.Steps GcdMachine.machine ticks
    (GcdMachine.entry, GcdMachine.frame [false] [false] [true] true)
    (GcdMachine.exit, final) ∧
    BinaryOutput.representation 0 (MvPolynomial.X () + 1) (fun _ => 0) 0 final := by
  obtain ⟨_, _, runs⟩ := GcdMachine.contract
  obtain ⟨ticks, final, _, trace, output⟩ := runs (fun _ => 0) (0, 0)
    (GcdMachine.frame [false] [false] [true] true) (by decide)
    ⟨[false], [false], [true], true, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨ticks, final, trace, output⟩

-- The internal machine computes gcd(13,5) in a common five-digit workspace.
example : ∃ ticks final, MultiTape.Steps GcdMachine.machine ticks
    (GcdMachine.entry, GcdMachine.frame [true, false, true, true, false]
      [true, false, true, false, false] (List.replicate 5 true) false)
    (GcdMachine.exit, final) ∧
    BinaryOutput.representation 0 (MvPolynomial.X () + 1) (fun _ => 4) 1 final := by
  obtain ⟨_, _, runs⟩ := GcdMachine.contract
  obtain ⟨ticks, final, _, trace, output⟩ := runs (fun _ => 4) (13, 5)
    (GcdMachine.frame [true, false, true, true, false]
      [true, false, true, false, false] (List.replicate 5 true) false) (by decide)
    ⟨[true, false, true, true, false], [true, false, true, false, false],
      List.replicate 5 true, false, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨ticks, final, trace, output⟩

#guard GcdInput.inputWord ([false], [false]) = [2, 3, 1, 1, 0]
#guard GcdExternal.compute ([false], [false]) = 0
#guard GcdExternal.compute ([false, false, false, false, false, false, false],
  [true, false, true, false, false, true, false]) = 37
#guard GcdExternal.compute ([false, false, false, false, true, true, false],
  [false, true, false, false, true, false, false]) = 6
example : GcdExternal.hypothesis (fun _ => 0) ([false], [false]) := by
  unfold GcdExternal.hypothesis GcdInput.hypothesis
  decide

-- The external convention supplies no initialized working tape.
example (input : GcdInput.Input) (name : Fin 6) (working : name ≠ 4) :
    GcdInput.preparedAt input 0 name = GcdInput.blank := by
  fin_cases name <;> simp_all [GcdInput.preparedAt]

-- One finite controller handles every runtime width.
example : Fintype GcdExternal.State := inferInstance

-- The complete external multi-tape machine handles the smallest zero input.
example : ∃ ticks final, MultiTape.Steps GcdExternal.machine ticks
    (GcdExternal.entry, BinaryOutput.initial 4 (GcdInput.inputWord ([false], [false])))
    (GcdExternal.exit, final) ∧
    BinaryOutput.representation 0 GcdExternal.outputCapacity (fun _ => 0) 0 final := by
  obtain ⟨_, _, runs⟩ := GcdExternal.contract
  obtain ⟨ticks, final, _, trace, output⟩ := runs (fun _ => 0) ([false], [false])
    (BinaryOutput.initial 4 (GcdInput.inputWord ([false], [false])))
    (by unfold GcdExternal.hypothesis GcdInput.hypothesis; decide) rfl
  exact ⟨ticks, final, trace, output⟩

-- Preparation, scratch initialization, and gcd compute gcd(13,5) together.
example : ∃ ticks final, MultiTape.Steps GcdExternal.machine ticks
    (GcdExternal.entry, BinaryOutput.initial 4
      (GcdInput.inputWord ([true, false, true, true, false], [true, false, true, false, false])))
    (GcdExternal.exit, final) ∧
    BinaryOutput.representation 0 GcdExternal.outputCapacity (fun _ => 4) 1 final := by
  obtain ⟨_, _, runs⟩ := GcdExternal.contract
  obtain ⟨ticks, final, _, trace, output⟩ := runs (fun _ => 4)
    ([true, false, true, true, false], [true, false, true, false, false])
    (BinaryOutput.initial 4
      (GcdInput.inputWord ([true, false, true, true, false], [true, false, true, false, false])))
    (by unfold GcdExternal.hypothesis GcdInput.hypothesis; decide) rfl
  exact ⟨ticks, final, trace, output⟩

end Polytime2.Examples.Gcd
