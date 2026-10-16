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
import Polytime2.Wiring
import Polytime2.BinaryAddition

/-! # Arithmetic with arbitrary preserved caller tapes

An addition routine owns three tapes in a larger collection. Its caller may
retain arbitrary contents and head positions on every other tape.
-/

namespace Polytime2.Examples.Context

open MultiTape
open Binary (word value)
open BinaryAddition (rippleFrame)

example (wiring : Fin 3 ↪ Fin 4) (left right : List Bool)
    (sameLength : right.length = left.length) (old : List Binary.Symbol)
    (oldLength : old.length = left.length) (oldCarry : Binary.Symbol)
    (caller : Tapes (CallingConvention.Alphabet (Fin 4))) (callerWidth : Fin 4 → ℕ) :
    let widths := install wiring (StandardBinaryRipple.width left.length) callerWidth
    let readonly := install wiring StandardBinaryRipple.readOnly (fun _ => true)
    let initial := install wiring
      (rippleFrame [0] (word left ++ [0]) [0] (word right ++ [0]) [0] (old ++ [oldCarry])) caller
    let final := install wiring
      (rippleFrame [0] (word left ++ [0]) [0] (word right ++ [0]) [0]
        (word (BinaryAddition.add left right))) caller
    CallingConvention.Runs widths readonly (MultiTape.wire wiring BinaryAddition.rippleMachine)
      (2 * left.length + 2) (.inl false) (fun _ => 0) initial (.inr 1) (fun _ => 0) final ∧
    value (BinaryAddition.add left right) = value left + value right ∧
    ∀ name, name ∉ Set.range wiring → final name = caller name := by
  dsimp only
  have trace := (BinaryAddition.runs left right sameLength old oldLength oldCarry).wire
    wiring (install wiring (StandardBinaryRipple.width left.length) callerWidth)
    (install wiring StandardBinaryRipple.readOnly (fun _ => true))
    (by intro name; simp) (by intro name premise; simpa using premise) caller (fun _ => 0)
  have positions : install wiring (fun _ : Fin 3 => (0 : ℤ))
      (fun _ : Fin 4 => (0 : ℤ)) = fun _ => 0 :=
    install_self wiring (fun _ : Fin 4 => (0 : ℤ))
  rw [positions] at trace
  exact ⟨trace, BinaryAddition.add_value left right sameLength,
    fun name outside => install_outside _ _ _ name outside⟩

end Polytime2.Examples.Context
