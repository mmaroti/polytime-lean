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

import Polytime2.Binary

/-! # Binary ripple scans with finite carry or borrow memory

A fixed digit rule and memory rule define the mathematical ripple operation.
The standard controllers reuse this fold and its length theorem.
-/

namespace Polytime2.BinaryRipple

open MultiTape
open Binary (Symbol data word)

abbrev Alphabet := fun _ : Fin 3 => Symbol
abbrev State := Sum Bool (Fin 2)

variable (digit carry : Bool → Bool → Bool → Bool)

def ripple (digit carry : Bool → Bool → Bool → Bool) : Bool → List Bool → List Bool → List Bool × Bool
  | previous, left :: ls, right :: rs =>
    let rest := ripple digit carry (carry left right previous) ls rs
    (digit left right previous :: rest.1, rest.2)
  | previous, _, _ => ([], previous)

def output (left right : List Bool) : List Bool :=
  (ripple digit carry false left right).1 ++ [(ripple digit carry false left right).2]

@[simp] theorem ripple_length (previous : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    (ripple digit carry previous left right).1.length = left.length := by
  induction left generalizing previous right with
  | nil => simp [ripple]
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest => simp [ripple, hypothesis _ rest (by simpa using sameLength)]

def frame (leftFirst rightFirst leftSecond rightSecond leftOutput rightOutput : List Symbol) :
    Tapes Alphabet := fun name =>
  if name = 0 then Turing.Tape.mk' (Turing.ListBlank.mk leftFirst) (Turing.ListBlank.mk rightFirst)
  else if name = 1 then Turing.Tape.mk' (Turing.ListBlank.mk leftSecond) (Turing.ListBlank.mk rightSecond)
  else Turing.Tape.mk' (Turing.ListBlank.mk leftOutput) (Turing.ListBlank.mk rightOutput)

end Polytime2.BinaryRipple
