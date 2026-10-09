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

import Polytime.InPlaceTableMachine
import Polytime.FiniteDispatchMachine
import Polytime.Examples.Matrices

/-! # Fixed tables for finite-field arithmetic

The generic table realization applies to addition, multiplication, negation,
and inversion with the canonical scalar codecs. The table is fixed before
any matrix dimensions or runtime scalar values are supplied.
-/

namespace Polytime.Examples.FiniteTables

open TupleMachine (Symbol data word)

-- carrierLevel: the fixed finite scalar carrier.
universe carrierLevel

section ScalarOperations

variable (presentation : FixedPresentation.{carrierLevel}) [Field presentation.Carrier]

/-- Both binary field operations use the same canonical product input codec. -/
example (operation : presentation.Carrier → presentation.Carrier → presentation.Carrier)
    (first second : presentation.Carrier) (tail : List Symbol) :
    Tape.Steps (FiniteTableMachine.machine (FiniteTableMachine.encodedTable
      (presentation.codec.product presentation.codec) presentation.codec
      (fun pair => operation pair.1 pair.2)))
      (2 * (presentation.bitWidth + presentation.bitWidth) + 2 * presentation.bitWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) []
        (word (List.ofFn (BoolTuple.fromBits
          ((presentation.codec.product presentation.codec).encode (first, second)))) ++ tail))
      (Tape.configuration .halt []
        (word (List.ofFn (BoolTuple.fromBits (presentation.codec.encode (operation first second)))) ++
          word (List.ofFn (BoolTuple.fromBits
            ((presentation.codec.product presentation.codec).encode (first, second)))) ++ tail)) :=
  FiniteTableMachine.realizes_operation (presentation.codec.product presentation.codec)
    presentation.codec (fun pair => operation pair.1 pair.2) (first, second) tail

/-- Negation and inversion use this unary instance of the same realization theorem. -/
example (operation : presentation.Carrier → presentation.Carrier)
    (value : presentation.Carrier) (tail : List Symbol) :
    Tape.Steps (FiniteTableMachine.machine (FiniteTableMachine.encodedTable
      presentation.codec presentation.codec operation)) (4 * presentation.bitWidth + 3)
      (Tape.configuration (.read 0 (fun _ => false)) []
        (word (List.ofFn (BoolTuple.fromBits (presentation.codec.encode value))) ++ tail))
      (Tape.configuration .halt []
        (word (List.ofFn (BoolTuple.fromBits (presentation.codec.encode (operation value)))) ++
          word (List.ofFn (BoolTuple.fromBits (presentation.codec.encode value))) ++ tail)) := by
  convert FiniteTableMachine.realizes_operation presentation.codec presentation.codec operation value tail using 1
  omega

/-- Row scaling keeps the runtime coefficient and overwrites the adjacent entry.
Only the operation table, not either scalar value, is fixed in the controller. -/
theorem realizes_scaled_pair (coefficient entry : presentation.Carrier) (left tail : List Symbol) :
    let codec := presentation.codec.product presentation.codec
    Tape.Steps (InPlaceTableMachine.machine (FiniteTableMachine.encodedTable codec codec
      (fun pair => (pair.1, pair.1 * pair.2))))
      (3 * (presentation.bitWidth + presentation.bitWidth) + 2)
      (Tape.configuration (.read 0 (fun _ => false)) left
        (word (List.ofFn (BoolTuple.fromBits (codec.encode (coefficient, entry)))) ++ tail))
      (Tape.configuration .halt left
        (word (List.ofFn (BoolTuple.fromBits (codec.encode (coefficient, coefficient * entry)))) ++ tail)) :=
  InPlaceTableMachine.realizes_operation (presentation.codec.product presentation.codec)
    (fun pair => (pair.1, pair.1 * pair.2)) (coefficient, entry) left tail

end ScalarOperations

section ExecutableChecks

/-- Project a nonadjacent input bit, exercising accumulation and reverse emission. -/
def projection : (Fin 3 → Bool) → (Fin 2 → Bool) := fun input position =>
  if position = 0 then input 2 else input 0 && !input 1

def execute {inputWidth outputWidth : ℕ}
    (table : (Fin inputWidth → Bool) → (Fin outputWidth → Bool))
    (bits : BitVec inputWidth) (tail : List Symbol) : Option (List Symbol) :=
  (Tape.run (FiniteTableMachine.machine table) (2 * inputWidth + 2 * outputWidth + 3)
    (Tape.configuration (.read 0 (fun _ => false)) []
      (word (List.ofFn (BoolTuple.fromBits bits)) ++ tail))).map fun final =>
    (List.range (outputWidth + inputWidth + tail.length)).map final.Tape.right₀.nth

#guard execute projection (BitVec.ofNat 3 5) [7] = some [2, 2, 2, 1, 2, 7]
#guard execute projection (BitVec.ofNat 3 2) [1, 7] = some [1, 1, 1, 2, 1, 1, 7]
#guard execute (inputWidth := 0) (outputWidth := 2) (fun _ _ => true) 0 [7] = some [2, 2, 7]
#guard execute (inputWidth := 2) (outputWidth := 0) (fun _ index => Fin.elim0 index) 2 [7] = some [1, 2, 7]
#guard execute (inputWidth := 0) (outputWidth := 0) (fun _ index => Fin.elim0 index) 0 [] = some []

/-- This is the fixed-field canonical codec, with its width normalized to three. -/
def scalarCodec : BitCodec (ZMod 5) 3 :=
  ((BitCodec.fin 5).transport (ZMod.finEquiv 5).toEquiv).cast (by decide)

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- These executions exercise actual canonical field operation tables.
#guard execute (FiniteTableMachine.encodedTable (scalarCodec.product scalarCodec) scalarCodec
    (fun pair => pair.1 + pair.2)) ((scalarCodec.product scalarCodec).encode (2, 4)) [7] =
  some [2, 1, 1, 1, 2, 1, 1, 1, 2, 7]
#guard execute (FiniteTableMachine.encodedTable (scalarCodec.product scalarCodec) scalarCodec
    (fun pair => pair.1 * pair.2)) ((scalarCodec.product scalarCodec).encode (2, 4)) [7] =
  some [2, 2, 1, 1, 2, 1, 1, 1, 2, 7]
#guard execute (FiniteTableMachine.encodedTable scalarCodec scalarCodec Neg.neg)
    (scalarCodec.encode 2) [7] = some [2, 2, 1, 1, 2, 1, 7]
#guard execute (FiniteTableMachine.encodedTable scalarCodec scalarCodec Inv.inv)
    (scalarCodec.encode 3) [7] = some [1, 2, 1, 2, 2, 1, 7]

/-- Observe both neighboring regions after an operation in the existing slot. -/
def executeInPlace {width : ℕ} (table : (Fin width → Bool) → (Fin width → Bool))
    (bits : BitVec width) (left tail : List Symbol) : Option (List Symbol × List Symbol) :=
  (Tape.run (InPlaceTableMachine.machine table) (3 * width + 2)
    (Tape.configuration (.read 0 (fun _ => false)) left
      (word (List.ofFn (BoolTuple.fromBits bits)) ++ tail))).map fun final =>
    ((List.range left.length).map final.Tape.left.nth,
      (List.range (width + tail.length)).map final.Tape.right₀.nth)

#guard executeInPlace (FiniteTableMachine.encodedTable scalarCodec scalarCodec Neg.neg)
    (scalarCodec.encode 2) [6, 7] [3, 4, 7] = some ([6, 7], [2, 2, 1, 3, 4, 7])
#guard executeInPlace (FiniteTableMachine.encodedTable scalarCodec scalarCodec Inv.inv)
    (scalarCodec.encode 3) [1, 2, 1] [3, 4, 7] = some ([1, 2, 1], [1, 2, 1, 3, 4, 7])
#guard executeInPlace (FiniteTableMachine.encodedTable scalarCodec scalarCodec
    (fun value => (2 : ZMod 5) * value)) (scalarCodec.encode 4) [7] [4] =
  some ([7], [2, 2, 1, 4])
#guard executeInPlace (width := 0) (fun _ index => Fin.elim0 index) 0 [6, 7] [3, 4] =
  some ([6, 7], [3, 4])
#guard executeInPlace (FiniteTableMachine.encodedTable (scalarCodec.product scalarCodec)
    (scalarCodec.product scalarCodec) (fun pair => (pair.1, pair.1 * pair.2)))
    ((scalarCodec.product scalarCodec).encode (2, 4)) [7] [3, 4] =
  some ([7], [1, 2, 1, 2, 2, 1, 3, 4])

-- A reused output slot may contain nonblank data; caller-owned regions survive.
#guard (Tape.run (FiniteTableMachine.machine projection) 13
    (Tape.configuration (.read 0 (fun _ => false)) ([6, 7] ++ [3, 4, 6])
      [2, 1, 2, 7, 1])).map (fun final =>
      ((List.range 3).map final.Tape.left.nth, (List.range 7).map final.Tape.right₀.nth)) =
  some ([3, 4, 6], [2, 2, 2, 1, 2, 7, 1])

/-- Consume a scalar into controller bits, observing restored blank storage. -/
def consumeScalar {width : ℕ} (bits : BitVec width) (tail : List Symbol) :
    Option (List Bool × List Symbol × List Symbol) :=
  (Tape.run (FiniteDispatchMachine.Read.machine width) (4 * width + 2)
    (Tape.configuration (0, (fun _ => false), 0) []
      (word (List.ofFn (BoolTuple.fromBits bits)) ++ tail))).map fun final =>
    (List.ofFn final.q.2.1, (List.range tail.length).map final.Tape.right₀.nth,
      (List.range 4).map final.Tape.left.nth)

#guard consumeScalar (BitVec.ofNat 3 5) [3, 4, 7] =
  some ([true, false, true], [3, 4, 7], List.replicate 4 0)
#guard consumeScalar (BitVec.ofNat 3 2) [1, 7] =
  some ([false, true, false], [1, 7], List.replicate 4 0)
#guard consumeScalar (BitVec.ofNat 0 0) [3, 4, 7] =
  some ([], [3, 4, 7], List.replicate 4 0)

/-- The runtime bits select a transition table in one fixed finite machine. -/
def selectedBranch (bits : Fin 3 → Bool) : Turing.TM0.Machine Symbol (Fin 2) := fun state _ =>
  if state = 0 then some (1, .write (data (bits 0 && !bits 2))) else none

def executeSelection (bits : BitVec 3) : Option (List Symbol × List Symbol) :=
  (Tape.run (FiniteDispatchMachine.machine selectedBranch (fun _ => 0)) 17
    (Tape.configuration (.inl (0, (fun _ => false), 0)) []
      (word (List.ofFn (BoolTuple.fromBits bits)) ++ [1, 7, 4]))).map fun final =>
    ((List.range 3).map final.Tape.right₀.nth, (List.range 4).map final.Tape.left.nth)

#guard executeSelection (BitVec.ofNat 3 1) = some ([2, 7, 4], List.replicate 4 0)
#guard executeSelection (BitVec.ofNat 3 5) = some ([1, 7, 4], List.replicate 4 0)
#guard executeSelection (BitVec.ofNat 3 0) = some ([1, 7, 4], List.replicate 4 0)

end ExecutableChecks
end Polytime.Examples.FiniteTables
