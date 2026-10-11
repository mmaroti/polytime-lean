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

import Polytime1.Frame
import Polytime1.Integer

/-! # Size-driven frame preparation and integer storage examples -/

namespace Polytime1.Examples.FramePreparation

abbrev context : SizeContext := ⟨Fin 2, inferInstance⟩
def ordering : context.Parameter ≃ Fin 2 := Equiv.refl _
def sizes (rows columns : ℕ) : SizeAssignment context := ![rows, columns]

def rowCount : SizeExpression context := .parameter 0
def columnCount : SizeExpression context := .parameter 1

def input : DomainExpression context := BoolTuple.domain rowCount

def matrix : DomainExpression context :=
  .power (.power (.fixed (FixedPresentation.fin 3)) columnCount) rowCount

-- The same mathematical constructor now has executable width calculation.
#guard matrix.bitWidth (sizes 2 3) = 12
#guard (DomainExpression.sum [input, matrix]).bitWidth (sizes 2 3) = 13
#guard (rowCount ^ 2 + rowCount * columnCount).eval (sizes 2 3) = 10

-- Header [2,3], a two-bit input, and a twelve-cell scratch matrix.
#guard (Frame.prepare ordering input [matrix]
    (Frame.serialize ordering input (sizes 2 3) (BitVec.ofNat (input.bitWidth (sizes 2 3)) 1))).map
      (fun prepared => (prepared.1 0, prepared.1 1, prepared.2.length)) = some (2, 3, 26)

-- The header is required and retained even for empty input and scratch slots.
#guard (Frame.prepare ordering input [matrix]
    (Frame.serialize ordering input (sizes 0 3) (BitVec.ofNat (input.bitWidth (sizes 0 3)) 0))).map
      (fun prepared => (prepared.1 0, prepared.1 1, prepared.2.length)) = some (0, 3, 10)

-- Missing unary terminators and payloads of the wrong width are rejected.
#guard Frame.parseHeader 2 [true, false, true] = none
#guard (Frame.prepare ordering input [] (Frame.header [2, 3] ++ [true])).isNone

/-- All four constructors use the same preparation contract. -/
example (scratch : List (DomainExpression context)) (rows columns : ℕ)
    (bits : BitVec (input.bitWidth (sizes rows columns))) :
    Frame.prepare ordering input scratch (Frame.serialize ordering input (sizes rows columns) bits) =
      some (sizes rows columns,
        Frame.preparedCells ordering scratch (sizes rows columns) (List.ofFn (BoolTuple.fromBits bits))) :=
  Frame.prepare_serialized ordering input scratch (sizes rows columns) bits

noncomputable section IntegerDomains

def unsigned : EncodedDomain context := BinaryNat.domain columnCount
def signed : EncodedDomain context := BinaryInt.domain columnCount

example : unsigned.expression.bitWidth (sizes 0 80) = 80 := by simp [unsigned, columnCount, sizes]
example : signed.expression.bitWidth (sizes 0 80) = 81 := by simp [signed, columnCount, sizes]

/-- Matrix dimensions and entry bit length remain independent size parameters. -/
abbrev integerContext : SizeContext := ⟨Fin 3, inferInstance⟩
def integerSizes (rows columns bits : ℕ) : SizeAssignment integerContext := ![rows, columns, bits]

def integerMatrix : DomainExpression integerContext :=
  .power (.power (BinaryInt.domain (SizeExpression.parameter (ctx := integerContext) 2)).expression
    (SizeExpression.parameter 1)) (SizeExpression.parameter 0)

example (rows columns bits : ℕ) :
    integerMatrix.bitWidth (integerSizes rows columns bits) = rows * columns * (bits + 1) := by
  simp [integerMatrix, integerSizes, Nat.mul_assoc]

example (sizes : SizeAssignment context) (value : signed.Carrier sizes) :
    (signed.codec sizes).decode ((signed.codec sizes).encode value) = some value :=
  (signed.codec sizes).decode_encode value

end IntegerDomains

-- The signed extremes and zero have unique binary representations.
#guard (BinaryInt.toBits (⟨-256, by decide⟩ : BinaryInt.Value 8)).toInt = -256
#guard (BinaryInt.toBits (⟨255, by decide⟩ : BinaryInt.Value 8)).toInt = 255
#guard (BinaryInt.toBits (⟨0, by decide⟩ : BinaryInt.Value 0)).toNat = 0
#guard (BinaryInt.toBits (⟨-1, by decide⟩ : BinaryInt.Value 0)).toNat = 1
#guard (BinaryInt.toBits (⟨-(2 : ℤ)^80, by norm_num⟩ : BinaryInt.Value 80)).toInt = -(2 : ℤ)^80

-- Exact arithmetic expands bit capacities rather than truncating results.
#guard (BinaryInt.add (⟨255, by decide⟩ : BinaryInt.Value 8) ⟨255, by decide⟩).val = 510
#guard (BinaryInt.sub (⟨-256, by decide⟩ : BinaryInt.Value 8) ⟨255, by decide⟩).val = -511
#guard (BinaryInt.mul (⟨-256, by decide⟩ : BinaryInt.Value 8) ⟨-256, by decide⟩).val = 65536
#guard (BinaryInt.div (⟨-256, by decide⟩ : BinaryInt.Value 8) ⟨-1, by decide⟩ (by decide)).val = 256
#guard (BinaryInt.div (⟨-7, by decide⟩ : BinaryInt.Value 8) ⟨-3, by decide⟩ (by decide)).val = 3
#guard (BinaryInt.rem (⟨-7, by decide⟩ : BinaryInt.Value 8) ⟨-3, by decide⟩ (by decide)).val = 2
#guard (BinaryInt.gcd (⟨-12, by decide⟩ : BinaryInt.Value 8) ⟨18, by decide⟩).val = 6
#guard (BinaryInt.gcd (⟨0, by decide⟩ : BinaryInt.Value 0) ⟨0, by decide⟩).val = 0

end Polytime1.Examples.FramePreparation
