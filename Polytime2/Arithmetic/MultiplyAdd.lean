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

import Polytime2.Arithmetic.BinaryAddition
import Polytime2.Arithmetic.BinaryMultiplication

/-! # A product followed by a sum in one binary workspace

Matrix addressing uses `factor * multiplier + addend`. Each operand is immutable;
a private product links the calls and all results have fixed binary capacity.
-/

namespace Polytime2.MultiplyAdd

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 9)
abbrev State := Sum StandardBinaryMultiplication.State StandardBinaryArithmetic.State

/-- Product, factor, shifted word, next word, multiplication flag, multiplier,
addend, final result, and addition flag. -/
def frame (factor multiplier addend : List Bool)
    (product shifted next result : List Symbol) (multiplyFlag addFlag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer product else if name = 1 then buffer (word factor)
  else if name = 2 then buffer shifted else if name = 3 then buffer next
  else if name = 4 then buffer [multiplyFlag] else if name = 5 then buffer (word multiplier)
  else if name = 6 then buffer (word addend) else if name = 7 then buffer result else buffer [addFlag]

def widths (digits multiplierDigits : ℕ) (name : Fin 9) : ℕ :=
  if name = 4 ∨ name = 8 then 1 else if name = 5 then multiplierDigits else digits

def readOnly (name : Fin 9) : Bool := decide (name = 1 ∨ name = 5 ∨ name = 6)

def multiplicationWiring : Fin 6 ↪ Fin 9 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 9 => name.val) equal)⟩

def additionWiring : Fin 4 ↪ Fin 9 :=
  ⟨(fun name => match name.val with | 0 => 0 | 1 => 6 | 2 => 7 | _ => 8), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem multiplicationWiring_apply (name : Fin 6) :
    multiplicationWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem additionWiring_apply (name : Fin 4) :
    additionWiring name = (match name.val with | 0 => 0 | 1 => 6 | 2 => 7 | _ => 8) := rfl

noncomputable def first : Machine Alphabet StandardBinaryMultiplication.State :=
  MultiTape.wire multiplicationWiring StandardBinaryMultiplication.machine
noncomputable def second : Machine Alphabet StandardBinaryArithmetic.State :=
  MultiTape.wire additionWiring (StandardBinaryArithmetic.machine BinaryAddition.digit BinaryAddition.carry)
noncomputable def machine : Machine Alphabet State := MultiTape.sequence first second (.inl false)

def entry : State := .inl StandardBinaryMultiplication.entry
def exit : State := .inr (.inr (false, true))

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, second, MultiTape.sequence, MultiTape.wire, StandardBinaryArithmetic.machine]

def product (factor multiplier : List Bool) : List Bool :=
  StandardBinaryMultiplication.finish factor multiplier.reverse (List.replicate factor.length false)

def result (factor multiplier addend : List Bool) : List Bool :=
  BinaryAddition.lowSum (product factor multiplier) addend

theorem product_length (factor multiplier : List Bool) :
    (product factor multiplier).length = factor.length :=
  StandardBinaryMultiplication.finish_length factor multiplier.reverse
    (List.replicate factor.length false) List.length_replicate

theorem result_length (factor multiplier addend : List Bool)
    (addendLength : addend.length = factor.length) :
    (result factor multiplier addend).length = factor.length := by
  have length := product_length factor multiplier
  exact (BinaryAddition.lowSum_length _ _ (addendLength.trans length.symm)).trans length

/-- The single capacity hypothesis is the ordinary mathematical address bound. -/
theorem result_value (factor multiplier addend : List Bool)
    (addendLength : addend.length = factor.length)
    (capacity : value factor * value multiplier + value addend < 2 ^ factor.length) :
    value (result factor multiplier addend) = value factor * value multiplier + value addend := by
  have length := product_length factor multiplier
  have productValue : value (product factor multiplier) = value factor * value multiplier :=
    StandardBinaryMultiplication.result_value multiplier factor (by omega)
  exact (BinaryAddition.lowSum_value _ _ (addendLength.trans length.symm)
    (by simpa [length, productValue] using capacity)).1.trans (by rw [productValue])

/-- All writable regions may initially contain blanks or invalid symbols.
The product and arithmetic scratch are valid on return, and every head is restored. -/
theorem runs (factor multiplier addend : List Bool) (addendLength : addend.length = factor.length)
    (oldProduct oldShifted oldNext oldResult : List Symbol)
    (productLength : oldProduct.length = factor.length) (shiftedLength : oldShifted.length = factor.length)
    (nextLength : oldNext.length = factor.length) (resultLength : oldResult.length = factor.length)
    (multiplyFlag addFlag : Symbol)
    (capacity : value factor * value multiplier + value addend < 2 ^ factor.length) :
    Runs (widths factor.length multiplier.length) readOnly machine
      (multiplier.length * (6 * factor.length + 14) + 8 * factor.length + 17)
      entry (fun _ => 0)
      (frame factor multiplier addend oldProduct oldShifted oldNext oldResult multiplyFlag addFlag)
      exit (fun _ => 0)
      (frame factor multiplier addend (word (product factor multiplier))
        (word (List.replicate factor.length false)) (word (List.replicate factor.length false))
        (word (result factor multiplier addend)) (data false) (data false)) := by
  let productBits := product factor multiplier
  have length : productBits.length = factor.length :=
    product_length factor multiplier
  have productValue : value productBits = value factor * value multiplier :=
    StandardBinaryMultiplication.result_value multiplier factor (by omega)
  have noCarry := (BinaryAddition.lowSum_value productBits addend (addendLength.trans length.symm)
    (by simpa [length, productValue] using capacity)).2
  have multiplied := (StandardBinaryMultiplication.runs multiplier factor oldProduct oldShifted oldNext
    productLength shiftedLength nextLength multiplyFlag).wire_of_eq multiplicationWiring
    (widths factor.length multiplier.length) readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp_all [readOnly, StandardBinaryMultiplication.readOnly])
    (frame factor multiplier addend oldProduct oldShifted oldNext oldResult multiplyFlag addFlag)
    (frame factor multiplier addend (word productBits) (word (List.replicate factor.length false))
      (word (List.replicate factor.length false)) oldResult (data false) addFlag)
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨0, rfl⟩)
      · exact False.elim (outside ⟨1, rfl⟩)
      · exact False.elim (outside ⟨2, rfl⟩)
      · exact False.elim (outside ⟨3, rfl⟩)
      · exact False.elim (outside ⟨4, rfl⟩)
      · exact False.elim (outside ⟨5, rfl⟩)
      · rfl
      · rfl
      · rfl)
  have added := (StandardBinaryArithmetic.runs BinaryAddition.digit BinaryAddition.carry false productBits addend
    (addendLength.trans length.symm) oldResult (resultLength.trans length.symm) addFlag).wire_of_eq additionWiring
    (widths factor.length multiplier.length) readOnly
    (by intro name; fin_cases name <;> simpa [widths, StandardBinaryArithmetic.width] using length.symm)
    (by intro name premise; fin_cases name <;> simp_all [readOnly, StandardBinaryArithmetic.readOnly])
    (frame factor multiplier addend (word productBits) (word (List.replicate factor.length false))
      (word (List.replicate factor.length false)) oldResult (data false) addFlag)
    (frame factor multiplier addend (word productBits) (word (List.replicate factor.length false))
      (word (List.replicate factor.length false)) (word (BinaryAddition.lowSum productBits addend))
      (data false) (data (BinaryAddition.ripple false productBits addend).2))
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by
      intro name outside
      fin_cases name
      · exact False.elim (outside ⟨0, rfl⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (outside ⟨1, rfl⟩)
      · exact False.elim (outside ⟨2, rfl⟩)
      · exact False.elim (outside ⟨3, rfl⟩))
  rw [noCarry, length] at added
  have complete := multiplied.sequence second (.inl false)
    (by intro symbols; simp [MultiTape.wire, StandardBinaryMultiplication.machine,
      StandardBinaryMultiplication.exit, MultiTape.sequence, StandardBinaryMultiplication.cleanup,
      StandardBinaryMultiplication.cleanupExit, StandardTapeCommands.setBoolean,
      StandardTapeCommands.booleanMachine]) added
  convert complete using 1 <;> first | rfl | ring

end Polytime2.MultiplyAdd
