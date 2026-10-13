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

/-! # Addition followed by multiplication with immutable inputs

Three separate operand tapes produce `(left + right) * multiplier` on a new
tape. The intermediate sum and all arithmetic scratch have fixed regions.
All writable regions may start arbitrarily, and every head is restored.
-/

namespace Polytime2.AddMultiply

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 9)
abbrev State := Sum StandardBinaryArithmetic.State StandardBinaryMultiplication.State

/-- Product, sum, shifted word, next word, multiplication flag, multiplier,
left addend, right addend, and addition flag. -/
def frame (left right multiplier : List Bool) (product sum shifted next : List Symbol)
    (multiplyFlag addFlag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer product
  else if name = 1 then buffer sum
  else if name = 2 then buffer shifted
  else if name = 3 then buffer next
  else if name = 4 then buffer [multiplyFlag]
  else if name = 5 then buffer (word multiplier)
  else if name = 6 then buffer (word left)
  else if name = 7 then buffer (word right)
  else buffer [addFlag]

def widths (digits multiplierDigits : ℕ) (name : Fin 9) : ℕ :=
  if name = 4 ∨ name = 8 then 1 else if name = 5 then multiplierDigits else digits

def readOnly (name : Fin 9) : Bool := decide (name = 5 ∨ name = 6 ∨ name = 7)

def sum (left right : List Bool) : List Bool := (BinaryAddition.ripple false left right).1

theorem sum_length (left right : List Bool) (sameLength : right.length = left.length) :
    (sum left right).length = left.length := BinaryRipple.ripple_length _ _ _ _ _ sameLength

theorem sum_value (left right : List Bool) (sameLength : right.length = left.length)
    (capacity : value left + value right < 2 ^ left.length) :
    value (sum left right) = value left + value right ∧
      (BinaryAddition.ripple false left right).2 = false := by
  have equation := BinaryAddition.ripple_value false left right sameLength
  cases flag : (BinaryAddition.ripple false left right).2 with
  | false => simpa [sum, flag] using equation
  | true => simp only [flag, Bool.toNat_true, Nat.mul_one, Bool.toNat_false, Nat.add_zero] at equation; omega

def additionWiring : Fin 4 ↪ Fin 9 :=
  ⟨(fun name => match name.val with | 0 => 6 | 1 => 7 | 2 => 1 | _ => 8), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def multiplicationWiring : Fin 6 ↪ Fin 9 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 9 => name.val) equal)⟩

@[simp] theorem additionWiring_apply (name : Fin 4) :
    additionWiring name = (match name.val with | 0 => 6 | 1 => 7 | 2 => 1 | _ => 8) := rfl
@[simp] theorem multiplicationWiring_apply (name : Fin 6) :
    multiplicationWiring name = ⟨name.val, by omega⟩ := rfl

noncomputable def first : Machine Alphabet StandardBinaryArithmetic.State :=
  MultiTape.wire additionWiring (StandardBinaryArithmetic.machine BinaryAddition.digit BinaryAddition.carry)

noncomputable def second : Machine Alphabet StandardBinaryMultiplication.State :=
  MultiTape.wire multiplicationWiring StandardBinaryMultiplication.machine

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence first second StandardBinaryMultiplication.entry

def entry : State := .inl (.inl false)
def exit : State := .inr StandardBinaryMultiplication.exit

def product (left right multiplier : List Bool) (shifted next : List Symbol) (flag : Symbol) : List Bool :=
  (StandardBinaryMultiplication.finish (sum left right) multiplier.reverse
    (List.replicate (sum left right).length false, shifted, next, flag)).1

theorem product_length (left right multiplier : List Bool) (shifted next : List Symbol) (flag : Symbol)
    (sameLength : right.length = left.length) (shiftedLength : shifted.length = left.length)
    (nextLength : next.length = left.length) :
    (product left right multiplier shifted next flag).length = left.length := by
  have sumLength := sum_length left right sameLength
  exact (StandardBinaryMultiplication.finish_fits (sum left right) multiplier.reverse
    (List.replicate (sum left right).length false, shifted, next, flag)
    ⟨List.length_replicate, shiftedLength.trans sumLength.symm, nextLength.trans sumLength.symm⟩).1.trans sumLength

/-- The hypotheses expose exactly the capacities needed by both mathematical
operations; users do not need to calculate a transition bound. -/
theorem product_value (left right multiplier : List Bool) (shifted next : List Symbol) (flag : Symbol)
    (sameLength : right.length = left.length) (shiftedLength : shifted.length = left.length)
    (nextLength : next.length = left.length)
    (sumCapacity : value left + value right < 2 ^ left.length)
    (productCapacity : (value left + value right) * value multiplier < 2 ^ left.length) :
    value (product left right multiplier shifted next flag) = (value left + value right) * value multiplier := by
  have sumLength := sum_length left right sameLength
  have sumValue := (sum_value left right sameLength sumCapacity).1
  simpa only [product, sumValue] using StandardBinaryMultiplication.result_value multiplier (sum left right)
    shifted next flag (shiftedLength.trans sumLength.symm) (nextLength.trans sumLength.symm)
    (by simpa only [sumLength, sumValue] using productCapacity)

/-- Both calls share an intermediate tape; the original operands remain
immutable during every transition of the composed computation. -/
theorem runs (left right multiplier : List Bool) (sameLength : right.length = left.length)
    (oldProduct oldSum oldShifted oldNext : List Symbol)
    (productLength : oldProduct.length = left.length) (sumLength : oldSum.length = left.length)
    (shiftedLength : oldShifted.length = left.length) (nextLength : oldNext.length = left.length)
    (multiplyFlag addFlag : Symbol) (sumCapacity : value left + value right < 2 ^ left.length) :
    Runs (widths left.length multiplier.length) readOnly machine
      (multiplier.length * (6 * left.length + 14) + 8 * left.length + 17)
      entry (fun _ => 0) (frame left right multiplier oldProduct oldSum oldShifted oldNext multiplyFlag addFlag)
      exit (fun _ => 0) (frame left right multiplier
        (word (product left right multiplier oldShifted oldNext multiplyFlag)) (word (sum left right))
        (word (List.replicate left.length false)) (word (List.replicate left.length false))
        (data false) (data false)) := by
  have length := sum_length left right sameLength
  have noCarry := (sum_value left right sameLength sumCapacity).2
  have added := (StandardBinaryArithmetic.runs BinaryAddition.digit BinaryAddition.carry false left right
    sameLength oldSum sumLength addFlag).wire_of_eq
    additionWiring (widths left.length multiplier.length) readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> simp_all [readOnly, StandardBinaryArithmetic.readOnly])
    (frame left right multiplier oldProduct oldSum oldShifted oldNext multiplyFlag addFlag)
    (frame left right multiplier oldProduct (word (sum left right)) oldShifted oldNext multiplyFlag
      (data (BinaryAddition.ripple false left right).2))
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by intro name; fin_cases name <;> first | exact (buffer_padding _).symm | rfl)
    (by
      intro name outside
      fin_cases name
      · rfl
      · exact False.elim (outside ⟨2, rfl⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · exact False.elim (outside ⟨0, rfl⟩)
      · exact False.elim (outside ⟨1, rfl⟩)
      · exact False.elim (outside ⟨3, rfl⟩))
  rw [noCarry] at added
  have multiplied := (StandardBinaryMultiplication.runs multiplier (sum left right)
    oldProduct oldShifted oldNext (productLength.trans length.symm)
    (shiftedLength.trans length.symm) (nextLength.trans length.symm) multiplyFlag).wire_of_eq
    multiplicationWiring (widths left.length multiplier.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardBinaryMultiplication.widths, length])
    (by intro name premise; fin_cases name <;>
      simp_all [readOnly, StandardBinaryMultiplication.readOnly])
    (frame left right multiplier oldProduct (word (sum left right)) oldShifted oldNext multiplyFlag (data false))
    (frame left right multiplier (word (product left right multiplier oldShifted oldNext multiplyFlag))
      (word (sum left right)) (word (List.replicate (sum left right).length false))
      (word (List.replicate (sum left right).length false)) (data false) (data false))
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
  rw [length] at multiplied
  have complete := added.sequence second StandardBinaryMultiplication.entry
    (by intro symbols; simp [MultiTape.wire, StandardBinaryArithmetic.machine]) multiplied
  convert complete using 1 <;> first | rfl | ring


/-- Two sizes specify word capacity and the independent multiplier width. -/
def domains : Sum Bool (Fin 9) → EncodedDomain Bool
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 ∨ name = 8 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals (decide (name = 5))

def argumentReadOnly : Sum Bool (Fin 9) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 9 ↪ Sum Bool (Fin 9) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Bool ↪ Sum Bool (Fin 9) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Bool (Fin 9))) State :=
  MultiTape.wire dataTapes machine

/-- The ordinary output is the exact mathematical expression. All private
intermediate and scratch tapes also return valid encoded values. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm entry exit
    (fun assignment input =>
      (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val +
          (input ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment false)).val < 2 ^ assignment false ∧
      ((input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val +
          (input ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment false)).val) *
        (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val < 2 ^ assignment false)
    (fun assignment input output =>
      (output ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment false)).val =
        ((input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val +
          (input ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment false)).val) *
        (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val) := by
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithm, MultiTape.wire,
    machine, exit, MultiTape.sequence, second, StandardBinaryMultiplication.machine,
    StandardBinaryMultiplication.exit, StandardBinaryMultiplication.cleanup,
    StandardBinaryMultiplication.cleanupExit, StandardTapeCommands.setBoolean,
    StandardTapeCommands.booleanMachine]),
    MvPolynomial.X true * (6 * MvPolynomial.X false + 14) + 8 * MvPolynomial.X false + 17, ?_⟩
  intro assignment input initial valid represented sizes
  let left := List.ofFn (fun index : Fin (assignment false) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (assignment false) =>
    (BitVec.ofFin (input ⟨.inr 7, rfl⟩)).getLsbD index.val)
  let multiplier := List.ofFn (fun index : Fin (assignment true) =>
    (BitVec.ofFin (input ⟨.inr 5, rfl⟩)).getLsbD index.val)
  have leftLength : left.length = assignment false := List.length_ofFn
  have rightLength : right.length = assignment false := List.length_ofFn
  have multiplierLength : multiplier.length = assignment true := List.length_ofFn
  have leftValue : value left = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment false)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  have rightValue : value right = (input ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment false)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 7, rfl⟩))
  have multiplierValue : value multiplier = (input ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment true)).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 5, rfl⟩))
  obtain ⟨oldProduct, productLength, productEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldSum, oldSumLength, sumEq⟩ := represented.2 (.inr 1) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldNext, nextLength, nextEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨multiplyFlags, multiplyFlagLength, multiplyFlagEq⟩ := represented.2 (.inr 4) rfl
  obtain ⟨addFlags, addFlagLength, addFlagEq⟩ := represented.2 (.inr 8) rfl
  change multiplyFlags.length = 1 at multiplyFlagLength
  change addFlags.length = 1 at addFlagLength
  obtain ⟨multiplyFlag, rfl⟩ := List.length_eq_one_iff.mp multiplyFlagLength
  obtain ⟨addFlag, rfl⟩ := List.length_eq_one_iff.mp addFlagLength
  have leftEq : initial (.inr 6) = buffer (word left) := represented.1 (.inr 6) rfl
  have rightEq : initial (.inr 7) = buffer (word right) := represented.1 (.inr 7) rfl
  have multiplierEq : initial (.inr 5) = buffer (word multiplier) := represented.1 (.inr 5) rfl
  have sameLength : right.length = left.length := rightLength.trans leftLength.symm
  have productFits : oldProduct.length = left.length := productLength.trans leftLength.symm
  have sumFits : oldSum.length = left.length := oldSumLength.trans leftLength.symm
  have shiftedFits : oldShifted.length = left.length := shiftedLength.trans leftLength.symm
  have nextFits : oldNext.length = left.length := nextLength.trans leftLength.symm
  have sumCapacity : value left + value right < 2 ^ left.length := by
    rw [leftValue, rightValue, leftLength]
    exact valid.1
  have productCapacity : (value left + value right) * value multiplier < 2 ^ left.length := by
    rw [leftValue, rightValue, multiplierValue, leftLength]
    exact valid.2
  have trace := (runs left right multiplier sameLength oldProduct oldSum oldShifted oldNext
    productFits sumFits shiftedFits nextFits multiplyFlag addFlag sumCapacity).wire
    dataTapes (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains (.inr name)).width assignment = _
      fin_cases name <;> norm_num [domains, widths, leftLength, multiplierLength,
        EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.binaryNaturals])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes
      (frame left right multiplier oldProduct oldSum oldShifted oldNext multiplyFlag addFlag) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      fin_cases name
      · exact productEq.symm
      · exact sumEq.symm
      · exact shiftedEq.symm
      · exact nextEq.symm
      · exact multiplyFlagEq.symm
      · exact multiplierEq.symm
      · exact leftEq.symm
      · exact rightEq.symm
      · exact addFlagEq.symm
  have positions : install dataTapes (fun _ : Fin 9 => (0 : ℤ))
      (fun _ : Sum Bool (Fin 9) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  let productBits := product left right multiplier oldShifted oldNext multiplyFlag
  have productBitsLength : productBits.length = assignment false :=
    (product_length left right multiplier oldShifted oldNext multiplyFlag sameLength shiftedFits nextFits).trans leftLength
  have sumBitsLength : (sum left right).length = assignment false :=
    (sum_length left right sameLength).trans leftLength
  let productValue : Fin (2 ^ assignment false) := ⟨value productBits,
    by simpa only [productBitsLength] using Binary.value_lt_pow_length productBits⟩
  let sumValue : Fin (2 ^ assignment false) := ⟨value (sum left right),
    by simpa only [sumBitsLength] using Binary.value_lt_pow_length (sum left right)⟩
  let zeroValue : Fin (2 ^ assignment false) := ⟨value (List.replicate (assignment false) false),
    by simpa only [List.length_replicate] using Binary.value_lt_pow_length (List.replicate (assignment false) false)⟩
  let output : Outputs domains argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases flag : name = 4 ∨ name = 8
      · change (if name = 4 ∨ name = 8 then EncodedDomain.booleans
          else EncodedDomain.binaryNaturals (decide (name = 5))).Carrier assignment
        rw [ite_eq_left flag]
        exact false
      · by_cases source : name = 5
        · subst name; contradiction
        · change (if name = 4 ∨ name = 8 then EncodedDomain.booleans
            else EncodedDomain.binaryNaturals (decide (name = 5))).Carrier assignment
          rw [ite_eq_right flag]
          simp only [source, decide_false]
          exact if name = 0 then productValue else if name = 1 then sumValue else zeroValue
  refine ⟨multiplier.length * (6 * left.length + 14) + 8 * left.length + 17, output,
    install dataTapes (frame left right multiplier (word productBits) (word (sum left right))
      (word (List.replicate left.length false)) (word (List.replicate left.length false)) (data false) (data false)) initial,
    ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X, leftLength, multiplierLength]
    exact le_rfl
  · change value productBits = _
    simpa only [leftValue, rightValue, multiplierValue] using product_value left right multiplier
      oldShifted oldNext multiplyFlag sameLength shiftedFits nextFits sumCapacity productCapacity
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      change install dataTapes _ initial (dataTapes name) = _
      rw [install_at]
      fin_cases name
      · exact (encoded_binaryNaturals false assignment productBits productBitsLength).symm
      · exact (encoded_binaryNaturals false assignment (sum left right) sumBitsLength).symm
      · change buffer (word (List.replicate left.length false)) =
          encoded (EncodedDomain.binaryNaturals false) assignment zeroValue
        rw [leftLength]
        exact (encoded_binaryNaturals false assignment
          (List.replicate (assignment false) false) List.length_replicate).symm
      · change buffer (word (List.replicate left.length false)) =
          encoded (EncodedDomain.binaryNaturals false) assignment zeroValue
        rw [leftLength]
        exact (encoded_binaryNaturals false assignment
          (List.replicate (assignment false) false) List.length_replicate).symm
      · exact (encoded_booleans assignment false).symm
      · contradiction
      · contradiction
      · contradiction
      · exact (encoded_booleans assignment false).symm

end Polytime2.AddMultiply
