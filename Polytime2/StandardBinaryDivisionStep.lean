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

import Polytime2.StandardBinaryScan
import Polytime2.StandardBinaryReduce

/-! # A long-division step with immutable inputs

A remainder and divisor are read-only arguments. Shift the next dividend bit
into private storage, reduce it, and write the next remainder separately.
All scratch and output regions can initially contain arbitrary symbols.
-/

namespace Polytime2.StandardBinaryDivisionStep

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 6 => Symbol
abbrev State := Sum (StandardBinaryScan.State Bool) StandardBinaryReduce.State

/-- Tapes: remainder, divisor, shifted word, difference, borrow, next remainder. -/
def frame (remainder divisor : List Bool) (shifted difference result : List Symbol)
    (flag : Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word remainder)
  else if name = 1 then buffer (word divisor)
  else if name = 2 then buffer shifted
  else if name = 3 then buffer difference
  else if name = 4 then buffer [flag]
  else buffer result

def widths (digits : ℕ) (name : Fin 6) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 6) : Bool := decide (name.val < 2)

def shiftWiring : Bool ↪ Fin 6 :=
  ⟨(fun name => if name then 2 else 0), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

def reduceWiring : Fin 5 ↪ Fin 6 :=
  ⟨(fun name => match name.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | _ => 5), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem shiftWiring_apply (name : Bool) :
    shiftWiring name = (if name then 2 else 0) := rfl

@[simp] theorem reduceWiring_apply (name : Fin 5) :
    reduceWiring name = (match name.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 4 | _ => 5) := rfl

noncomputable def shiftMachine : Machine Alphabet (StandardBinaryScan.State Bool) :=
  MultiTape.wire shiftWiring (StandardBinaryScan.machine BinaryScan.shift)

noncomputable def reduceMachine : Machine Alphabet StandardBinaryReduce.State :=
  MultiTape.wire reduceWiring StandardBinaryReduce.machine

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence shiftMachine reduceMachine StandardBinaryReduce.entry

def entry (bit : Bool) : State := .inl (.inl bit)
def exit : State := .inr StandardBinaryReduce.exit

def shifted (bit : Bool) (remainder : List Bool) : List Bool :=
  (BinaryScan.run BinaryScan.shift bit remainder).2

def next (bit : Bool) (remainder divisor : List Bool) : List Bool :=
  StandardBinaryReduce.reduced (shifted bit remainder) divisor

@[simp] theorem shifted_length (bit : Bool) (remainder : List Bool) :
    (shifted bit remainder).length = remainder.length := BinaryScan.run_length _ _ _

/-- A leading capacity bit makes the shift exact under the division invariant. -/
theorem next_value (bit : Bool) (remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length)
    (bounded : value remainder < value divisor)
    (capacity : 2 * value divisor ≤ 2 ^ remainder.length) :
    value (next bit remainder divisor) = (bit.toNat + 2 * value remainder) % value divisor := by
  have bitBound : bit.toNat ≤ 1 := by cases bit <;> decide
  have fits : bit.toNat + 2 * value remainder < 2 ^ remainder.length := by omega
  have shiftedValue := (BinaryScan.shift_value bit remainder fits).1
  change value (shifted bit remainder) = _ at shiftedValue
  have small : value (shifted bit remainder) < 2 * value divisor := by
    change value (shifted bit remainder) = _ at shiftedValue
    omega
  have reducedValue := StandardBinaryReduce.reduced_value (shifted bit remainder) divisor
    (by simpa using sameLength) small
  simpa only [next, shiftedValue] using reducedValue

private theorem shift_install (remainder divisor : List Bool)
    (old difference result newShifted : List Symbol) (flag : Symbol) :
    install shiftWiring
      (Copy.frame [0] (word remainder ++ [0]) [0] (newShifted ++ [0]))
      (frame remainder divisor old difference result flag) =
      frame remainder divisor newShifted difference result flag := by
  funext name
  fin_cases name
  · change install shiftWiring _ _ (shiftWiring false) = _
    rw [install_at]
    exact buffer_padding (word remainder)
  · apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [shiftWiring_apply] at equal
  · change install shiftWiring _ _ (shiftWiring true) = _
    rw [install_at]
    exact buffer_padding newShifted
  all_goals
    apply install_outside
    rintro ⟨localName, equal⟩
    cases localName <;> simp [shiftWiring_apply] at equal

private theorem reduce_install (remainder divisor shifted : List Bool)
    (oldDifference oldResult newDifference newResult : List Symbol) (oldFlag newFlag : Symbol) :
    install reduceWiring (StandardBinaryReduce.frame shifted divisor newDifference newResult newFlag)
      (frame remainder divisor (word shifted) oldDifference oldResult oldFlag) =
      frame remainder divisor (word shifted) newDifference newResult newFlag := by
  funext name
  fin_cases name
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [reduceWiring_apply] at equal
  · change install reduceWiring _ _ (reduceWiring 1) = _
    rw [install_at]
    rfl
  · change install reduceWiring _ _ (reduceWiring 0) = _
    rw [install_at]
    rfl
  · change install reduceWiring _ _ (reduceWiring 2) = _
    rw [install_at]
    rfl
  · change install reduceWiring _ _ (reduceWiring 3) = _
    rw [install_at]
    rfl
  · change install reduceWiring _ _ (reduceWiring 4) = _
    rw [install_at]
    rfl

/-- Every internal subroutine preserves the immutable operands, completely
writes its own outputs, and restores its heads. No scratch formatting is needed. -/
theorem runs (bit : Bool) (remainder divisor : List Bool)
    (sameLength : divisor.length = remainder.length)
    (old difference result : List Symbol)
    (oldLength : old.length = remainder.length)
    (differenceLength : difference.length = remainder.length)
    (resultLength : result.length = remainder.length) (flag : Symbol) :
    Runs (widths remainder.length) readOnly machine (6 * remainder.length + 10)
      (entry bit) (fun _ => 0) (frame remainder divisor old difference result flag)
      exit (fun _ => 0)
      (frame remainder divisor (word (shifted bit remainder))
        (word (BinarySubtraction.ripple false (shifted bit remainder) divisor).1)
        (word (next bit remainder divisor))
        (data (BinarySubtraction.ripple false (shifted bit remainder) divisor).2)) := by
  have shiftedTrace := (StandardBinaryScan.runs BinaryScan.shift bit remainder old oldLength).wire
    shiftWiring (widths remainder.length) readOnly
    (by intro name; cases name <;> simp [widths, shiftWiring_apply])
    (by intro name premise; cases name <;> simp_all [readOnly, shiftWiring_apply])
    (frame remainder divisor old difference result flag) (fun _ => 0)
  have shiftPositions : install shiftWiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Fin 6 => (0 : ℤ)) = fun _ => 0 := install_self shiftWiring _
  rw [shiftPositions, shift_install, shift_install] at shiftedTrace
  have reducedTrace := (StandardBinaryReduce.runs (shifted bit remainder) divisor
    (by simpa using sameLength) difference result
    (by simpa using differenceLength) (by simpa using resultLength) flag).wire
    reduceWiring (widths remainder.length) readOnly
    (by intro name; fin_cases name <;>
        simp [widths, StandardBinaryReduce.widths, reduceWiring_apply])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, StandardBinaryReduce.readOnly, reduceWiring_apply])
    (frame remainder divisor (word (shifted bit remainder)) difference result flag) (fun _ => 0)
  have reducePositions : install reduceWiring (fun _ : Fin 5 => (0 : ℤ))
      (fun _ : Fin 6 => (0 : ℤ)) = fun _ => 0 := install_self reduceWiring _
  rw [reducePositions, reduce_install, reduce_install] at reducedTrace
  have complete := shiftedTrace.sequence reduceMachine StandardBinaryReduce.entry
    (by intro symbols; simp [MultiTape.wire, StandardBinaryScan.machine]) reducedTrace
  simp only [shifted_length] at complete
  convert complete using 1 <;> first | rfl | omega

/-- All ordinary words have the common binary capacity; the borrow has one bit. -/
def domains : Sum Unit (Fin 6) → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

def argumentReadOnly : Sum Unit (Fin 6) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 6 ↪ Sum Unit (Fin 6) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Unit ↪ Sum Unit (Fin 6) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit (Fin 6))) State :=
  MultiTape.wire dataTapes machine

/-- The long-division step returns valid encodings on every scratch tape as
well as the public result. Its capacity hypothesis excludes shift overflow. -/
theorem contract (bit : Bool) :
    CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm (entry bit) exit
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val <
          (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ∧
        2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
      (fun assignment input output =>
        (output ⟨.inr 5, rfl⟩ : Fin (2 ^ assignment ())).val =
          (bit.toNat + 2 * (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val) %
          (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  refine ⟨(by intro parameter; rfl), ?_, 6 * MvPolynomial.X () + 10, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.wire, machine, exit, MultiTape.sequence, reduceMachine,
      StandardBinaryReduce.machine, StandardBinaryReduce.exit, StandardBinaryReduce.selection,
      MultiTape.withExit]
  · intro assignment input initial valid represented sizes
    let remainder := List.ofFn (fun index : Fin (assignment ()) =>
      (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val)
    let divisor := List.ofFn (fun index : Fin (assignment ()) =>
      (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
    have remainderLength : remainder.length = assignment () := List.length_ofFn
    have divisorLength : divisor.length = assignment () := List.length_ofFn
    have sameLength : divisor.length = remainder.length := divisorLength.trans remainderLength.symm
    have remainderValue : value remainder = (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 0, rfl⟩))
    have divisorValue : value divisor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
    obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 2) rfl
    obtain ⟨difference, differenceLength, differenceEq⟩ := represented.2 (.inr 3) rfl
    obtain ⟨result, resultLength, resultEq⟩ := represented.2 (.inr 5) rfl
    obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 4) rfl
    change flags.length = 1 at flagLength
    obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
    have sourceFirst : initial (.inr 0) = buffer (word remainder) := represented.1 (.inr 0) rfl
    have sourceSecond : initial (.inr 1) = buffer (word divisor) := represented.1 (.inr 1) rfl
    have start : install dataTapes (frame remainder divisor old difference result flag) initial = initial := by
      funext name
      cases name with
      | inl parameter =>
        apply install_outside
        rintro ⟨name, equal⟩
        cases equal
      | inr name =>
        rw [show Sum.inr name = dataTapes name from rfl, install_at]
        fin_cases name
        · exact sourceFirst.symm
        · exact sourceSecond.symm
        · exact oldEq.symm
        · exact differenceEq.symm
        · exact flagEq.symm
        · exact resultEq.symm
    have localTrace := runs bit remainder divisor sameLength old difference result
      (oldLength.trans remainderLength.symm) (differenceLength.trans remainderLength.symm)
      (resultLength.trans remainderLength.symm) flag
    have trace := localTrace.wire dataTapes (fun name => (domains name).width assignment) argumentReadOnly
      (by
        intro name
        change (domains (.inr name)).width assignment = widths remainder.length name
        fin_cases name <;> norm_num [domains, EncodedDomain.booleans, EncodedDomain.fixed,
          EncodedDomain.binaryNaturals, widths, remainderLength])
      (by intro name premise; exact premise) initial (fun _ => 0)
    have positions : install dataTapes (fun _ : Fin 6 => (0 : ℤ))
        (fun _ : Sum Unit (Fin 6) => (0 : ℤ)) = fun _ => 0 :=
      install_self dataTapes (fun _ : Sum Unit (Fin 6) => (0 : ℤ))
    rw [start, positions] at trace
    let shiftedWord := shifted bit remainder
    let differenceWord := (BinarySubtraction.ripple false shiftedWord divisor).1
    let borrowed := (BinarySubtraction.ripple false shiftedWord divisor).2
    have shiftedLength : shiftedWord.length = assignment () :=
      (shifted_length bit remainder).trans remainderLength
    have differenceFits : differenceWord.length = assignment () :=
      (BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
        false shiftedWord divisor (by omega)).trans shiftedLength
    have nextLength : (next bit remainder divisor).length = assignment () := by
      dsimp only [next, StandardBinaryReduce.reduced]
      split
      · exact shiftedLength
      · exact differenceFits
    let shiftedValue : Fin (2 ^ assignment ()) := ⟨value shiftedWord,
      by simpa only [shiftedLength] using Binary.value_lt_pow_length shiftedWord⟩
    let differenceValue : Fin (2 ^ assignment ()) := ⟨value differenceWord,
      by simpa only [differenceFits] using Binary.value_lt_pow_length differenceWord⟩
    let resultValue : Fin (2 ^ assignment ()) := ⟨value (next bit remainder divisor),
      by simpa only [nextLength] using Binary.value_lt_pow_length (next bit remainder divisor)⟩
    let output : Outputs domains argumentReadOnly assignment := fun name => by
      rcases name with ⟨name, writable⟩
      cases name with
      | inl parameter => contradiction
      | inr name =>
        by_cases isFlag : name = 4
        · subst name
          exact borrowed
        · change (if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()).Carrier assignment
          rw [ite_eq_right (by exact isFlag)]
          exact if name = 2 then shiftedValue else if name = 3 then differenceValue else resultValue
    refine ⟨6 * remainder.length + 10, output,
      install dataTapes (frame remainder divisor (word shiftedWord) (word differenceWord)
        (word (next bit remainder divisor)) (data borrowed)) initial,
      ?_, trace, ?_, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
      omega
    · change value (next bit remainder divisor) = _
      have bounded : value remainder < value divisor := by
        rw [remainderValue, divisorValue]
        exact valid.1
      have capacity : 2 * value divisor ≤ 2 ^ remainder.length := by
        rw [divisorValue, remainderLength]
        exact valid.2
      simpa only [remainderValue, divisorValue] using next_value bit remainder divisor sameLength bounded capacity
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        change install dataTapes _ initial (dataTapes name) = _
        rw [install_at]
        fin_cases name
        · contradiction
        · contradiction
        · exact (encoded_binaryNaturals () assignment shiftedWord shiftedLength).symm
        · exact (encoded_binaryNaturals () assignment differenceWord differenceFits).symm
        · exact (encoded_booleans assignment borrowed).symm
        · exact (encoded_binaryNaturals () assignment (next bit remainder divisor) nextLength).symm

end Polytime2.StandardBinaryDivisionStep
