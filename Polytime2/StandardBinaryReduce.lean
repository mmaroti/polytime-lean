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

import Polytime2.StandardBinaryArithmetic
import Polytime2.BinarySubtraction
import Polytime2.BinaryEncoding

/-! # Reduction with immutable operands and a separate result

Subtract into private low-word and borrow tapes, then select the dividend on
underflow or the difference otherwise. All regions have fixed widths, output
contents are arbitrary initially, and no markers or growing counters are used.
-/

namespace Polytime2.StandardBinaryReduce

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := fun _ : Fin 5 => Symbol
abbrev ArithmeticState := StandardBinaryArithmetic.State

def frame (left right : List Bool) (scratch result : List Symbol) (flag : Symbol) :
    Tapes Alphabet := fun name =>
  if name = 0 then buffer (word left)
  else if name = 1 then buffer (word right)
  else if name = 2 then buffer scratch
  else if name = 3 then buffer [flag]
  else buffer result

def widths (digits : ℕ) (name : Fin 5) : ℕ := if name = 3 then 1 else digits

def readOnly (name : Fin 5) : Bool := decide (name.val < 2)

def subtractionWiring : Fin 4 ↪ Fin 5 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 5 => name.val) equal)⟩

def selectionWiring : Fin 4 ↪ Fin 5 :=
  ⟨(fun name => match name.val with | 0 => 0 | 1 => 2 | 2 => 4 | _ => 3), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem subtractionWiring_apply (name : Fin 4) :
    subtractionWiring name = ⟨name.val, by omega⟩ := rfl

@[simp] theorem selectionWiring_apply (name : Fin 4) :
    selectionWiring name = (match name.val with | 0 => 0 | 1 => 2 | 2 => 4 | _ => 3) := rfl

def chooseDigit (left right selector : Bool) : Bool := if selector then left else right

def keepSelector (_left _right selector : Bool) : Bool := selector

private theorem select_ripple (selector : Bool) (left right : List Bool)
    (sameLength : right.length = left.length) :
    BinaryRipple.ripple chooseDigit keepSelector selector left right =
      (if selector then left else right, selector) := by
  induction left generalizing right with
  | nil =>
    have empty : right = [] := List.eq_nil_of_length_eq_zero sameLength
    subst right
    cases selector <;> rfl
  | cons bit bits hypothesis =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have tail := hypothesis rest (by simpa using sameLength)
      cases selector <;> simp_all [BinaryRipple.ripple, chooseDigit, keepSelector]

noncomputable def subtraction : Machine Alphabet ArithmeticState :=
  MultiTape.wire subtractionWiring
    (StandardBinaryArithmetic.machine BinarySubtraction.digit BinarySubtraction.borrow)

noncomputable def choose : Machine Alphabet ArithmeticState :=
  MultiTape.wire selectionWiring (StandardBinaryArithmetic.machine chooseDigit keepSelector)

def condition (symbols : Symbols Alphabet) : Bool := symbols 3 == 2

abbrev SelectionState := Sum (Sum Unit (Sum ArithmeticState ArithmeticState)) Unit

noncomputable def selection : Machine Alphabet SelectionState :=
  MultiTape.withExit (branchMachine condition choose choose (.inl true) (.inl false))

abbrev State := Sum ArithmeticState SelectionState

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence subtraction selection (.inl (.inl ()))

def entry : State := .inl (.inl false)
def exit : State := .inr (.inr ())

def reduced (left right : List Bool) : List Bool :=
  let difference := BinarySubtraction.ripple false left right
  if difference.2 then left else difference.1

/-- One subtraction suffices under the usual restoring-division invariant. -/
theorem reduced_value (left right : List Bool) (sameLength : right.length = left.length)
    (small : value left < 2 * value right) : value (reduced left right) = value left % value right := by
  by_cases borrowed : (BinarySubtraction.ripple false left right).2 = true
  · simp only [reduced, borrowed, ↓reduceIte]
    exact (Nat.mod_eq_of_lt ((BinarySubtraction.underflow_iff left right sameLength).mp borrowed)).symm
  · have nonnegative : value right ≤ value left := by
      have notLess := mt (BinarySubtraction.underflow_iff left right sameLength).mpr borrowed
      omega
    have noBorrow : (BinarySubtraction.ripple false left right).2 = false := Bool.eq_false_iff.mpr borrowed
    simp only [reduced, noBorrow, Bool.false_eq_true, ↓reduceIte]
    rw [BinarySubtraction.difference_of_no_borrow left right sameLength nonnegative]
    rw [Nat.mod_eq_sub_mod nonnegative,
      Nat.mod_eq_of_lt (show value left - value right < value right by omega)]

private theorem subtraction_install (left right : List Bool) (scratch result : List Symbol)
    (flag : Symbol) (newScratch : List Symbol) (newFlag : Symbol) :
    install subtractionWiring
      (StandardBinaryArithmetic.frame [0] (word left ++ [0]) [0] (word right ++ [0])
        [0] (newScratch ++ [0]) newFlag) (frame left right scratch result flag) =
      frame left right newScratch result newFlag := by
  funext name
  fin_cases name
  · change install subtractionWiring _ _ (subtractionWiring 0) = _
    rw [install_at]
    exact buffer_padding (word left)
  · change install subtractionWiring _ _ (subtractionWiring 1) = _
    rw [install_at]
    exact buffer_padding (word right)
  · change install subtractionWiring _ _ (subtractionWiring 2) = _
    rw [install_at]
    exact buffer_padding newScratch
  · change install subtractionWiring _ _ (subtractionWiring 3) = _
    rw [install_at]
    rfl
  · apply install_outside
    rintro ⟨localName, equal⟩
    have values := congrArg (fun name : Fin 5 => name.val) equal
    have bounded := localName.isLt
    simp only [subtractionWiring_apply] at values
    omega

private theorem selection_install (left right difference : List Bool) (result : List Symbol)
    (flag : Symbol) (newResult : List Symbol) (newFlag : Symbol) :
    install selectionWiring
      (StandardBinaryArithmetic.frame [0] (word left ++ [0]) [0] (word difference ++ [0])
        [0] (newResult ++ [0]) newFlag) (frame left right (word difference) result flag) =
      frame left right (word difference) newResult newFlag := by
  funext name
  fin_cases name
  · change install selectionWiring _ _ (selectionWiring 0) = _
    rw [install_at]
    exact buffer_padding (word left)
  · apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> simp [selectionWiring_apply] at equal
  · change install selectionWiring _ _ (selectionWiring 1) = _
    rw [install_at]
    exact buffer_padding (word difference)
  · change install selectionWiring _ _ (selectionWiring 3) = _
    rw [install_at]
    rfl
  · change install selectionWiring _ _ (selectionWiring 2) = _
    rw [install_at]
    exact buffer_padding newResult

private theorem subtraction_runs (left right : List Bool) (sameLength : right.length = left.length)
    (scratch result : List Symbol) (scratchLength : scratch.length = left.length) (flag : Symbol) :
    Runs (widths left.length) readOnly subtraction (2 * left.length + 2)
      (.inl false) (fun _ => 0) (frame left right scratch result flag)
      (.inr ((BinarySubtraction.ripple false left right).2, true)) (fun _ => 0)
      (frame left right (word (BinarySubtraction.ripple false left right).1) result
        (data (BinarySubtraction.ripple false left right).2)) := by
  have trace := (StandardBinaryArithmetic.runs BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength scratch scratchLength flag).wire subtractionWiring
    (widths left.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, subtractionWiring_apply, StandardBinaryArithmetic.width])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, subtractionWiring_apply, StandardBinaryArithmetic.readOnly])
    (frame left right scratch result flag) (fun _ => 0)
  have positions : install subtractionWiring (fun _ : Fin 4 => (0 : ℤ))
      (fun _ : Fin 5 => (0 : ℤ)) = fun _ => 0 :=
    install_self subtractionWiring (fun _ : Fin 5 => (0 : ℤ))
  rw [positions, subtraction_install, subtraction_install] at trace
  exact trace

private theorem choose_runs (selector : Bool) (left right difference : List Bool)
    (sameLength : difference.length = left.length) (result : List Symbol)
    (resultLength : result.length = left.length) (flag : Symbol) :
    Runs (widths left.length) readOnly choose (2 * left.length + 2)
      (.inl selector) (fun _ => 0) (frame left right (word difference) result flag)
      (.inr (selector, true)) (fun _ => 0)
      (frame left right (word difference) (word (if selector then left else difference)) (data selector)) := by
  have localTrace := StandardBinaryArithmetic.runs chooseDigit keepSelector selector
    left difference sameLength result resultLength flag
  simp only [StandardBinaryArithmetic.ripple, select_ripple selector left difference sameLength] at localTrace
  have trace := localTrace.wire selectionWiring (widths left.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, selectionWiring_apply, StandardBinaryArithmetic.width])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, selectionWiring_apply, StandardBinaryArithmetic.readOnly])
    (frame left right (word difference) result flag) (fun _ => 0)
  have positions : install selectionWiring (fun _ : Fin 4 => (0 : ℤ))
      (fun _ : Fin 5 => (0 : ℤ)) = fun _ => 0 :=
    install_self selectionWiring (fun _ : Fin 5 => (0 : ℤ))
  rw [positions, selection_install, selection_install] at trace
  exact trace

/-- Subtraction and selection realize reduction without ever modifying either
operand. Scratch and result regions may initially contain blanks or any symbols. -/
theorem runs (left right : List Bool) (sameLength : right.length = left.length)
    (scratch result : List Symbol) (scratchLength : scratch.length = left.length)
    (resultLength : result.length = left.length) (flag : Symbol) :
    Runs (widths left.length) readOnly machine (4 * left.length + 7)
      entry (fun _ => 0) (frame left right scratch result flag)
      exit (fun _ => 0) (frame left right (word (BinarySubtraction.ripple false left right).1)
        (word (reduced left right)) (data (BinarySubtraction.ripple false left right).2)) := by
  have differenceLength := BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
    false left right sameLength
  have first := subtraction_runs left right sameLength scratch result scratchLength flag
  cases borrowed : (BinarySubtraction.ripple false left right).2 with
  | false =>
    have chosen := choose_runs false left right (BinarySubtraction.ripple false left right).1
      differenceLength result resultLength (data false)
    have branch := chosen.branch_false condition choose (.inl true)
      (by simp [condition, MultiTape.read, frame, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, data])
      (by intro symbols; simp [choose, MultiTape.wire, StandardBinaryArithmetic.machine])
    rw [borrowed] at first
    have complete := first.sequence selection (.inl (.inl ()))
      (by intro symbols; simp [subtraction, MultiTape.wire, StandardBinaryArithmetic.machine]) branch
    simp only [reduced, borrowed, Bool.false_eq_true, ↓reduceIte] at complete ⊢
    convert complete using 1 <;> first | rfl | omega
  | true =>
    have chosen := choose_runs true left right (BinarySubtraction.ripple false left right).1
      differenceLength result resultLength (data true)
    have branch := chosen.branch_true condition choose (.inl false)
      (by simp [condition, MultiTape.read, frame, buffer, Turing.Tape.mk₁, Turing.Tape.mk₂, data])
      (by intro symbols; simp [choose, MultiTape.wire, StandardBinaryArithmetic.machine])
    rw [borrowed] at first
    have complete := first.sequence selection (.inl (.inl ()))
      (by intro symbols; simp [subtraction, MultiTape.wire, StandardBinaryArithmetic.machine]) branch
    simp only [reduced, borrowed, ↓reduceIte] at complete ⊢
    convert complete using 1 <;> first | rfl | omega

/-- The sole size parameter is the common binary digit capacity. -/
def domains : Sum Unit (Fin 5) → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 3 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

def argumentReadOnly : Sum Unit (Fin 5) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 5 ↪ Sum Unit (Fin 5) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Unit ↪ Sum Unit (Fin 5) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

/-- The immutable unary size tape stays stationary during reduction. -/
noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit (Fin 5))) State :=
  MultiTape.wire dataTapes machine

/-- Reduction implements mathematical remainder on bounded natural domains.
All three writable tapes, including private difference and borrow storage,
start arbitrarily and finish as valid, uniquely encoded values. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm entry exit
    (fun assignment input =>
      (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val <
        2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val)
    (fun assignment input output =>
      (output ⟨.inr 4, rfl⟩ : Fin (2 ^ assignment ())).val =
        (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val %
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  refine ⟨(by intro parameter; rfl), ?_, 4 * MvPolynomial.X () + 7, ?_⟩
  · intro symbols
    simp [algorithm, MultiTape.wire, machine, exit, MultiTape.sequence, selection, MultiTape.withExit]
  · intro assignment input initial valid represented sizes
    let left := List.ofFn (fun index : Fin (assignment ()) =>
      (BitVec.ofFin (input ⟨.inr 0, rfl⟩)).getLsbD index.val)
    let right := List.ofFn (fun index : Fin (assignment ()) =>
      (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
    have leftLength : left.length = assignment () := List.length_ofFn
    have rightLength : right.length = assignment () := List.length_ofFn
    have sameLength : right.length = left.length := rightLength.trans leftLength.symm
    have leftValue : value left = (input ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 0, rfl⟩))
    have rightValue : value right = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val :=
      Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
    obtain ⟨scratch, scratchLength, scratchEq⟩ := represented.2 (.inr 2) rfl
    obtain ⟨result, resultLength, resultEq⟩ := represented.2 (.inr 4) rfl
    obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 3) rfl
    change flags.length = 1 at flagLength
    obtain ⟨flag, rfl⟩ := List.length_eq_one_iff.mp flagLength
    have sourceFirst : initial (.inr 0) = buffer (word left) := represented.1 (.inr 0) rfl
    have sourceSecond : initial (.inr 1) = buffer (word right) := represented.1 (.inr 1) rfl
    have start : install dataTapes (frame left right scratch result flag) initial = initial := by
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
        · exact scratchEq.symm
        · exact flagEq.symm
        · exact resultEq.symm
    have scratchFits : scratch.length = left.length := scratchLength.trans leftLength.symm
    have resultFits : result.length = left.length := resultLength.trans leftLength.symm
    have localTrace := runs left right sameLength scratch result scratchFits resultFits flag
    have trace := localTrace.wire dataTapes (fun name => (domains name).width assignment) argumentReadOnly
      (by
        intro name
        change (domains (.inr name)).width assignment = widths left.length name
        fin_cases name <;> norm_num [domains, EncodedDomain.booleans, EncodedDomain.fixed,
          EncodedDomain.binaryNaturals, widths, leftLength])
      (by intro name premise; exact premise) initial (fun _ => 0)
    have positions : install dataTapes (fun _ : Fin 5 => (0 : ℤ))
        (fun _ : Sum Unit (Fin 5) => (0 : ℤ)) = fun _ => 0 :=
      install_self dataTapes (fun _ : Sum Unit (Fin 5) => (0 : ℤ))
    rw [start, positions] at trace
    let difference := (BinarySubtraction.ripple false left right).1
    let borrowed := (BinarySubtraction.ripple false left right).2
    have differenceLength : difference.length = assignment () :=
      (BinaryRipple.ripple_length BinarySubtraction.digit BinarySubtraction.borrow
        false left right sameLength).trans leftLength
    have reducedLength : (reduced left right).length = assignment () := by
      dsimp only [reduced]
      split
      · exact leftLength
      · exact differenceLength
    let differenceValue : Fin (2 ^ assignment ()) := ⟨value difference,
      by simpa only [differenceLength] using Binary.value_lt_pow_length difference⟩
    let resultValue : Fin (2 ^ assignment ()) := ⟨value (reduced left right),
      by simpa only [reducedLength] using Binary.value_lt_pow_length (reduced left right)⟩
    let output : Outputs domains argumentReadOnly assignment := fun name => by
      rcases name with ⟨name, writable⟩
      cases name with
      | inl parameter => contradiction
      | inr name =>
        by_cases isFlag : name = 3
        · subst name
          exact borrowed
        · change (if name = 3 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()).Carrier assignment
          rw [ite_eq_right (by exact isFlag)]
          exact if name = 2 then differenceValue else resultValue
    refine ⟨4 * left.length + 7, output,
      install dataTapes (frame left right (word difference) (word (reduced left right)) (data borrowed)) initial,
      ?_, trace, ?_, ?_⟩
    · simp only [map_add, map_mul, map_ofNat, MvPolynomial.eval_X]
      omega
    · have small : value left < 2 * value right := by rw [leftValue, rightValue]; exact valid
      change value (reduced left right) = _
      simpa only [leftValue, rightValue] using reduced_value left right sameLength small
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        change install dataTapes _ initial (dataTapes name) = _
        rw [install_at]
        fin_cases name
        · contradiction
        · contradiction
        · exact (encoded_binaryNaturals () assignment difference differenceLength).symm
        · exact (encoded_booleans assignment borrowed).symm
        · exact (encoded_binaryNaturals () assignment (reduced left right) reducedLength).symm

end Polytime2.StandardBinaryReduce
