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

import Polytime2.StandardBinaryRemainder
import Polytime2.Gcd

/-! # A Euclidean step with immutable operands

Compute the remainder in private fixed-width storage, then copy the divisor
to a second output tape. The two original operands remain unchanged.
-/

namespace Polytime2.StandardGcdStep

open MultiTape CallingConvention
open Binary (Symbol word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 8)
abbrev State := Sum StandardBinaryRemainder.State (Fin 3)
abbrev Workspace := StandardBinaryRemainder.Workspace

/-- The remainder machine's seven tapes, followed by the new first operand. -/
def frame (left right : List Bool) (work : Workspace) (newLeft : List Symbol) : Tapes Alphabet :=
  fun name => if name = 0 then buffer (word work.1)
    else if name = 1 then buffer (word right)
    else if name = 2 then buffer work.2.1
    else if name = 3 then buffer work.2.2.1
    else if name = 4 then buffer [work.2.2.2.2]
    else if name = 5 then buffer work.2.2.2.1
    else if name = 6 then buffer (word left)
    else buffer newLeft

def initialFrame (left right : List Bool) (work : Workspace)
    (oldRemainder newLeft : List Symbol) : Tapes Alphabet :=
  fun name => if name = 0 then buffer oldRemainder else frame left right work newLeft name

def widths (digits : ℕ) (name : Fin 8) : ℕ := if name = 4 then 1 else digits

def readOnly (name : Fin 8) : Bool := decide (name = 1 ∨ name = 6)

def remainderWiring : Fin 7 ↪ Fin 8 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 8 => name.val) equal)⟩

def copyWiring : Bool ↪ Fin 8 :=
  ⟨(fun name => if name then 7 else 1), by
    intro first second equal
    cases first <;> cases second <;> simp_all⟩

@[simp] theorem remainderWiring_apply (name : Fin 7) :
    remainderWiring name = ⟨name.val, by omega⟩ := rfl
@[simp] theorem copyWiring_apply (name : Bool) :
    copyWiring name = (if name then 7 else 1) := rfl

noncomputable def remainderMachine : Machine Alphabet StandardBinaryRemainder.State :=
  MultiTape.wire remainderWiring StandardBinaryRemainder.machine

noncomputable def copyMachine : Machine Alphabet (Fin 3) :=
  MultiTape.wire copyWiring StandardTerminatedCopy.machine

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence remainderMachine copyMachine 0

def entry : State := .inl StandardBinaryRemainder.entry
def exit : State := .inr 2

private theorem remainder_install (left right : List Bool) (work original : Workspace)
    (newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (frame left right original newLeft) = frame left right work newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install remainderWiring _ _ (remainderWiring 0) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 1) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 2) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 3) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 4) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 5) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 6) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 8 => name.val) equal;
        have bounded := localName.isLt; simp only [remainderWiring_apply] at values; omega)

private theorem remainder_initial (left right : List Bool) (work : Workspace)
    (old newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.initialFrame (buffer (word left)) right old work)
      (initialFrame left right work old newLeft) = initialFrame left right work old newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install remainderWiring _ _ (remainderWiring 0) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 1) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 2) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 3) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 4) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 5) = _; rw [install_at]; rfl)
    | (change install remainderWiring _ _ (remainderWiring 6) = _; rw [install_at]; rfl)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        have values := congrArg (fun name : Fin 8 => name.val) equal;
        have bounded := localName.isLt; simp only [remainderWiring_apply] at values; omega)

private theorem remainder_final (left right : List Bool) (work original : Workspace)
    (old newLeft : List Symbol) :
    install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (initialFrame left right original old newLeft) = frame left right work newLeft := by
  have same : install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
      (initialFrame left right original old newLeft) =
      install remainderWiring (StandardBinaryRemainder.frame (buffer (word left)) right work)
        (frame left right original newLeft) := by
    funext name
    by_cases located : name ∈ Set.range remainderWiring
    · obtain ⟨localName, rfl⟩ := located
      rw [install_at, install_at]
    · rw [install_outside _ _ _ _ located, install_outside _ _ _ _ located]
      have notZero : name ≠ 0 := by
        intro equal
        subst name
        exact located ⟨0, rfl⟩
      simp [initialFrame, notZero]
  rw [same, remainder_install]

private theorem copy_install (left right : List Bool) (work : Workspace)
    (old newLeft : List Symbol) :
    install copyWiring (Copy.frame [0] (word right ++ [0]) [0] (newLeft ++ [0]))
      (frame left right work old) = frame left right work newLeft := by
  funext name
  fin_cases name
  all_goals first
    | (change install copyWiring _ _ (copyWiring false) = _;
        rw [install_at]; exact buffer_padding (word right))
    | (change install copyWiring _ _ (copyWiring true) = _;
        rw [install_at]; exact buffer_padding newLeft)
    | (apply install_outside; rintro ⟨localName, equal⟩;
        cases localName <;> simp [copyWiring_apply] at equal)

/-- A complete Euclidean step uses a separate output for each new operand.
Every internal controller obeys the fixed-region convention. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (old shifted difference result newLeft : List Symbol)
    (oldLength : old.length = right.length) (shiftedLength : shifted.length = right.length)
    (differenceLength : difference.length = right.length) (resultLength : result.length = right.length)
    (newLeftLength : newLeft.length = right.length) (flag : Symbol) :
    let work : Workspace := (List.replicate right.length false, shifted, difference, result, flag)
    Runs (widths right.length) readOnly machine (8 * right.length ^ 2 + 21 * right.length + 9)
      entry (fun _ => 0) (initialFrame left right work old newLeft)
      exit (fun _ => 0) (frame left right
        (StandardBinaryRemainder.finish right left.reverse work) (word right)) := by
  dsimp only
  let work : Workspace := (List.replicate right.length false, shifted, difference, result, flag)
  have first := (StandardBinaryRemainder.runs left right old shifted difference result
    oldLength shiftedLength differenceLength resultLength flag).wire
    remainderWiring (widths right.length) readOnly
    (by intro name; fin_cases name <;>
        simp [widths, StandardBinaryRemainder.widths, sameLength, remainderWiring_apply])
    (by intro name premise; fin_cases name <;>
        simp_all [readOnly, StandardBinaryRemainder.readOnly, remainderWiring_apply])
    (initialFrame left right work old newLeft) (fun _ => 0)
  have firstPositions : install remainderWiring (fun _ : Fin 7 => (0 : ℤ))
      (fun _ : Fin 8 => (0 : ℤ)) = fun _ => 0 := install_self remainderWiring _
  rw [firstPositions, remainder_initial, remainder_final] at first
  have second := (StandardTerminatedCopy.runs right newLeft newLeftLength).wire
    copyWiring (widths right.length) readOnly
    (by intro name; cases name <;> simp [widths, copyWiring_apply])
    (by intro name premise; cases name <;> simp [readOnly, copyWiring_apply] at premise ⊢)
    (frame left right (StandardBinaryRemainder.finish right left.reverse work) newLeft) (fun _ => 0)
  have secondPositions : install copyWiring (fun _ : Bool => (0 : ℤ))
      (fun _ : Fin 8 => (0 : ℤ)) = fun _ => 0 := install_self copyWiring _
  rw [secondPositions, copy_install, copy_install] at second
  have complete := first.sequence copyMachine 0
    (by intro symbols; simp [MultiTape.wire, StandardBinaryRemainder.machine, StandardBinaryRemainder.exit, MultiTape.sequence,
      StandardBinaryRemainder.loopMachine, StandardBitFold.machine, StandardBitFold.exit]) second
  simp only [sameLength] at complete
  convert complete using 1 <;> first | rfl | ring

/-- The two public results have the mathematical values of `Gcd.advance`. -/
theorem result_value (left right : List Bool) (shifted difference result : List Symbol) (flag : Symbol)
    (shiftedLength : shifted.length = right.length) (differenceLength : difference.length = right.length)
    (resultLength : result.length = right.length) (positive : 0 < value right)
    (capacity : 2 * value right ≤ 2 ^ right.length) :
    (value right, value (StandardBinaryRemainder.finish right left.reverse
      (List.replicate right.length false, shifted, difference, result, flag)).1) =
      Gcd.advance (value left, value right) := by
  rw [StandardBinaryRemainder.result_value left right shifted difference result flag
    shiftedLength differenceLength resultLength positive capacity]
  rfl

/-- The dividend and divisor are separate inputs, with unary digit capacity.
All six writable tapes have bounded mathematical domains, including scratch. -/
def domains : Sum Unit (Fin 8) → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()

def argumentReadOnly : Sum Unit (Fin 8) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 8 ↪ Sum Unit (Fin 8) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Unit ↪ Sum Unit (Fin 8) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit (Fin 8))) State :=
  MultiTape.wire dataTapes machine

/-- A Euclidean step returns `(b, a % b)` on separate output tapes. Both inputs
remain immutable; all scratch and output regions start arbitrarily. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes algorithm entry exit
    (fun assignment input =>
      0 < (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ∧
      2 * (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
    (fun assignment input output =>
      ((output ⟨.inr 7, rfl⟩ : Fin (2 ^ assignment ())).val,
        (output ⟨.inr 0, rfl⟩ : Fin (2 ^ assignment ())).val) =
      Gcd.advance ((input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment ())).val,
        (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val)) := by
  refine ⟨(by intro parameter; rfl), (by intro symbols; simp [algorithm, MultiTape.wire, machine, exit, MultiTape.sequence, copyMachine,
      StandardTerminatedCopy.machine]),
    8 * MvPolynomial.X () ^ 2 + 21 * MvPolynomial.X () + 9, ?_⟩
  intro assignment input initial valid represented sizes
  let dividend := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 6, rfl⟩)).getLsbD index.val)
  let divisor := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 1, rfl⟩)).getLsbD index.val)
  have dividendLength : dividend.length = assignment () := List.length_ofFn
  have divisorLength : divisor.length = assignment () := List.length_ofFn
  have dividendValue : value dividend = (input ⟨.inr 6, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 6, rfl⟩))
  have divisorValue : value divisor = (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 1, rfl⟩))
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 (.inr 0) rfl
  obtain ⟨oldShifted, shiftedLength, shiftedEq⟩ := represented.2 (.inr 2) rfl
  obtain ⟨oldDifference, differenceLength, differenceEq⟩ := represented.2 (.inr 3) rfl
  obtain ⟨oldResult, resultLength, resultEq⟩ := represented.2 (.inr 5) rfl
  obtain ⟨newLeft, newLeftLength, newLeftEq⟩ := represented.2 (.inr 7) rfl
  obtain ⟨flags, flagLength, flagEq⟩ := represented.2 (.inr 4) rfl
  change flags.length = 1 at flagLength
  obtain ⟨oldFlag, rfl⟩ := List.length_eq_one_iff.mp flagLength
  have sourceEq : initial (.inr 6) = buffer (word dividend) := represented.1 (.inr 6) rfl
  have divisorEq : initial (.inr 1) = buffer (word divisor) := represented.1 (.inr 1) rfl
  let work : Workspace :=
    (List.replicate divisor.length false, oldShifted, oldDifference, oldResult, oldFlag)
  have oldFits : old.length = divisor.length := oldLength.trans divisorLength.symm
  have shiftedFits : oldShifted.length = divisor.length := shiftedLength.trans divisorLength.symm
  have differenceFits : oldDifference.length = divisor.length := differenceLength.trans divisorLength.symm
  have resultFits : oldResult.length = divisor.length := resultLength.trans divisorLength.symm
  have newLeftFits : newLeft.length = divisor.length := newLeftLength.trans divisorLength.symm
  have fits : StandardBinaryRemainder.Fits divisor.length work := ⟨List.length_replicate, shiftedFits, differenceFits, resultFits⟩
  have start : install dataTapes (initialFrame dividend divisor work old newLeft) initial = initial := by
    funext name
    cases name with
    | inl parameter =>
      apply install_outside
      rintro ⟨name, equal⟩
      cases equal
    | inr name =>
      rw [show Sum.inr name = dataTapes name from rfl, install_at]
      fin_cases name
      · exact oldEq.symm
      · exact divisorEq.symm
      · exact shiftedEq.symm
      · exact differenceEq.symm
      · exact flagEq.symm
      · exact resultEq.symm
      · exact sourceEq.symm
      · exact newLeftEq.symm
  have localTrace := runs dividend divisor (dividendLength.trans divisorLength.symm)
    old oldShifted oldDifference oldResult newLeft oldFits shiftedFits differenceFits resultFits newLeftFits oldFlag
  have trace := localTrace.wire dataTapes (fun name => (domains name).width assignment) argumentReadOnly
    (by
      intro name
      change (domains (.inr name)).width assignment = widths divisor.length name
      fin_cases name <;> norm_num [domains, EncodedDomain.booleans, EncodedDomain.fixed,
        EncodedDomain.binaryNaturals, widths, dividendLength, divisorLength])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have positions : install dataTapes (fun _ : Fin 8 => (0 : ℤ))
      (fun _ : Sum Unit (Fin 8) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at trace
  have positiveWidth : 0 < assignment () := by
    have divisorBound := (input ⟨.inr 1, rfl⟩ : Fin (2 ^ assignment ())).isLt
    by_contra notPositive
    have zeroWidth : assignment () = 0 := by omega
    simp only [zeroWidth, pow_zero] at divisorBound
    omega
  have nonempty : dividend.reverse ≠ [] := by
    intro empty
    have lengthZero := congrArg List.length empty
    simp only [List.length_reverse, List.length_nil, dividendLength] at lengthZero
    omega
  obtain ⟨remainder, shifted, difference, result, flag, canonical⟩ :=
    StandardBinaryRemainder.finish_canonical dividend.reverse divisor work nonempty
  have finalFits := StandardBinaryRemainder.finish_fits dividend.reverse divisor work fits
  rw [canonical] at finalFits
  have remainderFits : remainder.length = assignment () := finalFits.1.trans divisorLength
  have shiftedFits' : shifted.length = assignment () := by
    simpa only [word, List.length_map] using finalFits.2.1.trans divisorLength
  have differenceFits' : difference.length = assignment () := by
    simpa only [word, List.length_map] using finalFits.2.2.1.trans divisorLength
  have resultFits' : result.length = assignment () := by
    simpa only [word, List.length_map] using finalFits.2.2.2.trans divisorLength
  have positive : 0 < value divisor := by rw [divisorValue]; exact valid.1
  have capacity : 2 * value divisor ≤ 2 ^ divisor.length := by
    rw [divisorValue, divisorLength]
    exact valid.2
  have correct := StandardBinaryRemainder.result_value dividend divisor oldShifted oldDifference oldResult oldFlag
    shiftedFits differenceFits resultFits positive capacity
  change value (StandardBinaryRemainder.finish divisor dividend.reverse work).1 = _ at correct
  rw [canonical] at correct
  change StandardBinaryRemainder.finish divisor dividend.reverse work = _ at canonical
  rw [canonical] at trace
  let remainderValue : Fin (2 ^ assignment ()) := ⟨value remainder,
    by simpa only [remainderFits] using Binary.value_lt_pow_length remainder⟩
  let shiftedValue : Fin (2 ^ assignment ()) := ⟨value shifted,
    by simpa only [shiftedFits'] using Binary.value_lt_pow_length shifted⟩
  let differenceValue : Fin (2 ^ assignment ()) := ⟨value difference,
    by simpa only [differenceFits'] using Binary.value_lt_pow_length difference⟩
  let resultValue : Fin (2 ^ assignment ()) := ⟨value result,
    by simpa only [resultFits'] using Binary.value_lt_pow_length result⟩
  let copiedValue : Fin (2 ^ assignment ()) := ⟨value divisor,
    by simpa only [divisorLength] using Binary.value_lt_pow_length divisor⟩
  let output : Outputs domains argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases isFlag : name = 4
      · subst name
        exact flag
      · change (if name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals ()).Carrier assignment
        rw [ite_eq_right (by exact isFlag)]
        exact if name = 0 then remainderValue else if name = 2 then shiftedValue
          else if name = 3 then differenceValue else if name = 5 then resultValue else copiedValue
  refine ⟨8 * divisor.length ^ 2 + 21 * divisor.length + 9, output,
    install dataTapes (frame dividend divisor
      (remainder, word shifted, word difference, word result, Binary.data flag) (word divisor)) initial,
    ?_, trace, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X]
    rw [divisorLength]
  · change (value divisor, value remainder) = Gcd.advance _
    apply Prod.ext
    · exact divisorValue
    · simpa only [Gcd.advance, dividendValue, divisorValue] using correct
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      change install dataTapes _ initial (dataTapes name) = _
      rw [install_at]
      fin_cases name
      · exact (encoded_binaryNaturals () assignment remainder remainderFits).symm
      · contradiction
      · exact (encoded_binaryNaturals () assignment shifted shiftedFits').symm
      · exact (encoded_binaryNaturals () assignment difference differenceFits').symm
      · exact (encoded_booleans assignment flag).symm
      · exact (encoded_binaryNaturals () assignment result resultFits').symm
      · contradiction
      · exact (encoded_binaryNaturals () assignment divisor divisorLength).symm

end Polytime2.StandardGcdStep
