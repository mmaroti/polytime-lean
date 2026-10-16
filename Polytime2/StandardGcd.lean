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

import Polytime2.StandardGcdMachine

/-! # GCD with immutable encoded arguments

Two input tapes are copied into private working slots. The Euclidean machine
clears its scratch before returning, then its result is copied to a separate
output. The capacity hypothesis reserves a shift bit for division.
-/

namespace Polytime2.StandardGcd

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev Alphabet := CallingConvention.Alphabet (Fin 12)
abbrev State := Sum (Fin 3) (Sum (Fin 3) (Sum StandardGcdMachine.State (Fin 3)))

def widths (digits : ℕ) (name : Fin 12) : ℕ := if name = 4 ∨ name = 8 then 1 else digits

def readOnly (name : Fin 12) : Bool := decide (name = 9 ∨ name = 10)

def kernelWiring : Fin 9 ↪ Fin 12 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by
    intro first second equal
    exact Fin.ext (congrArg (fun name : Fin 12 => name.val) equal)⟩

@[simp] theorem kernelWiring_apply (name : Fin 9) : kernelWiring name = ⟨name.val, by omega⟩ := rfl

noncomputable def initializeLeft : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 9 6 (by decide)
noncomputable def initializeRight : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 10 1 (by decide)
noncomputable def calculate : Machine Alphabet StandardGcdMachine.State :=
  MultiTape.wire kernelWiring StandardGcdMachine.machine
noncomputable def extract : Machine Alphabet (Fin 3) := StandardTapeCommands.copy 6 11 (by decide)

noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence initializeLeft
    (MultiTape.sequence initializeRight
      (MultiTape.sequence calculate extract 0) (.inl StandardGcdMachine.entry)) (.inl 0)

def entry : State := .inl 0
def exit : State := .inr (.inr (.inr 2))

private theorem outside_kernel : (11 : Fin 12) ∉ Set.range kernelWiring := by
  rintro ⟨name, equal⟩
  have values := congrArg (fun name : Fin 12 => name.val) equal
  have bounded := name.isLt
  simp only [kernelWiring_apply] at values
  omega

/-- Copying inputs and extracting the answer adds only linear work. All
read-only inputs and all surrounding blanks are preserved at every transition. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (capacity : 2 * value right ≤ 2 ^ right.length)
    (initial : Tapes Alphabet) (contents : Fin 12 → List Symbol)
    (sourceLeft : initial 9 = buffer (word left)) (sourceRight : initial 10 = buffer (word right))
    (represented : ∀ name, readOnly name = false → initial name = buffer (contents name))
    (fits : ∀ name, readOnly name = false → (contents name).length = widths right.length name) :
    ∃ ticks finalLeft finalRight final,
      ticks ≤ 16 * right.length ^ 3 + 70 * right.length ^ 2 + 108 * right.length + 65 ∧
      finalLeft.length = right.length ∧ finalRight.length = right.length ∧
      Runs (widths right.length) readOnly machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      value finalLeft = Nat.gcd (value left) (value right) ∧
      (∀ name : Fin 9, final (kernelWiring name) =
        StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch right.length) (data false) name) ∧
      final 11 = buffer (word finalLeft) := by
  have borrowLength : (contents 4).length = 1 := fits 4 rfl
  have guardLength : (contents 8).length = 1 := fits 8 rfl
  obtain ⟨borrow, borrowEq⟩ := List.length_eq_one_iff.mp borrowLength
  obtain ⟨flag, flagEq⟩ := List.length_eq_one_iff.mp guardLength
  let scratch : StandardGcdMachine.Scratch :=
    ((fun name => match name.val with
      | 0 => contents 0 | 1 => contents 2 | 2 => contents 3 | 3 => contents 5 | _ => contents 7), borrow)
  have scratchFits : StandardGcdMachine.Fits right.length scratch := by
    intro name
    fin_cases name
    · exact fits 0 rfl
    · exact fits 2 rfl
    · exact fits 3 rfl
    · exact fits 5 rfl
    · exact fits 7 rfl
  have copiedLeft := StandardTapeCommands.copy_runs (9 : Fin 12) 6 (by decide)
    (widths right.length) readOnly rfl left (contents 6)
    (by simpa [widths] using sameLength.symm) (by simpa [widths] using sameLength.symm)
    (by simpa [widths, sameLength] using fits 6 rfl) initial sourceLeft (represented 6 rfl)
  let first := Function.update initial 6 (buffer (word left))
  have copiedRight := StandardTapeCommands.copy_runs (10 : Fin 12) 1 (by decide)
    (widths right.length) readOnly rfl right (contents 1) rfl rfl (fits 1 rfl) first
    (by simpa [first] using sourceRight) (by simpa [first] using represented 1 rfl)
  let second := Function.update first 1 (buffer (word right))
  obtain ⟨kernelTicks, finalLeft, finalRight, kernelCost, leftLength, rightLength,
    kernelTrace, finalZero, correct⟩ := StandardGcdMachine.runs left right sameLength scratch scratchFits flag capacity
  have calculated := kernelTrace.wire kernelWiring (widths right.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardGcdMachine.widths, kernelWiring_apply])
    (by intro name premise; fin_cases name <;> simp [readOnly, kernelWiring_apply] at premise)
    second (fun _ => 0)
  have initialMatches : install kernelWiring (StandardGcdMachine.frame left right scratch flag) second = second := by
    funext name
    by_cases located : name ∈ Set.range kernelWiring
    · obtain ⟨localName, rfl⟩ := located
      rw [install_at]
      fin_cases localName <;>
        simp [second, first, StandardGcdMachine.frame, scratch, kernelWiring_apply,
          represented 0 rfl, represented 2 rfl, represented 3 rfl, represented 4 rfl,
          represented 5 rfl, represented 7 rfl, represented 8 rfl, borrowEq, flagEq]
    · exact install_outside _ _ _ _ located
  have positions : install kernelWiring (fun _ : Fin 9 => (0 : ℤ))
      (fun _ : Fin 12 => (0 : ℤ)) = fun _ => 0 := install_self kernelWiring _
  rw [initialMatches, positions] at calculated
  let computed := install kernelWiring
    (StandardGcdMachine.frame finalLeft finalRight (StandardGcdMachine.zeroScratch right.length) (data false)) second
  have resultSource : computed 6 = buffer (word finalLeft) := by
    change install kernelWiring _ _ (kernelWiring 6) = _
    rw [install_at]
    rfl
  have oldOutput : computed 11 = buffer (contents 11) := by
    dsimp only [computed]
    rw [install_outside _ _ _ _ outside_kernel]
    simpa [second, first] using represented 11 rfl
  have resultLength : (contents 11).length = finalLeft.length := (fits 11 rfl).trans leftLength.symm
  have extracted := StandardTapeCommands.copy_runs (6 : Fin 12) 11 (by decide)
    (widths right.length) readOnly rfl finalLeft (contents 11)
    (by simpa [widths] using leftLength.symm) (by simpa [widths] using leftLength.symm)
    resultLength computed resultSource oldOutput
  have afterCalculation := calculated.sequence extract 0
    (by intro symbols; simp [MultiTape.wire, StandardGcdMachine.machine, StandardGcdMachine.exit,
      MultiTape.sequence, StandardGcdMachine.cleanup, StandardGcdMachine.cleanupExit,
      StandardTapeCommands.setBoolean, StandardTapeCommands.booleanMachine]) extracted
  have afterRight := copiedRight.sequence (MultiTape.sequence calculate extract 0)
    (.inl StandardGcdMachine.entry)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) afterCalculation
  have complete := copiedLeft.sequence _ (Sum.inl 0)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) afterRight
  simp only [sameLength, leftLength] at complete
  refine ⟨2 * right.length + 2 + (2 * right.length + 2 + (kernelTicks + (2 * right.length + 2) + 1) + 1) + 1,
    finalLeft, finalRight, Function.update computed 11 (buffer (word finalLeft)), ?_,
    leftLength, rightLength, complete, correct, ?_, Function.update_self _ _ _⟩
  · nlinarith [kernelCost]
  · intro name
    have different : kernelWiring name ≠ 11 := by
      intro equal
      exact outside_kernel ⟨name, equal⟩
    rw [Function.update_of_ne different]
    dsimp only [computed]
    rw [install_at]

/-- The immutable size tape and all data tapes have canonical encoded domains. -/
def domains : Sum Unit (Fin 12) → EncodedDomain Unit
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 ∨ name = 8 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals ()

def argumentReadOnly : Sum Unit (Fin 12) → Bool
  | .inl _ => true
  | .inr name => readOnly name

def dataTapes : Fin 12 ↪ Sum Unit (Fin 12) :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

def sizeTapes : Unit ↪ Sum Unit (Fin 12) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

noncomputable def algorithm : Machine (CallingConvention.Alphabet (Sum Unit (Fin 12))) State :=
  MultiTape.wire dataTapes machine

/-- Only the gcd result is exposed; all working tapes are private. -/
def outputTapes : Unit ↪ Sum Unit (Fin 12) := oneTape (.inr 11)

/-- The public GCD interface preserves separate input tapes and writes a
separate result. Its capacity hypothesis reserves the division shift bit. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment input =>
      2 * (input ⟨.inr 10, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
    (fun assignment input output =>
      (output () : Fin (2 ^ assignment ())).val =
        Nat.gcd (input ⟨.inr 9, rfl⟩ : Fin (2 ^ assignment ())).val
          (input ⟨.inr 10, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  classical
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire,
    machine, exit, MultiTape.sequence, extract, StandardTapeCommands.copy,
    StandardTerminatedCopy.machine]),
    16 * MvPolynomial.X () ^ 3 + 70 * MvPolynomial.X () ^ 2 + 108 * MvPolynomial.X () + 65, ?_⟩
  intro assignment input initial valid represented sizes
  let left := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 9, rfl⟩)).getLsbD index.val)
  let right := List.ofFn (fun index : Fin (assignment ()) =>
    (BitVec.ofFin (input ⟨.inr 10, rfl⟩)).getLsbD index.val)
  have leftLength : left.length = assignment () := List.length_ofFn
  have rightLength : right.length = assignment () := List.length_ofFn
  have leftValue : value left = (input ⟨.inr 9, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 9, rfl⟩))
  have rightValue : value right = (input ⟨.inr 10, rfl⟩ : Fin (2 ^ assignment ())).val :=
    Binary.value_bits (BitVec.ofFin (input ⟨.inr 10, rfl⟩))
  let contents : Fin 12 → List Symbol := fun name =>
    if writable : readOnly name = false then Classical.choose (represented.2 (.inr name) writable) else []
  have contentsSpec (name : Fin 12) (writable : readOnly name = false) :
      (contents name).length = (domains (.inr name)).width assignment ∧
        initial (.inr name) = buffer (contents name) := by
    dsimp only [contents]
    rw [dite_eq_left writable]
    exact Classical.choose_spec (represented.2 (.inr name) writable)
  obtain ⟨ticks, finalLeft, finalRight, final, cost, finalLeftLength, finalRightLength,
    trace, correct, scratchEq, resultEq⟩ := runs left right (leftLength.trans rightLength.symm)
    (by rw [rightValue, rightLength]; exact valid) (fun name => initial (.inr name)) contents
    (represented.1 (.inr 9) rfl) (represented.1 (.inr 10) rfl)
    (fun name writable => (contentsSpec name writable).2)
    (by
      intro name writable
      have fits := (contentsSpec name writable).1
      fin_cases name <;> simpa [domains, widths, EncodedDomain.booleans, show Nat.clog 2 2 = 1 from by decide,
        EncodedDomain.fixed, EncodedDomain.binaryNaturals, rightLength] using fits)
  have wired := trace.wire dataTapes (fun name => (domains name).width assignment) argumentReadOnly
    (by intro name; change (domains (.inr name)).width assignment = _
        fin_cases name <;> norm_num [domains, widths, rightLength,
      EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.binaryNaturals])
    (by intro name premise; exact premise) initial (fun _ => 0)
  have start : install dataTapes (fun name => initial (.inr name)) initial = initial :=
    install_self dataTapes initial
  have positions : install dataTapes (fun _ : Fin 12 => (0 : ℤ))
      (fun _ : Sum Unit (Fin 12) => (0 : ℤ)) = fun _ => 0 := install_self dataTapes _
  rw [start, positions] at wired
  let output : Outputs domains outputTapes assignment := fun _ =>
    ⟨value finalLeft, by simpa only [finalLeftLength.trans rightLength] using Binary.value_lt_pow_length finalLeft⟩
  refine ⟨ticks, output, install dataTapes final initial, ?_, wired, ?_, ?_⟩
  · simpa only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X, rightLength] using cost
  · simpa only [leftValue, rightValue] using correct
  · intro name
    cases name
    change install dataTapes final initial (dataTapes 11) = _
    rw [install_at]
    exact resultEq.trans (encoded_binaryNaturals () assignment finalLeft
      (finalLeftLength.trans rightLength)).symm

end Polytime2.StandardGcd
