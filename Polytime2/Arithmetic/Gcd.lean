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

import Polytime2.Arithmetic.GcdMachine

/-! # GCD with immutable encoded arguments

Two input tapes are copied into private working slots. The Euclidean result
is copied to a separate output; scratch needs only bounded regions. The capacity hypothesis reserves a shift bit for division.
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

/-- Only working operands are initialized; private scratch needs region bounds. -/
theorem runs (left right : List Bool) (sameLength : left.length = right.length)
    (capacity : 2 * value right ≤ 2 ^ right.length)
    (initial : Tapes Alphabet) (sourceLeft : initial 9 = buffer (word left))
    (sourceRight : initial 10 = buffer (word right))
    (regions : ∀ name, Region (widths right.length name) 0 (initial name)) :
    ∃ ticks answer final,
      ticks ≤ 32 * right.length ^ 3 + 160 * right.length ^ 2 + 246 * right.length + 137 ∧
      answer.length = right.length ∧
      Runs (widths right.length) readOnly machine ticks entry (fun _ => 0) initial exit (fun _ => 0) final ∧
      value answer = Nat.gcd (value left) (value right) ∧ final 11 = buffer (word answer) := by
  obtain ⟨oldLeft, oldLeftLength, oldLeftEq⟩ := (regions 6).exists_buffer
  obtain ⟨oldRight, oldRightLength, oldRightEq⟩ := (regions 1).exists_buffer
  have copiedLeft := StandardTapeCommands.copy_runs (9 : Fin 12) 6 (by decide)
    (widths right.length) readOnly rfl left oldLeft
    (by simpa [widths] using sameLength.symm) (by simpa [widths] using sameLength.symm)
    (oldLeftLength.trans sameLength.symm) initial sourceLeft oldLeftEq
  let first := Function.update initial 6 (buffer (word left))
  have copiedRight := StandardTapeCommands.copy_runs (10 : Fin 12) 1 (by decide)
    (widths right.length) readOnly rfl right oldRight rfl rfl oldRightLength first
    sourceRight oldRightEq
  let second := Function.update first 1 (buffer (word right))
  have secondRegions : ∀ name, Region (widths right.length name) 0 (second name) :=
    fun name => copiedRight.region name (copiedLeft.region name (regions name))
  obtain ⟨kernelTicks, finalLeft, finalRight, localFinal, kernelCost, leftLength, rightLength,
    kernelTrace, leftEq, rightEq, finalZero, correct⟩ := StandardGcdMachine.runs left right sameLength
      (fun name => second (kernelWiring name)) (by
        change second 6 = buffer (word left)
        simp [second, first])
      (by change second 1 = buffer (word right); exact Function.update_self _ _ _)
      (by
        intro name
        have region := secondRegions (kernelWiring name)
        fin_cases name <;> simpa [widths, StandardGcdMachine.widths] using region) capacity
  obtain ⟨computed, calculated, located, outside, immutable⟩ := kernelTrace.wire_restoring kernelWiring
    (widths right.length) readOnly
    (by intro name; fin_cases name <;> simp [widths, StandardGcdMachine.widths])
    (by intro name premise; fin_cases name <;> contradiction) second (fun _ => rfl)
  obtain ⟨oldOutput, outputLength, outputEq⟩ := (calculated.region 11 (secondRegions 11)).exists_buffer
  have extracted := StandardTapeCommands.copy_runs (6 : Fin 12) 11 (by decide)
    (widths right.length) readOnly rfl finalLeft oldOutput
    leftLength.symm leftLength.symm (outputLength.trans leftLength.symm) computed
    ((located 6).trans leftEq) outputEq
  have afterCalculation := calculated.sequence extract 0
    (by intro symbols; simp [MultiTape.wire, StandardGcdMachine.machine, StandardGcdMachine.exit, MultiTape.withExit]) extracted
  have afterRight := copiedRight.sequence (MultiTape.sequence calculate extract 0)
    (.inl StandardGcdMachine.entry)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) afterCalculation
  have complete := copiedLeft.sequence _ (Sum.inl 0)
    (by intro symbols; simp [StandardTapeCommands.copy, MultiTape.wire, StandardTerminatedCopy.machine]) afterRight
  refine ⟨_, finalLeft, Function.update computed 11 (buffer (word finalLeft)), ?_,
    leftLength, complete, correct, Function.update_self _ _ _⟩
  nlinarith [kernelCost]

/-- The immutable size tape and all data tapes have canonical encoded domains. -/
noncomputable def domains : Sum Unit (Fin 12) → EncodedDomain Unit
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

/-- Public arguments are preserved and the sole output is their gcd. -/
theorem contract : CallingConvention.Realizes domains argumentReadOnly sizeTapes outputTapes algorithm entry exit
    (fun assignment input =>
      2 * (input ⟨.inr 10, rfl⟩ : Fin (2 ^ assignment ())).val ≤ 2 ^ assignment ())
    (fun assignment input output =>
      (output () : Fin (2 ^ assignment ())).val =
        Nat.gcd (input ⟨.inr 9, rfl⟩ : Fin (2 ^ assignment ())).val
          (input ⟨.inr 10, rfl⟩ : Fin (2 ^ assignment ())).val) := by
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), (by intro symbols; simp [algorithm, MultiTape.wire,
    machine, exit, MultiTape.sequence, extract, StandardTapeCommands.copy, StandardTerminatedCopy.machine]),
    32 * MvPolynomial.X () ^ 3 + 160 * MvPolynomial.X () ^ 2 + 246 * MvPolynomial.X () + 137, ?_⟩
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
  have widthsMatch : ∀ name, (domains (.inr name)).width assignment = widths right.length name := by
    intro name
    fin_cases name <;> norm_num [domains, widths, rightLength,
      EncodedDomain.booleans, EncodedDomain.fixed, EncodedDomain.binaryNaturals]
  obtain ⟨ticks, answer, localFinal, cost, answerLength, localTrace, correct, result⟩ :=
    runs left right (leftLength.trans rightLength.symm) (by rw [rightValue, rightLength]; exact valid)
      (fun name => initial (.inr name))
      ((represented.1 (.inr 9) rfl).trans (encoded_binaryNaturals_value () assignment _))
      ((represented.1 (.inr 10) rfl).trans (encoded_binaryNaturals_value () assignment _))
      (by intro name; rw [← widthsMatch]; exact represented.region (.inr name))
  obtain ⟨final, trace, located, outside, immutable⟩ := localTrace.wire_restoring dataTapes
    (fun name => (domains name).width assignment) argumentReadOnly widthsMatch
    (by intro name premise; exact premise) initial (fun _ => rfl)
  let output : Outputs domains outputTapes assignment := fun _ =>
    ⟨value answer, by simpa only [answerLength.trans rightLength] using Binary.value_lt_pow_length answer⟩
  refine ⟨ticks, output, final, ?_, trace, ?_, ?_⟩
  · simpa only [map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X, rightLength] using cost
  · simpa only [leftValue, rightValue] using correct
  · intro name
    cases name
    exact ((located 11).trans result).trans (encoded_binaryNaturals () assignment answer
      (answerLength.trans rightLength)).symm

end Polytime2.StandardGcd
