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

import Polytime2.Primitives.FinitePredicate
import Polytime2.Matrices.EntryContract
import Polytime2.Arithmetic.BinarySubtraction
import Polytime2.Primitives.SizeReadContract
import Polytime2.Arithmetic.BinaryIncrement
import Polytime2.Primitives.TapeCommands
import Polytime2.Machine.Pipeline

/-! # Fixed-width pivot-search controller

The matrix, column, starting row, and unary dimensions are immutable inputs.
Candidate rows live in a fixed-width binary word. Bounds are tested before
matrix lookup; a finite scalar predicate determines whether search continues.
-/

namespace Polytime2.StandardPivotSearch

open MultiTape CallingConvention

abbrev TapeName := Sum StandardMatrixEntry.TapeName (Fin 6)
abbrev Alphabet := CallingConvention.Alphabet TapeName

def sizeTape (parameter : Fin 3) : TapeName := .inl (.inl (.inl parameter))
def counterTape (name : Fin 9) : TapeName := .inl (.inl (.inr name))
def matrixTape : TapeName := .inl (.inr false)
def elementTape : TapeName := .inl (.inr true)
def startTape : TapeName := .inr 0
def rowLimitTape : TapeName := .inr 1
def differenceTape : TapeName := .inr 2
def foundTape : TapeName := .inr 3
def continueTape : TapeName := .inr 4
def nextTape : TapeName := .inr 5

noncomputable def domains (scalar : EncodedDomain.{0, 0} Empty) : TapeName → EncodedDomain (Fin 3)
  | .inl name => StandardMatrixEntry.domains scalar.constant name
  | .inr name => if name = 3 ∨ name = 4 then EncodedDomain.booleans else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl (.inl (.inl _)) => true
  | .inl (.inl (.inr name)) => decide (name = 6)
  | .inl (.inr name) => !name
  | .inr name => decide (name = 0)

def sizeTapes : Fin 3 ↪ TapeName :=
  ⟨sizeTape, by intro first second equal; cases equal; rfl⟩

def comparisonWiring : Sum Unit (Fin 4) ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => counterTape 1 | 1 => rowLimitTape | 2 => differenceTape | _ => foundTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [sizeTape, counterTape, rowLimitTape, differenceTape, foundTape]⟩

@[simp] theorem comparisonWiring_apply (name : Sum Unit (Fin 4)) : comparisonWiring name =
    (match name with
    | .inl _ => sizeTape 0
    | .inr name => match name.val with
      | 0 => counterTape 1 | 1 => rowLimitTape | 2 => differenceTape | _ => foundTape) := rfl

def testWiring : (Fin 1 ⊕ Fin 1) ↪ TapeName :=
  ⟨Sum.elim (fun _ => elementTape) (fun _ => continueTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [elementTape, continueTape]⟩

@[simp] theorem testWiring_apply (name : Fin 1 ⊕ Fin 1) : testWiring name =
    (match name with | .inl _ => elementTape | .inr _ => continueTape) := by cases name <;> rfl

def incrementWiring : Sum (Fin 3) Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl parameter => sizeTape parameter
    | .inr false => counterTape 1 | .inr true => nextTape), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [sizeTape, counterTape, nextTape]⟩

@[simp] theorem incrementWiring_apply (name : Sum (Fin 3) Bool) : incrementWiring name =
    (match name with
    | .inl parameter => sizeTape parameter
    | .inr false => counterTape 1 | .inr true => nextTape) := rfl

noncomputable def compare : Machine Alphabet (Sum StandardBinaryArithmetic.State Unit) :=
  MultiTape.wire comparisonWiring BinarySubtraction.algorithm

def limitWiring : Sum Bool Bool ↪ TapeName :=
  ⟨(fun name => match name with
    | .inl false => sizeTape 1 | .inl true => sizeTape 0
    | .inr false => rowLimitTape | .inr true => counterTape 2), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all [sizeTape, counterTape, rowLimitTape]⟩

@[simp] theorem limitWiring_apply (name : Sum Bool Bool) : limitWiring name =
    (match name with
    | .inl false => sizeTape 1 | .inl true => sizeTape 0
    | .inr false => rowLimitTape | .inr true => counterTape 2) := rfl

noncomputable def readLimit : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire limitWiring StandardSizeRead.algorithm

@[simp] theorem readLimit_halt (symbols : Symbols Alphabet) : readLimit StandardSizeRead.exit symbols = none := by
  simp [readLimit, MultiTape.wire, StandardSizeRead.algorithm]

noncomputable def readEntry (width : ℕ) : Machine Alphabet (StandardMatrixEntry.State width) :=
  MultiTape.wire Function.Embedding.inl (StandardMatrixEntry.machine width)

noncomputable def zeroTest (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) : Machine Alphabet (StandardFinitePredicate.State (scalar.width Empty.elim)) :=
  MultiTape.wire testWiring (StandardFinitePredicate.machine scalar isZero)

abbrev ReadTestState (width : ℕ) := Sum (StandardMatrixEntry.State width) (StandardFinitePredicate.State width)

noncomputable def readTest (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) : Machine Alphabet (ReadTestState (scalar.width Empty.elim)) :=
  MultiTape.sequence (readEntry (scalar.width Empty.elim)) (zeroTest scalar isZero) StandardFinitePredicate.entry

def readTestEntry (width : ℕ) : ReadTestState width := .inl (StandardMatrixEntry.entry width)
noncomputable def readTestExit (width : ℕ) : ReadTestState width := .inr StandardFinitePredicate.exit

noncomputable def stop : Machine Alphabet Bool := StandardTapeCommands.setBoolean continueTape false

def found (symbols : Symbols Alphabet) : Bool := decide (symbols foundTape = Binary.data true)
def continues (symbols : Symbols Alphabet) : Bool := decide (symbols continueTape = Binary.data true)

abbrev SelectState (width : ℕ) := Sum (Sum Unit (Sum (ReadTestState width) Bool)) Unit

noncomputable def select (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) : Machine Alphabet (SelectState (scalar.width Empty.elim)) :=
  MultiTape.withExit (MultiTape.branchMachine found (readTest scalar isZero) stop
    (readTestEntry (scalar.width Empty.elim)) false)

abbrev GuardState (width : ℕ) := Sum (Sum StandardBinaryArithmetic.State Unit) (SelectState width)

noncomputable def guard (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) : Machine Alphabet (GuardState (scalar.width Empty.elim)) :=
  MultiTape.sequence compare (select scalar isZero) (.inl (.inl ()))

def guardEntry (width : ℕ) : GuardState width := .inl BinarySubtraction.entry
def guardExit (width : ℕ) : GuardState width := .inr (.inr ())

abbrev IncrementState := Sum (StandardBinaryScan.State Bool) Unit
abbrev AdvanceState := Sum IncrementState (Fin 3)

noncomputable def increment : Machine Alphabet IncrementState :=
  MultiTape.wire incrementWiring (StandardBinaryScan.algorithm BinaryScan.increment)

noncomputable def copyNext : Machine Alphabet (Fin 3) :=
  StandardTapeCommands.copy nextTape (counterTape 1) (by decide)

noncomputable def advance : Machine Alphabet AdvanceState := MultiTape.sequence increment copyNext 0

def advanceEntry : AdvanceState := .inl (.inl (.inl true))
def advanceExit : AdvanceState := .inr 2

abbrev LoopBodyState := Sum AdvanceState Bool

noncomputable def loopBody : Machine Alphabet LoopBodyState :=
  MultiTape.sequence advance stop false

def loopBodyEntry : LoopBodyState := .inl advanceEntry
def loopBodyExit : LoopBodyState := .inr true

abbrev LoopState (width : ℕ) := Sum (Sum (GuardState width) LoopBodyState) Unit

noncomputable def loop (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) : Machine Alphabet (LoopState (scalar.width Empty.elim)) :=
  MultiTape.withExit (MultiTape.whileMachine (guard scalar isZero) loopBody
    (guardEntry (scalar.width Empty.elim)) loopBodyEntry continues)

def loopEntry (width : ℕ) : LoopState width := .inl (.inl (guardEntry width))
def loopExit (width : ℕ) : LoopState width := .inr ()

@[simp] theorem guard_halt (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) (symbols : Symbols Alphabet) :
    guard scalar isZero (guardExit (scalar.width Empty.elim)) symbols = none := rfl

@[simp] theorem advance_halt (symbols : Symbols Alphabet) : advance advanceExit symbols = none := by
  simp [advance, advanceExit, copyNext, StandardTapeCommands.copy, MultiTape.sequence, MultiTape.wire,
    StandardTerminatedCopy.machine]

@[simp] theorem loopBody_halt (symbols : Symbols Alphabet) :
    loopBody loopBodyExit symbols = none := by
  simp [loopBody, loopBodyExit, stop, StandardTapeCommands.setBoolean,
    StandardTapeCommands.booleanMachine, MultiTape.sequence, MultiTape.wire]

@[simp] theorem loop_halt (scalar : EncodedDomain.{0, 0} Empty)
    (isZero : ∀ assignment, scalar.Carrier assignment → Bool) (symbols : Symbols Alphabet) :
    loop scalar isZero (loopExit (scalar.width Empty.elim)) symbols = none := rfl

end Polytime2.StandardPivotSearch
