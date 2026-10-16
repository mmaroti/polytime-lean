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

import Polytime2.StandardFixedRead
import Polytime2.StandardConstant

/-! # Finite tables on binary-encoded arguments

The widths and the table belong to the specialization. Both arguments are
immutable, every output bit is overwritten, and there are no scratch tapes.
The registers in the controller have fixed finite types.
-/

namespace Polytime2.StandardFiniteTable

open MultiTape CallingConvention
open Binary (Symbol word)

abbrev Alphabet := CallingConvention.Alphabet (Fin 3)
abbrev Register := StandardFixedRead.Memory
abbrev State (firstWidth secondWidth outputWidth : ℕ) :=
  Sum (StandardFixedRead.State firstWidth)
    (Sum (Register firstWidth × StandardFixedRead.State secondWidth)
      (Sum ((Register firstWidth × Register secondWidth) × Copy.State outputWidth) Unit))

variable {firstWidth secondWidth outputWidth : ℕ}

def widths (firstWidth secondWidth outputWidth : ℕ) (name : Fin 3) : ℕ :=
  if name = 0 then firstWidth else if name = 1 then secondWidth else outputWidth

def readOnly (name : Fin 3) : Bool := decide (name.val < 2)

def frame (first second : List Bool) (output : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word first)
  else if name = 1 then buffer (word second) else buffer output

/-- A scalar block at the current head, with explicit neighboring array data. -/
def frameWithContext (first second : List Bool) (output : List Symbol)
    (left right : Fin 3 → List Symbol) : Tapes Alphabet := fun name =>
  Turing.Tape.mk' (Turing.ListBlank.mk (left name))
    (Turing.ListBlank.mk ((if name = 0 then word first
      else if name = 1 then word second else output) ++ right name))

noncomputable def read (name : Fin 3) (width : ℕ) : Machine Alphabet (StandardFixedRead.State width) :=
  MultiTape.wire (oneTape name) (StandardFixedRead.machine width)

noncomputable def write (bits : BitVec outputWidth) : Machine Alphabet (Copy.State outputWidth) :=
  MultiTape.wire (oneTape 2) (StandardConstant.ofBitVec bits)

noncomputable def machine (table : Register firstWidth → Register secondWidth → BitVec outputWidth) :
    Machine Alphabet (State firstWidth secondWidth outputWidth)
  | .inl state, symbols => match read 0 firstWidth state symbols with
    | some (next, actions) => some (.inl next, actions)
    | none =>
      let secondEntry : StandardFixedRead.State secondWidth :=
        ((false, Fin.last secondWidth), fun _ => false)
      some (.inr (.inl (state.2, secondEntry)), stationary symbols)
  | .inr (.inl (first, state)), symbols => match read 1 secondWidth state symbols with
    | some (next, actions) => some (.inr (.inl (first, next)), actions)
    | none =>
      let writerEntry : Copy.State outputWidth := (false, Fin.last outputWidth)
      some (.inr (.inr (.inl ((first, state.2), writerEntry))), stationary symbols)
  | .inr (.inr (.inl ((first, second), state))), symbols =>
    match write (table first second) state symbols with
    | some (next, actions) => some (.inr (.inr (.inl ((first, second), next))), actions)
    | none => some (.inr (.inr (.inr ())), stationary symbols)
  | .inr (.inr (.inr _)), _ => none

def entry : State firstWidth secondWidth outputWidth :=
  .inl ((false, Fin.last firstWidth), fun _ => false)

def exit : State firstWidth secondWidth outputWidth := .inr (.inr (.inr ()))

private theorem read_runs (name : Fin 3) (width : ℕ) (bits : List Bool)
    (length : bits.length = width) (memory : Register width)
    (enclosingWidth : Fin 3 → ℕ) (widthMatches : enclosingWidth name = width)
    (initial : Tapes Alphabet) (left right : List Symbol)
    (source : initial name = Turing.Tape.mk' (Turing.ListBlank.mk left)
      (Turing.ListBlank.mk (word bits ++ right))) :
    Runs enclosingWidth readOnly (read name width) (2 * width + 1)
      ((false, Fin.last width), memory) (fun _ => 0) initial
      ((true, 0), fun index => (bits[index.val]?).getD false) (fun _ => 0) initial := by
  apply (StandardFixedRead.runsWithContext width bits length memory left right).wire_of_eq
    (oneTape name) enclosingWidth readOnly
  · intro localName
    exact widthMatches
  · intro localName premise
    rfl
  · intro localName
    exact source
  · intro localName
    exact source
  · intro localName outside
    rfl

private theorem stationary_run
    (table : Register firstWidth → Register secondWidth → BitVec outputWidth)
    (initial : Tapes Alphabet) (state nextState : State firstWidth secondWidth outputWidth)
    (instruction : machine table state (MultiTape.read initial) =
      some (nextState, stationary (MultiTape.read initial))) :
    Runs (widths firstWidth secondWidth outputWidth) readOnly (machine table) 1
      state (fun _ => 0) initial nextState (fun _ => 0) initial := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [stationary, displacement, add_zero, act_stationary] using
    Runs.zero (machine := machine table) nextState (fun _ => 0) initial

/-- A binary finite table has a constant-time bound fixed before its input
values. Reading and writing widths may differ and may be zero. -/
theorem runsWithContext
    (table : Register firstWidth → Register secondWidth → BitVec outputWidth)
    (first second : List Bool) (firstLength : first.length = firstWidth)
    (secondLength : second.length = secondWidth) (old : List Symbol)
    (oldLength : old.length = outputWidth) (left right : Fin 3 → List Symbol) :
    let firstRegister : Register firstWidth := fun index => (first[index.val]?).getD false
    let secondRegister : Register secondWidth := fun index => (second[index.val]?).getD false
    let result := List.ofFn (fun index : Fin outputWidth =>
      (table firstRegister secondRegister).getLsbD index.val)
    Runs (widths firstWidth secondWidth outputWidth) readOnly (machine table)
      (2 * (firstWidth + secondWidth + outputWidth) + 6)
      entry (fun _ => 0) (frameWithContext first second old left right)
      exit (fun _ => 0) (frameWithContext first second (word result) left right) := by
  intro firstRegister secondRegister result
  let initial := frameWithContext first second old left right
  let final := frameWithContext first second (word result) left right
  have firstTrace := (read_runs 0 firstWidth first firstLength (fun _ => false)
    (widths firstWidth secondWidth outputWidth) (by simp [widths]) initial (left 0) (right 0) rfl).rename
    Sum.inl (target := machine table) (by
      intro state symbols next actions instruction
      simp [machine, instruction])
  have firstHandover := stationary_run table initial
    (.inl ((true, 0), firstRegister))
    (.inr (.inl (firstRegister, ((false, Fin.last secondWidth), fun _ => false))))
    (by simp [machine, read, MultiTape.wire, StandardFixedRead.machine])
  have secondTrace := (read_runs 1 secondWidth second secondLength (fun _ => false)
    (widths firstWidth secondWidth outputWidth) (by simp [widths]) initial (left 1) (right 1) rfl).rename
    (fun state => .inr (.inl (firstRegister, state))) (target := machine table) (by
      intro state symbols next actions instruction
      simp [machine, instruction])
  have secondHandover := stationary_run table initial
    (.inr (.inl (firstRegister, ((true, 0), secondRegister))))
    (.inr (.inr (.inl ((firstRegister, secondRegister), (false, Fin.last outputWidth)))))
    (by simp [machine, read, MultiTape.wire, StandardFixedRead.machine])
  have writer := (StandardConstant.ofBitVec_runsWithContext (table firstRegister secondRegister)
    old oldLength (left 2) (right 2)).wire_of_eq (oneTape (2 : Fin 3))
    (widths firstWidth secondWidth outputWidth) readOnly
    (by intro name; simp [widths])
    (by intro name premise; exact premise)
    initial final (by intro name; rfl) (by intro name; rfl) (by
      intro name outside
      fin_cases name <;> first | rfl | exact False.elim (outside ⟨(), rfl⟩))
  have written := writer.rename
    (fun state => .inr (.inr (.inl ((firstRegister, secondRegister), state))))
    (target := machine table) (by
      intro state symbols next actions instruction
      simp [machine, write, instruction])
  have lastHandover := stationary_run table final
    (.inr (.inr (.inl ((firstRegister, secondRegister), (true, 0))))) exit
    (by simp [machine, write, MultiTape.wire, StandardConstant.ofBitVec,
      StandardConstant.machineSized, exit])
  have complete := firstTrace.trans (firstHandover.trans
    (secondTrace.trans (secondHandover.trans (written.trans lastHandover))))
  convert complete using 1 <;> first | rfl | omega

/-- Standalone inputs and output are the standard public calling convention. -/
theorem runs
    (table : Register firstWidth → Register secondWidth → BitVec outputWidth)
    (first second : List Bool) (firstLength : first.length = firstWidth)
    (secondLength : second.length = secondWidth) (old : List Symbol)
    (oldLength : old.length = outputWidth) :
    let firstRegister : Register firstWidth := fun index => (first[index.val]?).getD false
    let secondRegister : Register secondWidth := fun index => (second[index.val]?).getD false
    let result := List.ofFn (fun index : Fin outputWidth =>
      (table firstRegister secondRegister).getLsbD index.val)
    Runs (widths firstWidth secondWidth outputWidth) readOnly (machine table)
      (2 * (firstWidth + secondWidth + outputWidth) + 6)
      entry (fun _ => 0) (frame first second old)
      exit (fun _ => 0) (frame first second (word result)) := by
  have contextFrame (input output : List Bool) (contents : List Symbol) :
      frameWithContext input output contents (fun _ => [0]) (fun _ => [0]) =
        frame input output contents := by
    funext name
    fin_cases name <;> simp [frameWithContext, frame, buffer_padding]
  simpa only [contextFrame] using
    runsWithContext table first second firstLength secondLength old oldLength
      (fun _ => [0]) (fun _ => [0])

-- carrierLevel: mathematical values of the specialization-fixed domains.
universe carrierLevel

/-- A decoded finite operation becomes a table on fixed controller registers.
Unused binary labels have arbitrary behavior outside the input contract. -/
noncomputable def encodedTable (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ assignment, firstDomain.Carrier assignment →
      secondDomain.Carrier assignment → outputDomain.Carrier assignment) :
    Register (firstDomain.width Empty.elim) → Register (secondDomain.width Empty.elim) →
      BitVec (outputDomain.width Empty.elim) := fun first second =>
  match firstDomain.decode Empty.elim
      (BitVec.ofNat _ (Binary.value (List.ofFn first))),
    secondDomain.decode Empty.elim (BitVec.ofNat _ (Binary.value (List.ofFn second))) with
  | some firstValue, some secondValue =>
    outputDomain.encode Empty.elim (operation Empty.elim firstValue secondValue)
  | _, _ => 0

def domains (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty) :
    Fin 3 → EncodedDomain Empty
  | 0 => firstDomain
  | 1 => secondDomain
  | 2 => outputDomain

/-- The table returns one result; its argument tapes remain immutable. -/
def outputTapes : Unit ↪ Fin 3 := oneTape 2

def sizeTapes : Empty ↪ Fin 3 := ⟨Empty.elim, by intro parameter; cases parameter⟩

noncomputable def algorithm
    (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ assignment, firstDomain.Carrier assignment →
      secondDomain.Carrier assignment → outputDomain.Carrier assignment) :
    Machine Alphabet (State (firstDomain.width Empty.elim) (secondDomain.width Empty.elim)
      (outputDomain.width Empty.elim)) :=
  machine (encodedTable firstDomain secondDomain outputDomain operation)

/-- Every mathematical operation between specialization-fixed encoded domains
is realized by a finite binary table, with separate arguments and output.
No hypothesis about the old output contents is needed. -/
theorem contract (firstDomain secondDomain outputDomain : EncodedDomain.{0, carrierLevel} Empty)
    (operation : ∀ assignment, firstDomain.Carrier assignment →
      secondDomain.Carrier assignment → outputDomain.Carrier assignment) :
    CallingConvention.Realizes (domains firstDomain secondDomain outputDomain)
      readOnly sizeTapes outputTapes (algorithm firstDomain secondDomain outputDomain operation) entry exit
      (fun _ _ => True)
      (fun assignment input output => output () =
        operation assignment (input ⟨0, rfl⟩) (input ⟨1, rfl⟩)) := by
  refine ⟨(by intro parameter; cases parameter), (by intro name; rfl), (by intro symbols; rfl),
    MvPolynomial.C (2 * (firstDomain.width Empty.elim + secondDomain.width Empty.elim +
      outputDomain.width Empty.elim) + 6), ?_⟩
  intro assignment input initial valid represented sizes
  have sameAssignment : assignment = (Empty.elim : Empty → ℕ) := Subsingleton.elim _ _
  subst assignment
  let firstValue : firstDomain.Carrier Empty.elim := input ⟨0, rfl⟩
  let secondValue : secondDomain.Carrier Empty.elim := input ⟨1, rfl⟩
  let firstCode := firstDomain.encode Empty.elim firstValue
  let secondCode := secondDomain.encode Empty.elim secondValue
  let firstBits := List.ofFn (fun index : Fin (firstDomain.width Empty.elim) =>
    firstCode.getLsbD index.val)
  let secondBits := List.ofFn (fun index : Fin (secondDomain.width Empty.elim) =>
    secondCode.getLsbD index.val)
  let firstRegister : Register (firstDomain.width Empty.elim) :=
    fun index => (firstBits[index.val]?).getD false
  let secondRegister : Register (secondDomain.width Empty.elim) :=
    fun index => (secondBits[index.val]?).getD false
  have firstRegisterEq : firstRegister = fun index => firstCode.getLsbD index.val := by
    funext index
    simp [firstRegister, firstBits, index.isLt]
  have secondRegisterEq : secondRegister = fun index => secondCode.getLsbD index.val := by
    funext index
    simp [secondRegister, secondBits, index.isLt]
  let result := operation Empty.elim firstValue secondValue
  let resultBits := List.ofFn (fun index : Fin (outputDomain.width Empty.elim) =>
    (outputDomain.encode Empty.elim result).getLsbD index.val)
  have selected : encodedTable firstDomain secondDomain outputDomain operation
      firstRegister secondRegister = outputDomain.encode Empty.elim result := by
    rw [firstRegisterEq, secondRegisterEq]
    simp only [encodedTable, Binary.value_bits, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      firstCode, secondCode, firstDomain.decode_encode, secondDomain.decode_encode, result]
  obtain ⟨old, oldLength, oldEq⟩ := represented.2 2 rfl
  have initialEq : initial = frame firstBits secondBits old := by
    funext name
    fin_cases name
    · exact represented.1 0 rfl
    · exact represented.1 1 rfl
    · exact oldEq
  let output : Outputs (domains firstDomain secondDomain outputDomain) outputTapes Empty.elim :=
    fun _ => result
  have trace := runs (encodedTable firstDomain secondDomain outputDomain operation)
    firstBits secondBits List.length_ofFn List.length_ofFn old oldLength
  dsimp only at trace
  rw [show (fun index => (firstBits[index.val]?).getD false) = firstRegister from rfl,
    show (fun index => (secondBits[index.val]?).getD false) = secondRegister from rfl,
    selected] at trace
  have domainWidths : (fun name => (domains firstDomain secondDomain outputDomain name).width Empty.elim) =
      widths (firstDomain.width Empty.elim) (secondDomain.width Empty.elim)
        (outputDomain.width Empty.elim) := by
    funext name
    fin_cases name <;> rfl
  refine ⟨2 * (firstDomain.width Empty.elim + secondDomain.width Empty.elim +
    outputDomain.width Empty.elim) + 6, output,
    frame firstBits secondBits (word resultBits), by simp, ?_, rfl, ?_⟩
  · rw [initialEq, domainWidths]
    exact trace
  · intro name
    cases name
    rfl

end Polytime2.StandardFiniteTable
