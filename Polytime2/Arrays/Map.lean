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

import Polytime2.Primitives.BinaryFiniteTable

/-! # Binary array traversal by a specialization-fixed scalar table

A scalar parameter and source array are immutable. The output may initially
contain arbitrary symbols. Scalar blocks are read and written with finite
registers; runtime array lengths are never part of the finite controller.
-/

namespace Polytime2.StandardArrayMap

open MultiTape CallingConvention
open Binary (Symbol data word)

abbrev Alphabet := StandardFiniteTable.Alphabet
abbrev Register := StandardFiniteTable.Register
abbrev ForwardState (parameterWidth elementWidth : ℕ) :=
  Sum Unit (Sum (StandardFiniteTable.State parameterWidth elementWidth elementWidth)
    (Sum (Fin (elementWidth + 1)) Unit))

variable {parameterWidth elementWidth : ℕ}

def arrayTapes : Bool ↪ Fin 3 := twoTapes 1 2 (by decide)

noncomputable def advance (elementWidth : ℕ) : Machine Alphabet (Fin (elementWidth + 1)) :=
  MultiTape.wire arrayTapes (Move.machine elementWidth .right)

noncomputable def forward
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth) :
    Machine Alphabet (ForwardState parameterWidth elementWidth)
  | .inl _, symbols =>
    if elementWidth = 0 ∨ symbols 1 = 0 then
      some (.inr (.inr (.inr ())), stationary symbols)
    else some (.inr (.inl StandardFiniteTable.entry), stationary symbols)
  | .inr (.inl state), symbols => match StandardFiniteTable.machine table state symbols with
    | some (next, actions) => some (.inr (.inl next), actions)
    | none => some (.inr (.inr (.inl (Fin.last elementWidth))), stationary symbols)
  | .inr (.inr (.inl remaining)), symbols => match advance elementWidth remaining symbols with
    | some (next, actions) => some (.inr (.inr (.inl next)), actions)
    | none => some (.inl (), stationary symbols)
  | .inr (.inr (.inr _)), _ => none

def forwardEntry : ForwardState parameterWidth elementWidth := .inl ()
def forwardExit : ForwardState parameterWidth elementWidth := .inr (.inr (.inr ()))

noncomputable def restore (name : Fin 3) :
    Machine Alphabet (Sum (Fin 2) (Fin 3)) :=
  MultiTape.wire (oneTape name) StandardHead.BlankReturn.fromEnd

abbrev State (parameterWidth elementWidth : ℕ) :=
  Sum (ForwardState parameterWidth elementWidth)
    (Sum (Sum (Fin 2) (Fin 3)) (Sum (Fin 2) (Fin 3)))

noncomputable def machine
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth) :
    Machine Alphabet (State parameterWidth elementWidth) :=
  MultiTape.sequence (forward table)
    (MultiTape.sequence (restore 1) (restore 2) (.inl 1)) (.inl (.inl 1))

noncomputable instance stateFintype (parameterWidth elementWidth : ℕ) :
    Fintype (State parameterWidth elementWidth) := by
  letI : Fintype (StandardFiniteTable.State parameterWidth elementWidth elementWidth) := inferInstance
  letI : Fintype (ForwardState parameterWidth elementWidth) := inferInstance
  exact inferInstanceAs (Fintype (Sum _ _))

def entry : State parameterWidth elementWidth := .inl forwardEntry
def exit : State parameterWidth elementWidth := .inr (.inr (.inr 2))

@[simp] theorem halt
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (symbols : Symbols Alphabet) : machine table exit symbols = none := by
  simp [machine, exit, restore, MultiTape.sequence, MultiTape.wire,
    StandardHead.BlankReturn.fromEnd, StandardHead.BlankReturn.machine]

def bits (values : List (Register elementWidth)) : List Bool := values.flatMap List.ofFn

def mapped (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (parameter : Register parameterWidth) (values : List (Register elementWidth)) :
    List (Register elementWidth) :=
  values.map (fun value index => (table parameter value).getLsbD index.val)

@[simp] theorem bits_length (values : List (Register elementWidth)) :
    (bits values).length = values.length * elementWidth := by
  induction values <;> simp_all [bits, Nat.add_mul, Nat.add_comm]

def widths (parameterWidth arrayWidth : ℕ) (name : Fin 3) : ℕ :=
  if name = 0 then parameterWidth else arrayWidth

def readOnly : Fin 3 → Bool := StandardFiniteTable.readOnly

def position (offset : ℤ) (name : Fin 3) : ℤ := if name = 0 then 0 else offset

def frame (parameter : Register parameterWidth) (before after : List Bool)
    (written : List Bool) (old : List Symbol) : Tapes Alphabet := fun name =>
  if name = 0 then buffer (word (List.ofFn parameter))
  else if name = 1 then Turing.Tape.mk' (Turing.ListBlank.mk (word before.reverse ++ [0]))
    (Turing.ListBlank.mk (word after ++ [0]))
  else Turing.Tape.mk' (Turing.ListBlank.mk (word written.reverse ++ [0]))
    (Turing.ListBlank.mk (old ++ [0]))

/-- The finite-table call transforms one block without changing any neighbors. -/
theorem block_runs
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (parameter : Register parameterWidth) (value : Register elementWidth)
    (before after written : List Bool) (old rest : List Symbol)
    (oldLength : old.length = elementWidth)
    (arrayWidth : ℕ) (fits : before.length + elementWidth ≤ arrayWidth) :
    let result := List.ofFn (fun index : Fin elementWidth =>
      (table parameter value).getLsbD index.val)
    Runs (widths parameterWidth arrayWidth) readOnly (StandardFiniteTable.machine table)
      (2 * (parameterWidth + elementWidth + elementWidth) + 6)
      StandardFiniteTable.entry (position before.length)
      (frame parameter before (List.ofFn value ++ after) written (old ++ rest))
      StandardFiniteTable.exit (position before.length)
      (frame parameter before (List.ofFn value ++ after) written (word result ++ rest)) := by
  intro result
  let left : Fin 3 → List Symbol := fun name =>
    if name = 0 then [0] else if name = 1 then word before.reverse ++ [0]
    else word written.reverse ++ [0]
  let right : Fin 3 → List Symbol := fun name =>
    if name = 0 then [0] else if name = 1 then word after ++ [0] else rest ++ [0]
  have trace := StandardFiniteTable.runsWithContext table (List.ofFn parameter) (List.ofFn value)
    (by simp) (by simp) old oldLength left right
  have registerParameter : (fun index : Fin parameterWidth =>
      ((List.ofFn parameter)[index.val]?).getD false) = parameter := by
    funext index
    simp
  have registerValue : (fun index : Fin elementWidth =>
      ((List.ofFn value)[index.val]?).getD false) = value := by
    funext index
    simp
  dsimp only at trace
  rw [registerParameter, registerValue] at trace
  have enlarged := trace.regions (widths parameterWidth arrayWidth) (position before.length) (by
    intro name writable
    fin_cases name
    · contradiction
    · contradiction
    · simpa [position, StandardFiniteTable.widths, widths] using
        And.intro (Int.natCast_nonneg before.length) (show (before.length : ℤ) + elementWidth ≤ arrayWidth by omega))
  convert enlarged using 1
  · funext name
    fin_cases name <;> rfl
  · funext name
    simp [position]
  · funext name
    fin_cases name <;>
      simp [frame, StandardFiniteTable.frameWithContext, left, right,
        buffer_padding, word, List.map_append, List.append_assoc]
  · funext name
    simp [position]
  · funext name
    fin_cases name <;>
      simp [frame, StandardFiniteTable.frameWithContext, left, right,
        buffer_padding, word, result, List.map_append, List.append_assoc]

/-- Move both array heads to the next scalar, leaving the parameter at its start. -/
theorem advance_runs (parameter : Register parameterWidth) (source result after : List Bool)
    (sourceLength : source.length = elementWidth) (resultLength : result.length = elementWidth)
    (before written : List Bool) (old : List Symbol) (arrayWidth : ℕ) :
    Runs (widths parameterWidth arrayWidth) readOnly (advance elementWidth) elementWidth
      (Fin.last elementWidth) (position before.length)
      (frame parameter before (source ++ after) written (word result ++ old))
      0 (position (before.length + elementWidth))
      (frame parameter (before ++ source) after (written ++ result) old) := by
  let initial := frame parameter before (source ++ after) written (word result ++ old)
  let final := frame parameter (before ++ source) after (written ++ result) old
  have trace := StandardHead.move_runs elementWidth .right (fun _ : Bool => arrayWidth)
    (fun _ => true) (fun _ => (before.length : ℤ)) (fun name => initial (arrayTapes name))
  have wired := trace.wire arrayTapes (widths parameterWidth arrayWidth) readOnly
    (by intro name; cases name <;> rfl) (by intro name premise; rfl)
    initial (position before.length)
  have initialPosition : install arrayTapes (fun _ : Bool => (before.length : ℤ))
      (position before.length) = position before.length := by
    have same : (fun _ : Bool => (before.length : ℤ)) =
        fun name => position before.length (arrayTapes name) := by
      funext name
      cases name <;> rfl
    rw [same, install_self]
  have finalPosition : install arrayTapes
      (fun _ : Bool => (before.length : ℤ) + elementWidth * displacement (some Turing.Dir.right))
      (position before.length) = position (before.length + elementWidth) := by
    funext name
    fin_cases name
    · rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩; cases localName <;> cases equal)]
      rfl
    · change install arrayTapes _ _ (arrayTapes false) = _
      simp [position, displacement]
    · change install arrayTapes _ _ (arrayTapes true) = _
      simp [position, displacement]
  have movedSource : (Turing.Tape.move Turing.Dir.right)^[elementWidth] (initial 1) = final 1 := by
    have trace := Move.right_list (word source) (word before.reverse ++ [0]) (word after ++ [0])
    simpa [initial, final, frame, word, List.map_append, List.map_reverse,
      List.reverse_append, List.append_assoc, sourceLength] using trace
  have movedResult : (Turing.Tape.move Turing.Dir.right)^[elementWidth] (initial 2) = final 2 := by
    have trace := Move.right_list (word result) (word written.reverse ++ [0]) (old ++ [0])
    simpa [initial, final, frame, word, List.map_append, List.map_reverse,
      List.reverse_append, List.append_assoc, resultLength] using trace
  have finalTapes : install arrayTapes
      (fun name => (Turing.Tape.move Turing.Dir.right)^[elementWidth] (initial (arrayTapes name)))
      initial = final := by
    funext name
    fin_cases name
    · rw [install_outside _ _ _ _ (by
        rintro ⟨localName, equal⟩; cases localName <;> cases equal)]
      rfl
    · change install arrayTapes _ _ (arrayTapes false) = _
      rw [install_at]
      exact movedSource
    · change install arrayTapes _ _ (arrayTapes true) = _
      rw [install_at]
      exact movedResult
  rw [install_self, initialPosition, finalPosition, finalTapes] at wired
  exact wired

private theorem stationary_run
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (arrayWidth : ℕ) (offset : ℤ) (tapes : Tapes Alphabet)
    (state next : ForwardState parameterWidth elementWidth)
    (instruction : forward table state (MultiTape.read tapes) = some (next, stationary (MultiTape.read tapes))) :
    Runs (widths parameterWidth arrayWidth) readOnly (forward table) 1
      state (position offset) tapes next (position offset) tapes := by
  apply Runs.next instruction (by intro name premise; rfl)
  simpa only [act_stationary, stationary, displacement, add_zero] using
    Runs.zero (machine := forward table) next (position offset) tapes

/-- Traverse a nonzero-width array; each iteration performs one finite table
call and advances by the specialization-fixed element width. -/
theorem forward_runs
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (parameter : Register parameterWidth) (positive : 0 < elementWidth)
    (values : List (Register elementWidth)) (before written : List Bool) (old : List Symbol)
    (writtenLength : written.length = before.length)
    (oldLength : old.length = (bits values).length)
    (arrayWidth : ℕ) (fits : before.length + (bits values).length = arrayWidth) :
    Runs (widths parameterWidth arrayWidth) readOnly (forward table)
      (values.length * (2 * (parameterWidth + elementWidth + elementWidth) + elementWidth + 9) + 1)
      forwardEntry (position before.length) (frame parameter before (bits values) written old)
      forwardExit (position arrayWidth)
      (frame parameter (before ++ bits values) [] (written ++ bits (mapped table parameter values)) []) := by
  induction values generalizing before written old with
  | nil =>
    have empty : old = [] := List.eq_nil_of_length_eq_zero oldLength
    subst old
    have size : before.length = arrayWidth := by simpa [bits] using fits
    simpa [bits, mapped, List.append_nil, size, forwardEntry, forwardExit] using
      stationary_run table arrayWidth before.length (frame parameter before [] written [])
        forwardEntry forwardExit (by simp [forward, forwardEntry, forwardExit, frame, MultiTape.read, word])
  | cons value values hypothesis =>
    let block : List Bool := List.ofFn value
    let result : List Bool := List.ofFn (fun index : Fin elementWidth =>
      (table parameter value).getLsbD index.val)
    have blockLength : block.length = elementWidth := by simp [block]
    have resultLength : result.length = elementWidth := by simp [result]
    have oldBound : elementWidth ≤ old.length := by simp [bits] at oldLength; omega
    have oldBlockLength : (old.take elementWidth).length = elementWidth := by simp [oldBound]
    have oldRestLength : (old.drop elementWidth).length = (bits values).length := by
      simp only [List.length_drop]
      simp [bits] at oldLength ⊢
      omega
    have nextWritten : (written ++ result).length = (before ++ block).length := by
      simp [writtenLength, blockLength, resultLength]
    have nextFits : (before ++ block).length + (bits values).length = arrayWidth := by
      simp [bits] at fits
      simp [blockLength]
      omega
    have selected : (frame parameter before (bits (value :: values)) written old 1).head ≠ 0 := by
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
      have nonblank : data (value 0) ≠ 0 := by cases value 0 <;> decide
      simpa [frame, bits, word, List.ofFn_succ] using nonblank
    let initial := frame parameter before (bits (value :: values)) written old
    have choose := stationary_run table arrayWidth before.length initial forwardEntry
      (.inr (.inl StandardFiniteTable.entry)) (by
        simp [forward, forwardEntry, initial, MultiTape.read, selected, positive.ne'])
    have tableTrace := (block_runs table parameter value before (bits values) written
      (old.take elementWidth) (old.drop elementWidth) oldBlockLength arrayWidth
      (by simp [bits] at fits; omega)).rename
      (fun state => .inr (.inl state)) (target := forward table) (by
        intro state symbols next actions instruction
        simp [forward, instruction])
    have writtenFrame : frame parameter before (bits (value :: values)) written old =
        frame parameter before (List.ofFn value ++ bits values) written
          (old.take elementWidth ++ old.drop elementWidth) := by simp [bits]
    rw [← writtenFrame] at tableTrace
    let patched := frame parameter before (block ++ bits values) written
      (word result ++ old.drop elementWidth)
    have toAdvance := stationary_run table arrayWidth before.length patched
      (.inr (.inl StandardFiniteTable.exit)) (.inr (.inr (.inl (Fin.last elementWidth))))
      (by simp [forward, StandardFiniteTable.machine, StandardFiniteTable.exit])
    have moved := (advance_runs parameter block result (bits values) blockLength resultLength
      before written (old.drop elementWidth) arrayWidth).rename
      (fun state => .inr (.inr (.inl state))) (target := forward table) (by
        intro state symbols next actions instruction
        simp [forward, instruction])
    let advanced := frame parameter (before ++ block) (bits values) (written ++ result)
      (old.drop elementWidth)
    have toCheck := stationary_run table arrayWidth (before.length + elementWidth) advanced
      (.inr (.inr (.inl 0))) forwardEntry (by simp [forward, advance, MultiTape.wire, Move.machine, forwardEntry])
    have rest := hypothesis (before ++ block) (written ++ result) (old.drop elementWidth)
      nextWritten oldRestLength nextFits
    simp only [List.length_append, blockLength, Nat.cast_add] at rest
    have complete := choose.trans (tableTrace.trans (toAdvance.trans (moved.trans (toCheck.trans rest))))
    convert complete using 1
    · simp only [List.length_cons]
      ring
    · simp [bits, mapped, block, result, List.append_assoc]

/-- Zero-bit scalar domains need no traversal, regardless of array length. -/
theorem forward_runs_total
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (parameter : Register parameterWidth) (values : List (Register elementWidth))
    (old : List Symbol) (oldLength : old.length = (bits values).length) :
    ∃ ticks, ticks ≤ values.length *
        (2 * (parameterWidth + elementWidth + elementWidth) + elementWidth + 9) + 1 ∧
      Runs (widths parameterWidth (bits values).length) readOnly (forward table) ticks
        forwardEntry (position 0) (frame parameter [] (bits values) [] old)
        forwardExit (position (bits values).length)
        (frame parameter (bits values) [] (bits (mapped table parameter values)) []) := by
  by_cases zero : elementWidth = 0
  · have sourceEmpty : bits values = [] := List.eq_nil_of_length_eq_zero (by simp [zero])
    have targetEmpty : bits (mapped table parameter values) = [] :=
      List.eq_nil_of_length_eq_zero (by simp [zero])
    have oldEmpty : old = [] := List.eq_nil_of_length_eq_zero (by simpa [sourceEmpty] using oldLength)
    refine ⟨1, by omega, ?_⟩
    rw [sourceEmpty, targetEmpty, oldEmpty]
    exact stationary_run table 0 0 (frame parameter [] [] [] []) forwardEntry forwardExit
      (by simp [forward, zero, forwardEntry, forwardExit])
  · refine ⟨_, le_rfl, ?_⟩
    simpa using forward_runs table parameter (Nat.pos_of_ne_zero zero) values [] [] old rfl oldLength
      (bits values).length (by simp)

/-- Complete array traversal writes through arbitrary output contents and
restores all three heads, including for empty and zero-bit arrays. -/
theorem runs
    (table : Register parameterWidth → Register elementWidth → BitVec elementWidth)
    (parameter : Register parameterWidth) (values : List (Register elementWidth))
    (old : List Symbol) (oldLength : old.length = (bits values).length) :
    ∃ ticks, ticks ≤ values.length *
        (2 * (parameterWidth + elementWidth + elementWidth) + elementWidth + 9) +
          2 * (bits values).length + 9 ∧
      Runs (widths parameterWidth (bits values).length) readOnly (machine table) ticks
        entry (fun _ => 0) (frame parameter [] (bits values) [] old)
        exit (fun _ => 0)
        (StandardFiniteTable.frame (List.ofFn parameter) (bits values)
          (word (bits (mapped table parameter values)))) := by
  obtain ⟨forwardTicks, forwardCost, forwardTrace⟩ := forward_runs_total table parameter values old oldLength
  let ending := frame parameter (bits values) [] (bits (mapped table parameter values)) []
  let middle := Function.update ending 1 (buffer (word (bits values)))
  let final := Function.update middle 2 (buffer (word (bits (mapped table parameter values))))
  let middlePosition := Function.update (position (bits values).length) 1 0
  have sourceTrace := (StandardHead.BlankReturn.fromEnd_runs (bits values)).wire
    (oneTape (1 : Fin 3)) (widths parameterWidth (bits values).length) readOnly
    (by intro name; rfl) (by intro name premise; rfl) ending (position (bits values).length)
  have sourceInitial : (Binary.tape (word (bits values).reverse ++ [0]) [0]) () = ending 1 := by
    simp [ending, frame, word, Binary.tape, List.map_reverse]
  simp only [install_one] at sourceTrace
  rw [sourceInitial, Function.update_eq_self] at sourceTrace
  have sourcePosition : Function.update (position (bits values).length) 1
      ((bits values).length : ℤ) = position (bits values).length := by
    funext name
    fin_cases name <;> simp [position]
  rw [sourcePosition] at sourceTrace
  have targetLength : (bits (mapped table parameter values)).length = (bits values).length := by
    simp [mapped]
  have targetTrace := (StandardHead.BlankReturn.fromEnd_runs (bits (mapped table parameter values))).wire
    (oneTape (2 : Fin 3)) (widths parameterWidth (bits values).length) readOnly
    (by intro name; exact targetLength.symm) (by intro name premise; rfl) middle middlePosition
  have targetInitial : (Binary.tape (word (bits (mapped table parameter values)).reverse ++ [0]) [0]) () = middle 2 := by
    simp [middle, ending, frame, word, Binary.tape, List.map_reverse]
  simp only [install_one] at targetTrace
  rw [targetInitial, Function.update_eq_self] at targetTrace
  have targetPosition : Function.update middlePosition 2
      ((bits (mapped table parameter values)).length : ℤ) = middlePosition := by
    have same : ((bits (mapped table parameter values)).length : ℤ) = middlePosition 2 := by
      simp [middlePosition, position, targetLength]
    rw [same, Function.update_eq_self]
  rw [targetPosition] at targetTrace
  have restoredPosition : Function.update middlePosition 2 (0 : ℤ) = fun _ => 0 := by
    funext name
    fin_cases name <;> simp [middlePosition, position]
  rw [restoredPosition] at targetTrace
  have completeRestore := sourceTrace.sequence (restore 2) (.inl 1)
    (by intro symbols; simp [MultiTape.wire, StandardHead.BlankReturn.fromEnd,
      MultiTape.sequence, StandardHead.BlankReturn.machine]) targetTrace
  have complete := forwardTrace.sequence
    (MultiTape.sequence (restore 1) (restore 2) (.inl 1)) (.inl (.inl 1))
    (by intro symbols; simp [forward, forwardExit]) completeRestore
  refine ⟨forwardTicks + (((bits values).length + 3) +
    ((bits (mapped table parameter values)).length + 3) + 1) + 1, ?_, ?_⟩
  · simp only [targetLength]
    omega
  · have finalEqual : final = StandardFiniteTable.frame (List.ofFn parameter) (bits values)
        (word (bits (mapped table parameter values))) := by
      funext name
      fin_cases name <;> simp [final, middle, ending, frame, StandardFiniteTable.frame]
    dsimp only [final] at finalEqual
    rw [finalEqual] at complete
    have zeroPosition : position (0 : ℤ) = fun _ => 0 := by
      funext name
      simp [position]
    rw [zeroPosition] at complete
    exact complete

end Polytime2.StandardArrayMap
