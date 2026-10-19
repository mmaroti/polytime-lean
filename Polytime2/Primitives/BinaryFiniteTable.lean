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

import Polytime2.Primitives.FiniteTable

/-! # Binary specialization of finite-family tables

Array block maps retain their three-tape interface. All reading, writing, and
controller execution are supplied by the heterogeneous finite-family table.
-/

namespace Polytime2.StandardFiniteTable

open MultiTape CallingConvention
open Binary (Symbol word)

abbrev Alphabet := CallingConvention.Alphabet (Fin 3)
abbrev Register := StandardFixedRead.Memory

def inputWidths (first second : ℕ) (name : Fin 2) : ℕ := if name = 0 then first else second
abbrev State (first second output : ℕ) := FiniteTable.State (inputWidths first second) (fun _ : Fin 1 => output)

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

def inputTapes : Fin 2 ↪ Fin 3 :=
  ⟨(fun name => ⟨name.val, by omega⟩), by intro first second equal; exact Fin.ext (congrArg (fun name : Fin 3 => name.val) equal)⟩
def resultTapes : Fin 1 ↪ Fin 3 := ⟨(fun _ => 2), by intro first second equal; exact Subsingleton.elim _ _⟩

noncomputable def machine (table : Register firstWidth → Register secondWidth → BitVec outputWidth) :
    Machine Alphabet (State firstWidth secondWidth outputWidth) :=
  FiniteTable.machine (inputWidths firstWidth secondWidth) (fun _ : Fin 1 => outputWidth)
    inputTapes resultTapes (fun values _ => table (values 0) (values 1))

def entry : State firstWidth secondWidth outputWidth := FiniteTable.entry _ _
def exit : State firstWidth secondWidth outputWidth := none

/-- Different input and output widths, arbitrary old output, and neighboring
array symbols all use the same generic execution theorem. -/
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
  obtain ⟨final, trace, written, outside⟩ := FiniteTable.runsWithContext
    (inputWidths firstWidth secondWidth) (fun _ : Fin 1 => outputWidth) inputTapes resultTapes
    (fun values _ => table (values 0) (values 1))
    (fun name => if name = 0 then first else second) (by intro name; fin_cases name <;> assumption)
    (fun _ => old) (fun _ => oldLength) (widths firstWidth secondWidth outputWidth) readOnly
    (by intro name; fin_cases name <;> rfl) (by intro name; fin_cases name; rfl)
    (by intro name; fin_cases name; rfl) left right (frameWithContext first second old left right)
    (by intro name; fin_cases name <;> rfl) (by intro name; fin_cases name; rfl)
  have finalEq : final = frameWithContext first second (word result) left right := by
    funext name
    fin_cases name
    · exact outside 0 (by rintro ⟨name, equal⟩; fin_cases name; cases equal)
    · exact outside 1 (by rintro ⟨name, equal⟩; fin_cases name; cases equal)
    · exact written 0
  have costEq : FiniteTable.cost (inputWidths firstWidth secondWidth) +
      FiniteTable.cost (fun _ : Fin 1 => outputWidth) = 2 * (firstWidth + secondWidth + outputWidth) + 6 := by
    simp [FiniteTable.cost, Fin.sum_univ_succ, inputWidths]; omega
  rw [costEq, finalEq] at trace
  exact trace

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

end Polytime2.StandardFiniteTable
