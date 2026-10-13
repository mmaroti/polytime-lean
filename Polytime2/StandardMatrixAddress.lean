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

import Polytime2.StandardSizeReadContract
import Polytime2.MultiplyAddContract

/-! # Binary matrix addresses derived from unary dimensions

Size names 0, 1, and 2 specify bit capacity, rows, and columns. The immutable
row and column indices are binary words. Column-size reading and multiply-add
reuse one scratch word, with a separate final address and canonical scratch.
-/

namespace Polytime2.StandardMatrixAddress

open MultiTape CallingConvention
open Binary (Symbol data word value)

abbrev TapeName := Sum (Fin 3) (Fin 9)
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev State := Sum StandardSizeRead.State MultiplyAdd.State

def domains : TapeName → EncodedDomain (Fin 3)
  | .inl parameter => EncodedDomain.unary parameter
  | .inr name => if name = 4 ∨ name = 8 then EncodedDomain.booleans
      else EncodedDomain.binaryNaturals 0

def readOnly : TapeName → Bool
  | .inl _ => true
  | .inr name => decide (name = 1 ∨ name = 6)

def sizeTapes : Fin 3 ↪ TapeName :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def frame (sizes : Fin 3 → ℕ) (row column : List Bool)
    (product shifted next columns result : List Symbol) (multiplyFlag addFlag : Symbol) : Tapes Alphabet
  | .inl parameter => unary (sizes parameter)
  | .inr name => if name = 0 then buffer product else if name = 1 then buffer (word row)
      else if name = 2 then buffer shifted else if name = 3 then buffer next
      else if name = 4 then buffer [multiplyFlag] else if name = 5 then buffer columns
      else if name = 6 then buffer (word column) else if name = 7 then buffer result else buffer [addFlag]

def sizeWiring : Fin 4 ↪ TapeName :=
  ⟨(fun name => match name.val with
    | 0 => .inl 2 | 1 => .inl 0 | 2 => .inr 5 | _ => .inr 2), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

def arithmeticWiring : Fin 9 ↪ TapeName :=
  ⟨Sum.inr, by intro first second equal; cases equal; rfl⟩

noncomputable def readColumns : Machine Alphabet StandardSizeRead.State :=
  MultiTape.wire sizeWiring StandardSizeRead.machine
noncomputable def arithmetic : Machine Alphabet MultiplyAdd.State :=
  MultiTape.wire arithmeticWiring MultiplyAdd.machine
noncomputable def machine : Machine Alphabet State :=
  MultiTape.sequence readColumns arithmetic MultiplyAdd.entry

def entry : State := .inl StandardSizeRead.entry
def exit : State := .inr MultiplyAdd.exit

@[simp] theorem halt (symbols : Symbols Alphabet) : machine exit symbols = none := by
  simp [machine, exit, arithmetic, MultiTape.sequence, MultiTape.wire]

def columnBits (sizes : Fin 3 → ℕ) : List Bool :=
  StandardSizeRead.advanceBits (sizes 2) (List.replicate (sizes 0) false)

@[simp] theorem columnBits_length (sizes : Fin 3 → ℕ) : (columnBits sizes).length = sizes 0 := by
  simp [columnBits]

theorem columnBits_value (sizes : Fin 3 → ℕ) (fits : sizes 2 < 2 ^ sizes 0) :
    value (columnBits sizes) = sizes 2 := by
  simp [columnBits, StandardSizeRead.advanceBits_value, Nat.mod_eq_of_lt fits]

/-- Reading the column dimension and address arithmetic share the shifted-word
scratch region. No output or temporary counter requires prefilled digits. -/
theorem runs (sizes : Fin 3 → ℕ) (row column : List Bool)
    (rowLength : row.length = sizes 0) (columnLength : column.length = sizes 0)
    (oldProduct oldShifted oldNext oldColumns oldResult : List Symbol)
    (productLength : oldProduct.length = sizes 0) (shiftedLength : oldShifted.length = sizes 0)
    (nextLength : oldNext.length = sizes 0) (columnsLength : oldColumns.length = sizes 0)
    (resultLength : oldResult.length = sizes 0) (multiplyFlag addFlag : Symbol)
    (columnsFit : sizes 2 < 2 ^ sizes 0)
    (addressFit : value row * sizes 2 + value column < 2 ^ sizes 0) :
    ∃ scratch : List Bool, scratch.length = sizes 0 ∧
      Runs (fun name => (domains name).width sizes) readOnly machine
        (sizes 2 * (4 * sizes 0 + 8) + sizes 0 * (6 * sizes 0 + 14) + 12 * sizes 0 + 29)
        entry (fun _ => 0)
        (frame sizes row column oldProduct oldShifted oldNext oldColumns oldResult multiplyFlag addFlag)
        exit (fun _ => 0)
        (frame sizes row column
          (word (MultiplyAdd.product row (columnBits sizes) (word scratch) oldNext multiplyFlag))
          (word (List.replicate (sizes 0) false)) (word (List.replicate (sizes 0) false))
          (word (columnBits sizes))
          (word (MultiplyAdd.result row (columnBits sizes) column (word scratch) oldNext multiplyFlag))
          (data false) (data false)) := by
  obtain ⟨scratch, scratchLength, sizeTrace⟩ := StandardSizeRead.runs (sizes 2) (sizes 0)
    oldColumns oldShifted columnsLength shiftedLength
  have readTrace := sizeTrace.wire_of_eq sizeWiring
    (fun name => (domains name).width sizes) readOnly
    (by intro name; fin_cases name <;> rfl)
    (by intro name premise; fin_cases name <;> exact premise)
    (frame sizes row column oldProduct oldShifted oldNext oldColumns oldResult multiplyFlag addFlag)
    (frame sizes row column oldProduct (word scratch) oldNext (word (columnBits sizes)) oldResult multiplyFlag addFlag)
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by
      intro name outside
      cases name with
      | inl parameter =>
        fin_cases parameter
        · exact False.elim (outside ⟨1, rfl⟩)
        · rfl
        · exact False.elim (outside ⟨0, rfl⟩)
      | inr name =>
        fin_cases name
        · rfl
        · rfl
        · exact False.elim (outside ⟨3, rfl⟩)
        · rfl
        · rfl
        · exact False.elim (outside ⟨2, rfl⟩)
        · rfl
        · rfl
        · rfl)
  have multiplyTrace := (MultiplyAdd.runs row (columnBits sizes) column
    (columnLength.trans rowLength.symm) oldProduct (word scratch) oldNext oldResult
    (productLength.trans rowLength.symm) (by simp [word, scratchLength, rowLength])
    (nextLength.trans rowLength.symm) (resultLength.trans rowLength.symm) multiplyFlag addFlag
    (by simpa [rowLength, columnBits_value sizes columnsFit] using addressFit)).wire_of_eq arithmeticWiring
    (fun name => (domains name).width sizes) readOnly
    (by
      intro name
      change (domains (.inr name)).width sizes = _
      fin_cases name <;> norm_num [domains, MultiplyAdd.widths, rowLength,
        EncodedDomain.binaryNaturals, EncodedDomain.booleans, EncodedDomain.fixed])
    (by
      intro name premise
      change readOnly (.inr name) = true at premise
      fin_cases name <;> simp_all [readOnly, MultiplyAdd.readOnly])
    (frame sizes row column oldProduct (word scratch) oldNext (word (columnBits sizes)) oldResult multiplyFlag addFlag)
    (frame sizes row column
      (word (MultiplyAdd.product row (columnBits sizes) (word scratch) oldNext multiplyFlag))
      (word (List.replicate row.length false)) (word (List.replicate row.length false)) (word (columnBits sizes))
      (word (MultiplyAdd.result row (columnBits sizes) column (word scratch) oldNext multiplyFlag))
      (data false) (data false))
    (by intro name; fin_cases name <;> rfl)
    (by intro name; fin_cases name <;> rfl)
    (by intro name outside; cases name with
      | inl parameter => rfl
      | inr name => exact False.elim (outside ⟨name, rfl⟩))
  rw [rowLength, columnBits_length] at multiplyTrace
  have complete := readTrace.sequence arithmetic MultiplyAdd.entry
    (by intro symbols; simp [MultiTape.wire]) multiplyTrace
  refine ⟨scratch, scratchLength, ?_⟩
  convert complete using 1 <;> first | rfl | ring

end Polytime2.StandardMatrixAddress
