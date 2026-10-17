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

import Polytime2.StandardMatrixEntry
import Polytime2.FixedArrayUpdate

/-! # Separate-output matrix entry replacement

The row, column, source matrix, and replacement scalar are immutable inputs.
Address arithmetic reads the unary dimensions and shares counters with update.
-/

namespace Polytime2.StandardMatrixReplace

open MultiTape CallingConvention
open Binary (Symbol word value data)

abbrev TapeName := Sum StandardMatrixAddress.TapeName (Fin 3)
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev State (elementWidth : ℕ) := Sum StandardMatrixAddress.State (FixedArrayUpdate.State elementWidth)

noncomputable def domains (element : EncodedDomain.{0, 0} (Fin 3)) : TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardMatrixAddress.domains name
  | .inr name => if name = 1 then element else element.arrayOfLength StandardMatrixEntry.length

def readOnly : TapeName → Bool
  | .inl name => StandardMatrixAddress.readOnly name
  | .inr name => decide (name ≠ 2)

def sizeTapes : Fin 3 ↪ TapeName := StandardMatrixAddress.sizeTapes.trans Function.Embedding.inl

def updateWiring : Fin 7 ↪ TapeName :=
  ⟨(fun name => match name.val with
    | 0 => .inl (.inr 7) | 1 => .inr 0 | 2 => .inr 1 | 3 => .inr 2
    | 4 => .inl (.inr 0) | 5 => .inl (.inr 2) | _ => .inl (.inr 4)), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem updateWiring_apply (name : Fin 7) : updateWiring name =
    (match name.val with
    | 0 => .inl (.inr 7) | 1 => .inr 0 | 2 => .inr 1 | 3 => .inr 2
    | 4 => .inl (.inr 0) | 5 => .inl (.inr 2) | _ => .inl (.inr 4)) := rfl

noncomputable def address : Machine Alphabet StandardMatrixAddress.State :=
  MultiTape.wire Function.Embedding.inl StandardMatrixAddress.machine
noncomputable def update (elementWidth : ℕ) : Machine Alphabet (FixedArrayUpdate.State elementWidth) :=
  MultiTape.wire updateWiring (FixedArrayUpdate.machine elementWidth)
noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  MultiTape.sequence address (update elementWidth) (FixedArrayUpdate.entry elementWidth)

def entry (elementWidth : ℕ) : State elementWidth := .inl StandardMatrixAddress.entry
def exit (elementWidth : ℕ) : State elementWidth := .inr (FixedArrayUpdate.exit elementWidth)

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit, update, MultiTape.sequence, MultiTape.wire]

def frame (sizes : Fin 3 → ℕ) (row column : List Bool) (array result : Turing.Tape Symbol)
    (element product shifted next columns addressBits : List Symbol) (multiplyFlag addFlag : Symbol) : Tapes Alphabet
  | .inl name => StandardMatrixAddress.frame sizes row column product shifted next columns addressBits multiplyFlag addFlag name
  | .inr name => if name = 0 then array else if name = 1 then buffer element else result

/-- The full source array is copied before its selected block is overwritten.
The output region may initially contain arbitrary symbols, including blanks. -/
theorem runs (element : EncodedDomain.{0, 0} (Fin 3)) (sizes : Fin 3 → ℕ)
    (row column : List Bool) (rowLength : row.length = sizes 0) (columnLength : column.length = sizes 0)
    (array : (element.arrayOfLength StandardMatrixEntry.length).Carrier sizes)
    (replacement : element.Carrier sizes)
    (oldOutput oldProduct oldShifted oldNext oldColumns oldAddress : List Symbol)
    (outputLength : oldOutput.length = (element.arrayOfLength StandardMatrixEntry.length).width sizes)
    (productLength : oldProduct.length = sizes 0) (shiftedLength : oldShifted.length = sizes 0)
    (nextLength : oldNext.length = sizes 0) (columnsLength : oldColumns.length = sizes 0)
    (addressLength : oldAddress.length = sizes 0) (multiplyFlag addFlag : Symbol)
    (columnsFit : sizes 2 < 2 ^ sizes 0)
    (addressFit : value row * sizes 2 + value column < 2 ^ sizes 0)
    (within : value row * sizes 2 + value column < MvPolynomial.eval sizes StandardMatrixEntry.length) :
    ∃ (ticks : ℕ) (addressBits : List Bool),
      addressBits.length = sizes 0 ∧ value addressBits = value row * sizes 2 + value column ∧
      ticks ≤ sizes 2 * (4 * sizes 0 + 8) + sizes 0 * (6 * sizes 0 + 14) + 12 * sizes 0 + 30 +
        MvPolynomial.eval sizes StandardMatrixEntry.length * (6 * sizes 0 + 4 * element.width sizes + 11) +
        6 * sizes 0 + 2 * element.width sizes + 18 ∧
      Runs (fun name => (domains element name).width sizes) readOnly (machine (element.width sizes)) ticks
        (entry (element.width sizes)) (fun _ => 0)
        (frame sizes row column (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes array)
          (buffer oldOutput) (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          oldProduct oldShifted oldNext oldColumns oldAddress multiplyFlag addFlag)
        (exit (element.width sizes)) (fun _ => 0)
        (frame sizes row column (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes array)
          (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes
            (Function.update array ⟨value row * sizes 2 + value column, within⟩ replacement))
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement)))
          (word (List.replicate (sizes 0) false)) (word (List.replicate (sizes 0) false))
          (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
          (word addressBits) (data false) (data false)) := by
  obtain ⟨scratch, scratchLength, addressTrace⟩ := StandardMatrixAddress.runs sizes row column rowLength columnLength
    oldProduct oldShifted oldNext oldColumns oldAddress productLength shiftedLength nextLength columnsLength
    addressLength multiplyFlag addFlag columnsFit addressFit
  let productBits := MultiplyAdd.product row (StandardMatrixAddress.columnBits sizes) (word scratch) oldNext multiplyFlag
  let addressBits := MultiplyAdd.result row (StandardMatrixAddress.columnBits sizes) column (word scratch) oldNext multiplyFlag
  have scratchFits : (word scratch).length = row.length := by simp [word, scratchLength, rowLength]
  have nextFits : oldNext.length = row.length := nextLength.trans rowLength.symm
  have sameLength : column.length = row.length := columnLength.trans rowLength.symm
  have productBitsLength : productBits.length = sizes 0 :=
    (MultiplyAdd.product_length row (StandardMatrixAddress.columnBits sizes) (word scratch) oldNext multiplyFlag
      scratchFits nextFits).trans rowLength
  have addressBitsLength : addressBits.length = sizes 0 :=
    (MultiplyAdd.result_length row (StandardMatrixAddress.columnBits sizes) column (word scratch) oldNext multiplyFlag
      sameLength scratchFits nextFits).trans rowLength
  have addressValue : value addressBits = value row * sizes 2 + value column := by
    have fits : value row * value (StandardMatrixAddress.columnBits sizes) + value column < 2 ^ row.length := by
      rwa [StandardMatrixAddress.columnBits_value sizes columnsFit, rowLength]
    simpa only [StandardMatrixAddress.columnBits_value sizes columnsFit] using
      MultiplyAdd.result_value row (StandardMatrixAddress.columnBits sizes) column (word scratch) oldNext multiplyFlag
        sameLength scratchFits nextFits fits
  have inRange : value addressBits < MvPolynomial.eval sizes StandardMatrixEntry.length := by rwa [addressValue]
  let replacementBits := word (EncodedDomain.ArrayEncoding.bits (element.encode sizes replacement))
  let middle := frame sizes row column (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes array)
    (buffer oldOutput) replacementBits (word productBits) (word (List.replicate (sizes 0) false))
    (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
    (word addressBits) (data false) (data false)
  have first := addressTrace.wire_of_eq Function.Embedding.inl
    (fun name => (domains element name).width sizes) readOnly
    (by intro name; rfl) (by intro name premise; exact premise)
    (frame sizes row column (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes array)
      (buffer oldOutput) replacementBits oldProduct oldShifted oldNext oldColumns oldAddress multiplyFlag addFlag) middle
    (by intro name; rfl) (by intro name; rfl)
    (by intro name outside; cases name with
      | inl name => exact False.elim (outside ⟨name, rfl⟩)
      | inr name => fin_cases name <;> rfl)
  obtain ⟨ticks, cost, localTrace⟩ := FixedArrayUpdate.encoded_runsOfLength element StandardMatrixEntry.length
    sizes addressBits inRange array replacement oldOutput (word productBits)
    (word (List.replicate (sizes 0) false)) outputLength
    (by simp [word, productBitsLength, addressBitsLength]) (by simp [word, addressBitsLength]) (data false)
  let final := frame sizes row column (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes array)
    (encoded (element.arrayOfLength StandardMatrixEntry.length) sizes (Function.update array ⟨value addressBits, inRange⟩ replacement))
    replacementBits (word (List.replicate (sizes 0) false)) (word (List.replicate (sizes 0) false))
    (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
    (word addressBits) (data false) (data false)
  have second := localTrace.wire_of_eq updateWiring
    (fun name => (domains element name).width sizes) readOnly
    (by
      intro name
      simp only [updateWiring_apply]
      fin_cases name <;> norm_num [domains, StandardMatrixAddress.domains,
        FixedArrayUpdate.widths, addressBitsLength, EncodedDomain.binaryNaturals,
        EncodedDomain.booleans, EncodedDomain.fixed])
    (by
      intro name premise
      simp only [updateWiring_apply] at premise
      fin_cases name <;> norm_num [readOnly, StandardMatrixAddress.readOnly,
        FixedArrayUpdate.readOnly] at *)
    middle final (by intro name; fin_cases name <;> rfl)
    (by
      intro name
      fin_cases name
      · rfl
      · rfl
      · rfl
      · rfl
      · change buffer (word (List.replicate (sizes 0) false)) = buffer (word (List.replicate addressBits.length false))
        rw [addressBitsLength]
      · change buffer (word (List.replicate (sizes 0) false)) = buffer (word (List.replicate addressBits.length false))
        rw [addressBitsLength]
      · rfl)
    (by
      intro name outside
      cases name with
      | inl name =>
        cases name with
        | inl parameter => rfl
        | inr name =>
          fin_cases name
          · exact False.elim (outside ⟨4, rfl⟩)
          · rfl
          · exact False.elim (outside ⟨5, rfl⟩)
          · rfl
          · exact False.elim (outside ⟨6, rfl⟩)
          · rfl
          · rfl
          · rfl
          · rfl
      | inr name =>
        fin_cases name
        · exact False.elim (outside ⟨1, rfl⟩)
        · exact False.elim (outside ⟨2, rfl⟩)
        · exact False.elim (outside ⟨3, rfl⟩))
  have complete := first.sequence (update (element.width sizes)) (FixedArrayUpdate.entry (element.width sizes))
    (by intro symbols; simp [MultiTape.wire]) second
  refine ⟨sizes 2 * (4 * sizes 0 + 8) + sizes 0 * (6 * sizes 0 + 14) +
    12 * sizes 0 + 29 + ticks + 1, addressBits, addressBitsLength, addressValue, ?_, ?_⟩
  · rw [addressBitsLength] at cost
    omega
  · have selected : (⟨value addressBits, inRange⟩ : Fin (MvPolynomial.eval sizes StandardMatrixEntry.length)) =
        ⟨value row * sizes 2 + value column, within⟩ := Fin.ext addressValue
    simpa only [final, selected, machine, address, entry, exit] using complete

end Polytime2.StandardMatrixReplace
