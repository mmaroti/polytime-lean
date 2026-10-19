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

import Polytime2.Matrices.AddressContract
import Polytime2.Arrays.FixedLookup

/-! # Matrix entry lookup from separate row and column inputs

Address arithmetic and indexed lookup reuse two counter tapes and a flag.
The row-major array and both binary indices are immutable. Dimensions are
read from separate unary size tapes, rather than duplicated binary inputs.
-/

namespace Polytime2.StandardMatrixEntry

open MultiTape CallingConvention
open Binary (Symbol word value data)

abbrev TapeName := Sum StandardMatrixAddress.TapeName Bool
abbrev Alphabet := CallingConvention.Alphabet TapeName
abbrev State (elementWidth : ℕ) := Sum StandardMatrixAddress.State (FixedArrayLookup.State elementWidth)

noncomputable def length : MvPolynomial (Fin 3) ℕ := MvPolynomial.X 1 * MvPolynomial.X 2

noncomputable def domains (element : EncodedDomain.{0, 0} (Fin 3)) : TapeName → EncodedDomain.{0, 0} (Fin 3)
  | .inl name => StandardMatrixAddress.domains name
  | .inr false => element.arrayOfLength length
  | .inr true => element

def readOnly : TapeName → Bool
  | .inl name => StandardMatrixAddress.readOnly name
  | .inr name => !name

def sizeTapes : Fin 3 ↪ TapeName := StandardMatrixAddress.sizeTapes.trans Function.Embedding.inl

def lookupWiring : Fin 6 ↪ TapeName :=
  ⟨(fun name => match name.val with
    | 0 => .inl (.inr 7) | 1 => .inr false | 2 => .inr true
    | 3 => .inl (.inr 0) | 4 => .inl (.inr 2) | _ => .inl (.inr 4)), by
    intro first second equal
    fin_cases first <;> fin_cases second <;> simp_all⟩

@[simp] theorem lookupWiring_apply (name : Fin 6) : lookupWiring name =
    (match name.val with
    | 0 => .inl (.inr 7) | 1 => .inr false | 2 => .inr true
    | 3 => .inl (.inr 0) | 4 => .inl (.inr 2) | _ => .inl (.inr 4)) := rfl

noncomputable def address : Machine Alphabet StandardMatrixAddress.State :=
  MultiTape.wire Function.Embedding.inl StandardMatrixAddress.machine
noncomputable def lookup (elementWidth : ℕ) : Machine Alphabet (FixedArrayLookup.State elementWidth) :=
  MultiTape.wire lookupWiring (FixedArrayLookup.machine elementWidth)
noncomputable def machine (elementWidth : ℕ) : Machine Alphabet (State elementWidth) :=
  MultiTape.sequence address (lookup elementWidth) (FixedArrayLookup.entry elementWidth)

def entry (elementWidth : ℕ) : State elementWidth := .inl StandardMatrixAddress.entry
def exit (elementWidth : ℕ) : State elementWidth := .inr (FixedArrayLookup.exit elementWidth)

@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols Alphabet) :
    machine elementWidth (exit elementWidth) symbols = none := by
  simp [machine, exit, lookup, MultiTape.sequence, MultiTape.wire]

def frame (sizes : Fin 3 → ℕ) (row column : List Bool) (array : Turing.Tape Symbol)
    (element product shifted next columns result : List Symbol) (multiplyFlag addFlag : Symbol) : Tapes Alphabet
  | .inl name => StandardMatrixAddress.frame sizes row column product shifted next columns result multiplyFlag addFlag name
  | .inr false => array
  | .inr true => buffer element

/-- The address is computed and then used by the ordinary indexed lookup.
Every writable region may initially contain blanks or invalid symbols. -/
theorem runs (element : EncodedDomain.{0, 0} (Fin 3)) (sizes : Fin 3 → ℕ)
    (row column : List Bool) (rowLength : row.length = sizes 0) (columnLength : column.length = sizes 0)
    (array : (element.arrayOfLength length).Carrier sizes)
    (oldElement oldProduct oldShifted oldNext oldColumns oldResult : List Symbol)
    (elementLength : oldElement.length = element.width sizes)
    (productLength : oldProduct.length = sizes 0) (shiftedLength : oldShifted.length = sizes 0)
    (nextLength : oldNext.length = sizes 0) (columnsLength : oldColumns.length = sizes 0)
    (resultLength : oldResult.length = sizes 0) (multiplyFlag addFlag : Symbol)
    (columnsFit : sizes 2 < 2 ^ sizes 0)
    (addressFit : value row * sizes 2 + value column < 2 ^ sizes 0)
    (within : value row * sizes 2 + value column < MvPolynomial.eval sizes length) :
    ∃ (ticks : ℕ) (addressBits : List Bool),
      addressBits.length = sizes 0 ∧ value addressBits = value row * sizes 2 + value column ∧
      ticks ≤ sizes 2 * (4 * sizes 0 + 8) + sizes 0 * (6 * sizes 0 + 14) + 12 * sizes 0 + 30 +
        MvPolynomial.eval sizes length * (6 * sizes 0 + 2 * element.width sizes + 11) +
        6 * sizes 0 + 2 * element.width sizes + 15 ∧
      Runs (fun name => (domains element name).width sizes) readOnly (machine (element.width sizes)) ticks
        (entry (element.width sizes)) (fun _ => 0)
        (frame sizes row column (encoded (element.arrayOfLength length) sizes array)
          oldElement oldProduct oldShifted oldNext oldColumns oldResult multiplyFlag addFlag)
        (exit (element.width sizes)) (fun _ => 0)
        (frame sizes row column (encoded (element.arrayOfLength length) sizes array)
          (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes
            (array ⟨value row * sizes 2 + value column, within⟩))))
          (word (List.replicate (sizes 0) false)) (word (List.replicate (sizes 0) false))
          (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
          (word addressBits) (data false) (data false)) := by
  obtain ⟨scratch, scratchLength, addressTrace⟩ := StandardMatrixAddress.runs sizes row column rowLength columnLength
    oldProduct oldShifted oldNext oldColumns oldResult productLength shiftedLength nextLength columnsLength
    resultLength multiplyFlag addFlag columnsFit addressFit
  let productBits := MultiplyAdd.product row (StandardMatrixAddress.columnBits sizes)
  let addressBits := MultiplyAdd.result row (StandardMatrixAddress.columnBits sizes) column
  have sameLength : column.length = row.length := columnLength.trans rowLength.symm
  have productBitsLength : productBits.length = sizes 0 :=
    (MultiplyAdd.product_length row (StandardMatrixAddress.columnBits sizes)).trans rowLength
  have addressBitsLength : addressBits.length = sizes 0 :=
    (MultiplyAdd.result_length row (StandardMatrixAddress.columnBits sizes) column
      sameLength).trans rowLength
  have addressValue : value addressBits = value row * sizes 2 + value column := by
    have fits : value row * value (StandardMatrixAddress.columnBits sizes) + value column < 2 ^ row.length := by
      rwa [StandardMatrixAddress.columnBits_value sizes columnsFit, rowLength]
    simpa only [StandardMatrixAddress.columnBits_value sizes columnsFit] using
      MultiplyAdd.result_value row (StandardMatrixAddress.columnBits sizes) column
        sameLength fits
  have inRange : value addressBits < MvPolynomial.eval sizes length := by rwa [addressValue]
  let middle := frame sizes row column (encoded (element.arrayOfLength length) sizes array)
    oldElement (word productBits) (word (List.replicate (sizes 0) false))
    (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
    (word addressBits) (data false) (data false)
  have first := addressTrace.wire_of_eq Function.Embedding.inl
    (fun name => (domains element name).width sizes) readOnly
    (by intro name; rfl) (by intro name premise; exact premise)
    (frame sizes row column (encoded (element.arrayOfLength length) sizes array)
      oldElement oldProduct oldShifted oldNext oldColumns oldResult multiplyFlag addFlag) middle
    (by intro name; rfl) (by intro name; rfl)
    (by intro name outside; cases name with
      | inl name => exact False.elim (outside ⟨name, rfl⟩)
      | inr name => cases name <;> rfl)
  obtain ⟨ticks, cost, localTrace⟩ := FixedArrayLookup.encoded_runsOfLength element length sizes addressBits
    inRange array oldElement (word productBits) (word (List.replicate (sizes 0) false)) elementLength
    (by simp [word, productBitsLength, addressBitsLength]) (by simp [word, addressBitsLength]) (data false)
  let final := frame sizes row column (encoded (element.arrayOfLength length) sizes array)
    (word (EncodedDomain.ArrayEncoding.bits (element.encode sizes (array ⟨value addressBits, inRange⟩))))
    (word (List.replicate (sizes 0) false)) (word (List.replicate (sizes 0) false))
    (word (List.replicate (sizes 0) false)) (word (StandardMatrixAddress.columnBits sizes))
    (word addressBits) (data false) (data false)
  have second := localTrace.wire_of_eq lookupWiring
    (fun name => (domains element name).width sizes) readOnly
    (by
      intro name
      simp only [lookupWiring_apply]
      fin_cases name <;> norm_num [domains, StandardMatrixAddress.domains,
        FixedArrayLookup.widths, FixedArrayBlockCopy.widths, ArrayBlockCopy.widths, addressBitsLength, EncodedDomain.binaryNaturals,
        EncodedDomain.booleans, EncodedDomain.fixed])
    (by
      intro name premise
      simp only [lookupWiring_apply] at premise
      fin_cases name <;> norm_num [readOnly, StandardMatrixAddress.readOnly,
        FixedArrayLookup.readOnly, FixedArrayBlockCopy.readOnly, ArrayBlockCopy.readOnly] at *)
    middle final
    (by intro name; fin_cases name <;> rfl)
    (by
      intro name
      fin_cases name
      · rfl
      · rfl
      · rfl
      · change buffer (word (List.replicate (sizes 0) false)) =
          buffer (word (List.replicate addressBits.length false))
        rw [addressBitsLength]
      · change buffer (word (List.replicate (sizes 0) false)) =
          buffer (word (List.replicate addressBits.length false))
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
          · exact False.elim (outside ⟨3, rfl⟩)
          · rfl
          · exact False.elim (outside ⟨4, rfl⟩)
          · rfl
          · exact False.elim (outside ⟨5, rfl⟩)
          · rfl
          · rfl
          · rfl
          · rfl
      | inr name => cases name with
        | false => exact False.elim (outside ⟨1, rfl⟩)
        | true => exact False.elim (outside ⟨2, rfl⟩))
  have complete := first.sequence (lookup (element.width sizes)) (FixedArrayLookup.entry (element.width sizes))
    (by intro symbols; simp [MultiTape.wire]) second
  refine ⟨sizes 2 * (4 * sizes 0 + 8) + sizes 0 * (6 * sizes 0 + 14) +
    12 * sizes 0 + 29 + ticks + 1, addressBits, addressBitsLength, addressValue, ?_, ?_⟩
  · rw [addressBitsLength] at cost
    omega
  · have selected : (⟨value addressBits, inRange⟩ : Fin (MvPolynomial.eval sizes length)) =
        ⟨value row * sizes 2 + value column, within⟩ := Fin.ext addressValue
    simpa only [final, selected, machine, address, entry, exit] using complete

end Polytime2.StandardMatrixEntry
