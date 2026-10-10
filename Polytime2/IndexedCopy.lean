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


import Polytime2.Array

/-! # Copying one array entry to another on shared tapes

Lookup and update share the array, element, counter, and flag tapes. Only their
index tapes differ. No array serialization or copying occurs at handover.
-/

namespace Polytime2.IndexedCopy

open MultiTape

/-- The additional tape holds the source index; the original index is the target. -/
abbrev TapeName := Sum Unit Array.TapeName
abbrev Alphabet (_name : TapeName) := Binary.Symbol

def frame (source target array element counter : List Bool) (flag : Bool) : Tapes Alphabet
  | .inl () => Binary.tape [3] (Binary.word source ++ [0]) ()
  | .inr name => Array.frame target [] array element counter flag name

/-- `true` selects the source index, `false` the target; all other roles are shared. -/
def wiring (source : Bool) : Array.TapeName ↪ TapeName :=
  ⟨(fun name => match source, name with
    | true, .index => .inl ()
    | _, name => .inr name), by
      intro first second equal
      cases source <;> cases first <;> cases second <;> simp_all⟩

theorem restricted (selected : Bool) (source target array element counter : List Bool) (flag : Bool)
    (name : Array.TapeName) :
    frame source target array element counter flag (wiring selected name) =
      Array.frame (if selected then source else target) [] array element counter flag name := by
  cases selected <;> cases name <;> rfl

theorem installed (selected : Bool) (source target array element counter : List Bool) (flag : Bool)
    (newArray newElement newCounter : List Bool) (newFlag : Bool) :
    install (wiring selected)
      (Array.frame (if selected then source else target) [] newArray newElement newCounter newFlag)
      (frame source target array element counter flag) =
      frame source target newArray newElement newCounter newFlag := by
  funext name
  cases selected with
  | false =>
    cases name with
    | inl unused =>
      exact install_outside _ _ _ _ (by rintro ⟨localName, equal⟩; cases localName <;> cases equal)
    | inr localName => exact install_at (wiring false) _ _ localName
  | true =>
    cases name with
    | inl unused => cases unused; exact install_at (wiring true) _ _ .index
    | inr localName =>
      cases localName with
      | index => exact install_outside _ _ _ _ (by rintro ⟨localName, equal⟩; cases localName <;> cases equal)
      | array => exact install_at (wiring true) _ _ .array
      | element => exact install_at (wiring true) _ _ .element
      | counter => exact install_at (wiring true) _ _ .counter
      | flag => exact install_at (wiring true) _ _ .flag

noncomputable def machine (width : ℕ) :
    Machine Alphabet (Sum (Array.AccessState width) (Array.AccessState width)) :=
  sequence (wire (wiring true) (Array.access width false))
    (wire (wiring false) (Array.access width true)) (.inl (.inl (.inl 0)))

@[simp] theorem halt (width : ℕ) (symbols : Symbols Alphabet) :
    machine width (.inr (.inr 1)) symbols = none := by
  simp [machine, MultiTape.sequence, wire]

-- parameterLevel: names of runtime sizes bounding array length and index capacity.
universe parameterLevel

/-- Copy entry `source` to entry `target`, using one shared array and element tape.
The polynomial is chosen before runtime sizes, indices, and array contents. -/
theorem polynomial_time {Parameter : Type parameterLevel} [Fintype Parameter]
    (width : ℕ) (arrayCapacity digitCapacity : MvPolynomial Parameter ℕ) :
    ∃ bound : MvPolynomial Parameter ℕ,
      ∀ assignment source target element counter flag (blocks : List (List Bool)),
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity →
        source.length ≤ MvPolynomial.eval assignment digitCapacity →
        target.length = source.length → counter.length = source.length →
        (∀ block ∈ blocks, block.length = width) →
        ∀ sourceValid : Binary.value source < blocks.length,
          Binary.value target < blocks.length → element.length = width →
          ∃ ticks, ticks ≤ MvPolynomial.eval assignment bound ∧
            Steps (machine width) ticks
              (.inl (.inl (.inl (.inl 0))), frame source target blocks.flatten element counter flag)
              (.inr (.inr 1), frame source target
                (blocks.set (Binary.value target) blocks[Binary.value source]).flatten
                blocks[Binary.value source] (List.replicate source.length false) false) := by
  obtain ⟨bound, runs⟩ := Array.polynomial_time width false arrayCapacity digitCapacity
  obtain ⟨updateBound, updates⟩ := Array.polynomial_time width true arrayCapacity digitCapacity
  refine ⟨bound + updateBound + 1, ?_⟩
  intro assignment source target element counter flag blocks arrayBound digitBound
    targetLength counterLength widths sourceValid targetValid elementLength
  obtain ⟨lookupTicks, lookupCost, lookupTrace⟩ := runs assignment source element counter flag blocks
    arrayBound digitBound widths sourceValid elementLength counterLength
  have lookup := wire_steps (wiring true) (Array.access width false) lookupTrace
    (frame source target blocks.flatten element counter flag)
    (by intro name; simpa using restricted true source target blocks.flatten element counter flag name)
  simp only [Bool.false_eq_true, ite_false] at lookup
  rw [show install (wiring true)
    (Array.frame source [] blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false)
    (frame source target blocks.flatten element counter flag) =
    frame source target blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false
    from installed true source target blocks.flatten element counter flag _ _ _ false] at lookup
  obtain ⟨updateTicks, updateCost, updateTrace⟩ := updates assignment target blocks[Binary.value source]
    (List.replicate source.length false) false blocks arrayBound (by simpa [targetLength] using digitBound)
    widths targetValid (widths _ (List.getElem_mem sourceValid)) (by simp [targetLength])
  have update := wire_steps (wiring false) (Array.access width true) updateTrace
    (frame source target blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false)
    (by
      intro name
      exact restricted false source target blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false name)
  simp only [eq_self, ite_true, targetLength] at update
  rw [show install (wiring false)
    (Array.frame target [] (blocks.set (Binary.value target) blocks[Binary.value source]).flatten
      blocks[Binary.value source] (List.replicate source.length false) false)
    (frame source target blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false) =
    frame source target (blocks.set (Binary.value target) blocks[Binary.value source]).flatten
      blocks[Binary.value source] (List.replicate source.length false) false
    from installed false source target blocks.flatten blocks[Binary.value source] (List.replicate source.length false) false _ _ _ false] at update
  refine ⟨lookupTicks + updateTicks + 1, ?_, ?_⟩
  · simp only [map_add, map_one]
    omega
  · exact sequence_steps _ _ _ lookup (by intro symbols; simp [wire]) update

/-- A polynomial-time certificate for shared-tape indexed copying. Both indices,
all head positions, and the zeroed scratch counter are part of the contract. -/
theorem realizes {Parameter : Type parameterLevel} [Fintype Parameter]
    (width : ℕ) (arrayCapacity digitCapacity : MvPolynomial Parameter ℕ) :
    Realizes (machine width) (.inl (.inl (.inl (.inl 0)))) (.inr (.inr 1))
      (fun assignment initial => ∃ source target element counter flag, ∃ blocks : List (List Bool),
        blocks.length ≤ MvPolynomial.eval assignment arrayCapacity ∧
        source.length ≤ MvPolynomial.eval assignment digitCapacity ∧
        target.length = source.length ∧ counter.length = source.length ∧
        (∀ block ∈ blocks, block.length = width) ∧
        Binary.value source < blocks.length ∧ Binary.value target < blocks.length ∧
        element.length = width ∧ initial = frame source target blocks.flatten element counter flag)
      (fun _ initial final => ∃ source target element counter flag, ∃ blocks : List (List Bool),
        ∃ sourceValid : Binary.value source < blocks.length,
          Binary.value target < blocks.length ∧
          initial = frame source target blocks.flatten element counter flag ∧
          final = frame source target
            (blocks.set (Binary.value target) blocks[Binary.value source]).flatten
            blocks[Binary.value source] (List.replicate source.length false) false) := by
  obtain ⟨bound, runs⟩ := polynomial_time width arrayCapacity digitCapacity
  refine ⟨halt width, bound, ?_⟩
  intro assignment initial input
  obtain ⟨source, target, element, counter, flag, blocks, arrayBound, digitBound,
    targetLength, counterLength, widths, sourceValid, targetValid, elementLength, rfl⟩ := input
  obtain ⟨ticks, cost, trace⟩ := runs assignment source target element counter flag blocks
    arrayBound digitBound targetLength counterLength widths sourceValid targetValid elementLength
  exact ⟨ticks, _, cost, trace, source, target, element, counter, flag, blocks,
    sourceValid, targetValid, rfl, rfl⟩

end Polytime2.IndexedCopy
