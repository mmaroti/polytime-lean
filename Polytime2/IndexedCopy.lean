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

import Polytime2.StandardArrayLookupSizedContract
import Polytime2.StandardArrayUpdate

/-! # Copying one indexed array entry under the standard convention

The source index, target index, and source array are immutable. Lookup writes
the selected element to private storage; update writes the changed array to a
separate output tape. Both stages share the input array without copying it.
-/

namespace Polytime2.IndexedCopy

open MultiTape CallingConvention
open Binary (Symbol)

-- parameterLevel: names of the caller's unary size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

abbrev Alphabet := CallingConvention.Alphabet (Sum Parameter (Fin 11))
abbrev State (elementWidth : ℕ) :=
  Sum (StandardArrayLookup.State elementWidth)
    (StandardArrayUpdate.State elementWidth)

def lookupData (name : Fin 6) : Fin 11 :=
  ⟨match name.val with
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | 3 => 5
    | 4 => 6
    | _ => 7, by fin_cases name <;> decide⟩

theorem lookupData_injective : Function.Injective lookupData := by
  intro first second equal
  apply Fin.ext
  fin_cases first <;> fin_cases second <;> simp [lookupData] at equal ⊢

def updateData (name : Fin 7) : Fin 11 :=
  ⟨match name.val with
    | 0 => 1
    | 1 => 2
    | 2 => 4
    | 3 => 3
    | 4 => 8
    | 5 => 9
    | _ => 10, by fin_cases name <;> decide⟩

theorem updateData_injective : Function.Injective updateData := by
  intro first second equal
  apply Fin.ext
  fin_cases first <;> fin_cases second <;> simp [updateData] at equal ⊢

noncomputable def domains (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ) :
    Sum Parameter (Fin 11) → EncodedDomain Parameter
  | .inl parameter => EncodedDomain.unary parameter
  | .inr 0 | .inr 1 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 2 | .inr 3 => element.arrayOfLength length
  | .inr 4 => element
  | .inr 5 | .inr 6 | .inr 8 | .inr 9 => EncodedDomain.binaryNaturals indexCapacity
  | .inr 7 | .inr 10 => EncodedDomain.booleans

def argumentReadOnly : Sum Parameter (Fin 11) → Bool
  | .inl _ => true
  | .inr name => decide (name.val < 3)

def sizeTapes : Parameter ↪ Sum Parameter (Fin 11) :=
  ⟨Sum.inl, by intro first second equal; cases equal; rfl⟩

def lookupCallWiring : Sum Parameter (Fin 6) ↪ Sum Parameter (Fin 11) :=
  (Function.Embedding.refl Parameter).sumMap ⟨lookupData, lookupData_injective⟩

def updateCallWiring : Sum Parameter (Fin 7) ↪ Sum Parameter (Fin 11) :=
  (Function.Embedding.refl Parameter).sumMap ⟨updateData, updateData_injective⟩

noncomputable def algorithm (elementWidth : ℕ) : Machine (Alphabet (Parameter := Parameter)) (State elementWidth) :=
  MultiTape.sequence
    (MultiTape.wire lookupCallWiring (StandardArrayLookupSized.algorithmSized elementWidth))
    (MultiTape.wire updateCallWiring (StandardArrayUpdate.algorithmSized elementWidth))
    (StandardArrayUpdate.entry elementWidth)

def entry (elementWidth : ℕ) : State elementWidth :=
  .inl (StandardArrayLookup.entry elementWidth)

def exit (elementWidth : ℕ) : State elementWidth :=
  .inr (StandardArrayUpdate.exit elementWidth)

omit [Fintype Parameter] in
/-- The two internal routines compose whenever lookup's output tapes satisfy
the update routine's entry layout. This exposes the intermediate frame
obligation without adding any controller state to either component.
-/
theorem sequence_runs (elementWidth : ℕ) (width : Sum Parameter (Fin 11) → ℕ)
    (readOnly : Sum Parameter (Fin 11) → Bool)
    {lookupTicks updateTicks : ℕ}
    {initialPosition middlePosition finalPosition : Sum Parameter (Fin 11) → ℤ}
    {initial middle final : Tapes (Alphabet (Parameter := Parameter))}
    (lookupTrace : Runs width readOnly
      (MultiTape.wire lookupCallWiring (StandardArrayLookupSized.algorithmSized elementWidth))
      lookupTicks (StandardArrayLookup.entry elementWidth) initialPosition initial
      (StandardArrayLookup.exit elementWidth) middlePosition middle)
    (updateTrace : Runs width readOnly
      (MultiTape.wire updateCallWiring (StandardArrayUpdate.algorithmSized elementWidth))
      updateTicks (StandardArrayUpdate.entry elementWidth) middlePosition middle
      (StandardArrayUpdate.exit elementWidth) finalPosition final) :
    Runs width readOnly (algorithm elementWidth) (lookupTicks + updateTicks + 1)
      (.inl (StandardArrayLookup.entry elementWidth)) initialPosition initial
      (.inr (StandardArrayUpdate.exit elementWidth)) finalPosition final := by
  apply Runs.sequence
    (MultiTape.wire updateCallWiring (StandardArrayUpdate.algorithmSized elementWidth))
    (StandardArrayUpdate.entry elementWidth) lookupTrace
  · intro symbols
    simp [MultiTape.wire, StandardArrayLookupSized.algorithmSized, StandardArrayLookup.halt]
  · exact updateTrace

omit [Fintype Parameter] in
@[simp] theorem halt (elementWidth : ℕ) (symbols : Symbols (Alphabet (Parameter := Parameter))) :
    algorithm elementWidth (exit elementWidth) symbols = none := by
  simp [algorithm, exit, MultiTape.sequence, MultiTape.wire,
    StandardArrayUpdate.algorithmSized,
    StandardArrayUpdate.machine,
    StandardArrayUpdate.exit,
    StandardArrayUpdate.restore, StandardHead.BlankReturn.machine]

omit [Fintype Parameter] in
private theorem lookup_outside (name : Fin 11)
    (outside : name = 1 ∨ name = 3 ∨ name = 8 ∨ name = 9 ∨ name = 10) :
    Sum.inr name ∉ Set.range (lookupCallWiring (Parameter := Parameter)) := by
  rintro ⟨localName, equal⟩
  cases localName with
  | inl parameter => cases equal
  | inr localName =>
    fin_cases localName <;>
      rcases outside with rfl | rfl | rfl | rfl | rfl <;>
        simp [lookupCallWiring, lookupData] at equal

omit [Fintype Parameter] in
private theorem update_outside (name : Fin 11)
    (outside : name = 5 ∨ name = 6 ∨ name = 7) :
    Sum.inr name ∉ Set.range (updateCallWiring (Parameter := Parameter)) := by
  rintro ⟨localName, equal⟩
  cases localName with
  | inl parameter => cases equal
  | inr localName =>
    fin_cases localName <;>
      rcases outside with rfl | rfl | rfl <;>
        simp [updateCallWiring, updateData] at equal

/-- Copy the source coordinate to the target coordinate of a fresh output
array. Both indices and the original array are immutable; all scratch returns
as valid encoded values, even when the indices agree or elements use no bits.
-/
theorem contract (element : EncodedDomain.{parameterLevel, 0} Parameter)
    (elementWidth : ℕ) (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (fixedWidth : ∀ assignment, element.width assignment = elementWidth) :
    CallingConvention.Realizes (domains element indexCapacity length) argumentReadOnly sizeTapes
      (algorithm elementWidth) (entry elementWidth) (exit elementWidth)
      (fun assignment input =>
        (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length ∧
          (input ⟨.inr 1, rfl⟩).val < MvPolynomial.eval assignment length)
      (fun assignment input output =>
        ∃ sourceBound : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
          ∃ targetBound : (input ⟨.inr 1, rfl⟩).val < MvPolynomial.eval assignment length,
            output ⟨.inr 3, rfl⟩ = Function.update (input ⟨.inr 2, rfl⟩)
              ⟨(input ⟨.inr 1, rfl⟩).val, targetBound⟩
              (input ⟨.inr 2, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, sourceBound⟩)) := by
  classical
  obtain ⟨lookupSizes, lookupHalt, lookupBound, lookupRun⟩ :=
    StandardArrayLookupSized.contractSized element elementWidth indexCapacity length fixedWidth
  obtain ⟨updateSizes, updateHalt, updateBound, updateRun⟩ :=
    StandardArrayUpdate.contractSized element elementWidth indexCapacity length fixedWidth
  refine ⟨(by intro parameter; rfl), halt elementWidth,
    lookupBound + updateBound + 1, ?_⟩
  intro assignment input initial valid represented sizes
  let lookupInput : Inputs (StandardArrayLookupSized.domainsSized element indexCapacity length)
      StandardArrayLookupSized.argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, immutable⟩
    cases name with
    | inl parameter => exact input ⟨.inl parameter, rfl⟩
    | inr name =>
      by_cases indexTape : name = 0
      · subst name; exact input ⟨.inr 0, rfl⟩
      · by_cases arrayTape : name = 1
        · subst name; exact input ⟨.inr 2, rfl⟩
        · simp [StandardArrayLookupSized.argumentReadOnly, StandardArrayLookup.readOnly,
            indexTape, arrayTape] at immutable
  let lookupInitial := fun name => initial (lookupCallWiring name)
  have lookupEntry : Entry (StandardArrayLookupSized.domainsSized element indexCapacity length)
      StandardArrayLookupSized.argumentReadOnly assignment lookupInput lookupInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter => exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · exact represented.1 (.inr 0) rfl
        · exact represented.1 (.inr 2) rfl
        all_goals contradiction
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        fin_cases name
        · contradiction
        · contradiction
        · exact represented.2 (.inr 4) rfl
        · exact represented.2 (.inr 5) rfl
        · exact represented.2 (.inr 6) rfl
        · exact represented.2 (.inr 7) rfl
  obtain ⟨lookupTicks, lookupOutput, lookupFinal, lookupCost, lookupTrace,
      lookupCorrect, lookupExit⟩ :=
    lookupRun assignment lookupInput lookupInitial valid.1 lookupEntry sizes
  let middle := install lookupCallWiring lookupFinal initial
  have lookupPreserved (name : Sum Parameter (Fin 6))
      (immutable : StandardArrayLookupSized.argumentReadOnly name = true) :
      lookupFinal name = lookupInitial name :=
    lookupTrace.readOnly_tape name immutable
  have middleOutside (name : Fin 11)
      (outside : name = 1 ∨ name = 3 ∨ name = 8 ∨ name = 9 ∨ name = 10) :
      middle (.inr name) = initial (.inr name) :=
    install_outside _ _ _ _ (lookup_outside name outside)
  have middleInput (name : Sum Parameter (Fin 6))
      (immutable : StandardArrayLookupSized.argumentReadOnly name = true) :
      middle (lookupCallWiring name) = lookupInitial name := by
    rw [show middle (lookupCallWiring name) = lookupFinal name from install_at _ _ _ _]
    exact lookupPreserved name immutable
  have middleOutput (name : Sum Parameter (Fin 6))
      (writable : StandardArrayLookupSized.argumentReadOnly name = false) :
      middle (lookupCallWiring name) = encoded (StandardArrayLookupSized.domainsSized element indexCapacity length name)
        assignment (lookupOutput ⟨name, writable⟩) := by
    rw [show middle (lookupCallWiring name) = lookupFinal name from install_at _ _ _ _]
    exact lookupExit name writable
  let updateInput : Inputs (StandardArrayUpdate.domainsSized element indexCapacity length)
      StandardArrayUpdate.argumentReadOnlySized assignment := fun name => by
    rcases name with ⟨name, immutable⟩
    cases name with
    | inl parameter => exact input ⟨.inl parameter, rfl⟩
    | inr name =>
      by_cases indexTape : name = 0
      · subst name; exact input ⟨.inr 1, rfl⟩
      · by_cases arrayTape : name = 1
        · subst name; exact input ⟨.inr 2, rfl⟩
        · by_cases elementTape : name = 2
          · subst name; exact lookupOutput ⟨.inr 2, rfl⟩
          · have remaining : 3 ≤ name.val := by
              have bound := name.isLt
              have first : name.val ≠ 0 := fun equal => indexTape (Fin.ext equal)
              have second : name.val ≠ 1 := fun equal => arrayTape (Fin.ext equal)
              have third : name.val ≠ 2 := fun equal => elementTape (Fin.ext equal)
              omega
            simp [StandardArrayUpdate.argumentReadOnlySized] at immutable
            omega
  let updateInitial := fun name => middle (updateCallWiring name)
  have updateEntry : Entry (StandardArrayUpdate.domainsSized element indexCapacity length)
      StandardArrayUpdate.argumentReadOnlySized assignment updateInput updateInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter =>
        change middle (lookupCallWiring (.inl parameter)) = _
        rw [middleInput (.inl parameter) rfl]
        exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · change middle (.inr 1) = _
          rw [middleOutside 1 (Or.inl rfl)]
          exact represented.1 (.inr 1) rfl
        · change middle (lookupCallWiring (.inr 1)) = _
          rw [middleInput (.inr 1) rfl]
          exact represented.1 (.inr 2) rfl
        · exact middleOutput (.inr 2) rfl
        all_goals contradiction
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        fin_cases name
        · contradiction
        · contradiction
        · contradiction
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 3) rfl
          refine ⟨contents, ?_, (middleOutside 3 (Or.inr (Or.inl rfl))).trans equal⟩
          simpa [StandardArrayUpdate.domainsSized,
            domains, EncodedDomain.array, EncodedDomain.arrayOfLength] using length
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 8) rfl
          exact ⟨contents, length, (middleOutside 8 (by simp)).trans equal⟩
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 9) rfl
          exact ⟨contents, length, (middleOutside 9 (by simp)).trans equal⟩
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 10) rfl
          exact ⟨contents, length, (middleOutside 10 (by simp)).trans equal⟩
  have updateSizeInputs (parameter : Parameter) :
      updateInitial (StandardArrayUpdate.sizeTapesSized parameter) = unary (assignment parameter) := by
    change middle (lookupCallWiring (.inl parameter)) = _
    rw [middleInput (.inl parameter) rfl]
    exact sizes parameter
  obtain ⟨updateTicks, updateOutput, updateFinal, updateCost, updateTrace,
      updateCorrect, updateExit⟩ :=
    updateRun assignment updateInput updateInitial (by simpa [updateInput] using valid.2) updateEntry updateSizeInputs
  let final := install updateCallWiring updateFinal middle
  have wiredLookup := lookupTrace.wire_of_eq lookupCallWiring
    (fun name => (domains element indexCapacity length name).width assignment) argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name immutable; cases name with | inl _ => rfl | inr name => fin_cases name <;> exact immutable)
    initial middle (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have wiredUpdate := updateTrace.wire_of_eq updateCallWiring
    (fun name => (domains element indexCapacity length name).width assignment) argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by
      intro name immutable
      cases name with
      | inl _ => rfl
      | inr name =>
        fin_cases name <;> first | rfl | contradiction)
    middle final (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have complete := sequence_runs elementWidth _ _ wiredLookup wiredUpdate
  let output : Outputs (domains element indexCapacity length) argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases resultTape : name = 3
      · subst name; exact updateOutput ⟨.inr 3, rfl⟩
      · by_cases elementTape : name = 4
        · subst name; exact lookupOutput ⟨.inr 2, rfl⟩
        · by_cases lookupCounter : name = 5
          · subst name; exact lookupOutput ⟨.inr 3, rfl⟩
          · by_cases lookupScratch : name = 6
            · subst name; exact lookupOutput ⟨.inr 4, rfl⟩
            · by_cases lookupFlag : name = 7
              · subst name; exact lookupOutput ⟨.inr 5, rfl⟩
              · by_cases updateCounter : name = 8
                · subst name; exact updateOutput ⟨.inr 4, rfl⟩
                · by_cases updateScratch : name = 9
                  · subst name; exact updateOutput ⟨.inr 5, rfl⟩
                  · by_cases updateFlag : name = 10
                    · subst name; exact updateOutput ⟨.inr 6, rfl⟩
                    · have invalid : name.val < 3 := by
                        fin_cases name <;> first | decide | contradiction
                      simp [argumentReadOnly, invalid] at writable
  refine ⟨lookupTicks + updateTicks + 1, output, final, ?_, complete, ?_, ?_⟩
  · simp only [map_add, map_one]
    omega
  · obtain ⟨sourceBound, sourceValue⟩ := lookupCorrect
    obtain ⟨targetBound, updated⟩ := updateCorrect
    refine ⟨valid.1, valid.2, ?_⟩
    dsimp [output, lookupInput, updateInput] at sourceValue updated ⊢
    rw [sourceValue] at updated
    exact updated
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      fin_cases name
      · contradiction
      · contradiction
      · contradiction
      · exact (show final (updateCallWiring (.inr 3)) = updateFinal (.inr 3) from
          install_at _ _ _ _).trans (updateExit (.inr 3) rfl)
      · change final (updateCallWiring (.inr 2)) = _
        rw [show final (updateCallWiring (.inr 2)) = updateFinal (.inr 2) from install_at _ _ _ _]
        rw [updateTrace.readOnly_tape (.inr 2) rfl]
        exact middleOutput (.inr 2) rfl
      · change final (.inr 5) = _
        rw [show final (.inr 5) = middle (.inr 5) from
          install_outside _ _ _ _ (update_outside 5 (by simp))]
        exact middleOutput (.inr 3) rfl
      · change final (.inr 6) = _
        rw [show final (.inr 6) = middle (.inr 6) from
          install_outside _ _ _ _ (update_outside 6 (by simp))]
        exact middleOutput (.inr 4) rfl
      · change final (.inr 7) = _
        rw [show final (.inr 7) = middle (.inr 7) from
          install_outside _ _ _ _ (update_outside 7 (by simp))]
        exact middleOutput (.inr 5) rfl
      · exact (show final (updateCallWiring (.inr 4)) = updateFinal (.inr 4) from
          install_at _ _ _ _).trans (updateExit (.inr 4) rfl)
      · exact (show final (updateCallWiring (.inr 5)) = updateFinal (.inr 5) from
          install_at _ _ _ _).trans (updateExit (.inr 5) rfl)
      · exact (show final (updateCallWiring (.inr 6)) = updateFinal (.inr 6) from
          install_at _ _ _ _).trans (updateExit (.inr 6) rfl)

end Polytime2.IndexedCopy
