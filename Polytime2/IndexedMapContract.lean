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

import Polytime2.IndexedMap

/-! # Mathematical contract for indexed finite operations -/

namespace Polytime2.IndexedMap

open MultiTape CallingConvention

-- parameterLevel: names of the caller's unary size parameters.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

omit [Fintype Parameter] in
private theorem lookup_outside (name : Fin 12)
    (outside : name = 2 ∨ name = 3 ∨ name = 5 ∨ name = 9 ∨ name = 10 ∨ name = 11) :
    Sum.inr name ∉ Set.range (lookupWiring (Parameter := Parameter)) := by
  rintro ⟨localName, equal⟩
  cases localName with
  | inl parameter => cases equal
  | inr localName =>
    fin_cases localName <;>
      rcases outside with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [lookupWiring, lookupData] at equal

def outputTapes : Unit ↪ Sum Parameter (Fin 12) := oneTape (.inr 3)

set_option maxHeartbeats 800000 in
/-- Lookup, a fixed scalar operation, and update compose with immutable inputs,
arbitrary initial writable contents, and a canonical public result. -/
theorem contract (parameterDomain elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (operation : ∀ assignment, parameterDomain.Carrier assignment →
      elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    CallingConvention.Realizes (domains parameterDomain elementDomain indexCapacity length)
      argumentReadOnly sizeTapes outputTapes (algorithm parameterDomain elementDomain operation)
      (entry (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim))
      (exit (parameterDomain.width Empty.elim) (elementDomain.width Empty.elim))
      (fun assignment input => (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length)
      (fun assignment input output =>
        ∃ within : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
          output () = Function.update (input ⟨.inr 1, rfl⟩)
            ⟨(input ⟨.inr 0, rfl⟩).val, within⟩
            (operation Empty.elim (input ⟨.inr 2, rfl⟩)
              (input ⟨.inr 1, rfl⟩ ⟨(input ⟨.inr 0, rfl⟩).val, within⟩))) := by
  classical
  let element : EncodedDomain Parameter := elementDomain.constant
  let elementWidth := elementDomain.width Empty.elim
  obtain ⟨lookupSizes, lookupOutputsWritable, lookupHalt, lookupBound, lookupRun⟩ :=
    StandardArrayLookupSized.contractSized element elementWidth indexCapacity length (by intro assignment; rfl)
  obtain ⟨tableSizes, tableOutputsWritable, tableHalt, tableBound, tableRun⟩ :=
    StandardFiniteTable.contract parameterDomain elementDomain elementDomain operation
  obtain ⟨updateSizes, updateOutputsWritable, updateHalt, updateBound, updateRun⟩ :=
    StandardArrayUpdate.contractSized element elementWidth indexCapacity length (by intro assignment; rfl)
  refine ⟨(by intro parameter; rfl), (by intro name; rfl), ?_,
    lookupBound + MvPolynomial.C (MvPolynomial.eval Empty.elim tableBound) + updateBound + 2, ?_⟩
  · intro symbols
    simp [algorithm, exit, MultiTape.sequence, MultiTape.wire,
      StandardArrayUpdate.algorithmSized, StandardArrayUpdate.machine,
      StandardArrayUpdate.exit, StandardArrayUpdate.restore, StandardHead.BlankReturn.machine]
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
        · subst name; exact input ⟨.inr 1, rfl⟩
        · simp [StandardArrayLookupSized.argumentReadOnly, StandardArrayLookup.readOnly,
            indexTape, arrayTape] at immutable
  let lookupInitial := fun name => initial (lookupWiring name)
  have lookupEntry : Entry (StandardArrayLookupSized.domainsSized element indexCapacity length)
      StandardArrayLookupSized.argumentReadOnly assignment lookupInput lookupInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter => exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · exact represented.1 (.inr 0) rfl
        · exact represented.1 (.inr 1) rfl
        all_goals contradiction
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        fin_cases name
        · contradiction
        · contradiction
        · exact represented.2 (.inr 4) rfl
        · exact represented.2 (.inr 6) rfl
        · exact represented.2 (.inr 7) rfl
        · exact represented.2 (.inr 8) rfl
  obtain ⟨lookupTicks, lookupOutput, lookupFinal, lookupCost, lookupTrace,
      lookupCorrect, lookupExit⟩ :=
    lookupRun assignment lookupInput lookupInitial valid lookupEntry sizes
  let afterLookup := install lookupWiring lookupFinal initial
  have lookupOutside (name : Fin 12)
      (outside : name = 2 ∨ name = 3 ∨ name = 5 ∨ name = 9 ∨ name = 10 ∨ name = 11) :
      afterLookup (.inr name) = initial (.inr name) :=
    install_outside _ _ _ _ (lookup_outside name outside)
  have lookupInputPreserved (name : Sum Parameter (Fin 6))
      (immutable : StandardArrayLookupSized.argumentReadOnly name = true) :
      afterLookup (lookupWiring name) = lookupInitial name := by
    rw [show afterLookup (lookupWiring name) = lookupFinal name from install_at _ _ _ _]
    exact lookupTrace.readOnly_tape name immutable
  have lookupReturned : afterLookup (lookupWiring (.inr 2)) =
      encoded element assignment (lookupOutput ()) := by
    rw [show afterLookup (lookupWiring (.inr 2)) = lookupFinal (.inr 2) from install_at _ _ _ _]
    exact lookupExit ()
  let tableDomains := StandardFiniteTable.domains parameterDomain elementDomain elementDomain
  let tableInput : Inputs tableDomains StandardFiniteTable.readOnly Empty.elim := fun name => by
    rcases name with ⟨name, immutable⟩
    by_cases parameterTape : name = 0
    · subst name; exact input ⟨.inr 2, rfl⟩
    · by_cases elementTape : name = 1
      · subst name; exact lookupOutput ()
      · have invalid : name.val ≥ 2 := by
          have bounded := name.isLt
          have first : name.val ≠ 0 := fun equal => parameterTape (Fin.ext equal)
          have second : name.val ≠ 1 := fun equal => elementTape (Fin.ext equal)
          omega
        simp [StandardFiniteTable.readOnly] at immutable
        omega
  let tableInitial := fun name => afterLookup (tableWiring name)
  have tableEntry : Entry tableDomains StandardFiniteTable.readOnly Empty.elim
      tableInput tableInitial := by
    constructor
    · intro name immutable
      fin_cases name
      · change afterLookup (.inr 2) = _
        rw [lookupOutside 2 (Or.inl rfl)]
        exact represented.1 (.inr 2) rfl
      · exact lookupReturned
      · contradiction
    · intro name writable
      fin_cases name
      · contradiction
      · contradiction
      · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 5) rfl
        exact ⟨contents, length,
          (lookupOutside 5 (Or.inr (Or.inr (Or.inl rfl)))).trans equal⟩
  obtain ⟨tableTicks, tableOutput, tableFinal, tableCost, tableTrace,
      tableCorrect, tableExit⟩ :=
    tableRun Empty.elim tableInput tableInitial trivial tableEntry (by intro parameter; cases parameter)
  let afterTable := install tableWiring tableFinal afterLookup
  have tableOutside (name : Fin 12) (outside : name ≠ 2 ∧ name ≠ 4 ∧ name ≠ 5) :
      afterTable (.inr name) = afterLookup (.inr name) := by
    apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName
    · exact outside.1 (Sum.inr.inj equal).symm
    · exact outside.2.1 (Sum.inr.inj equal).symm
    · exact outside.2.2 (Sum.inr.inj equal).symm
  have tableOutsideSize (parameter : Parameter) :
      afterTable (.inl parameter) = afterLookup (.inl parameter) := by
    apply install_outside
    rintro ⟨localName, equal⟩
    fin_cases localName <;> cases equal
  have tableInputPreserved (name : Fin 3)
      (immutable : StandardFiniteTable.readOnly name = true) :
      afterTable (tableWiring name) = tableInitial name := by
    rw [show afterTable (tableWiring name) = tableFinal name from install_at _ _ _ _]
    exact tableTrace.readOnly_tape name immutable
  have tableReturned : afterTable (tableWiring 2) =
      encoded elementDomain Empty.elim (tableOutput ()) := by
    rw [show afterTable (tableWiring 2) = tableFinal 2 from install_at _ _ _ _]
    exact tableExit ()
  let updateInput : Inputs (StandardArrayUpdate.domainsSized element indexCapacity length)
      StandardArrayUpdate.argumentReadOnlySized assignment := fun name => by
    rcases name with ⟨name, immutable⟩
    cases name with
    | inl parameter => exact input ⟨.inl parameter, rfl⟩
    | inr name =>
      by_cases indexTape : name = 0
      · subst name; exact input ⟨.inr 0, rfl⟩
      · by_cases arrayTape : name = 1
        · subst name; exact input ⟨.inr 1, rfl⟩
        · by_cases elementTape : name = 2
          · subst name; exact tableOutput ()
          · have remaining : 3 ≤ name.val := by
              have bound := name.isLt
              have first : name.val ≠ 0 := fun equal => indexTape (Fin.ext equal)
              have second : name.val ≠ 1 := fun equal => arrayTape (Fin.ext equal)
              have third : name.val ≠ 2 := fun equal => elementTape (Fin.ext equal)
              omega
            simp [StandardArrayUpdate.argumentReadOnlySized] at immutable
            omega
  let updateInitial := fun name => afterTable (updateWiring name)
  have updateEntry : Entry (StandardArrayUpdate.domainsSized element indexCapacity length)
      StandardArrayUpdate.argumentReadOnlySized assignment updateInput updateInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter =>
        change afterTable (.inl parameter) = _
        rw [tableOutsideSize parameter]
        change afterLookup (lookupWiring (.inl parameter)) = _
        rw [lookupInputPreserved (.inl parameter) rfl]
        exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · change afterTable (.inr 0) = _
          rw [tableOutside 0 (by decide)]
          change afterLookup (lookupWiring (.inr 0)) = _
          rw [lookupInputPreserved (.inr 0) rfl]
          exact represented.1 (.inr 0) rfl
        · change afterTable (.inr 1) = _
          rw [tableOutside 1 (by decide)]
          change afterLookup (lookupWiring (.inr 1)) = _
          rw [lookupInputPreserved (.inr 1) rfl]
          exact represented.1 (.inr 1) rfl
        · exact tableReturned
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
          exact ⟨contents, length, (tableOutside 3 (by decide)).trans
            ((lookupOutside 3 (by simp)).trans equal)⟩
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 9) rfl
          exact ⟨contents, length, (tableOutside 9 (by decide)).trans
            ((lookupOutside 9 (by simp)).trans equal)⟩
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 10) rfl
          exact ⟨contents, length, (tableOutside 10 (by decide)).trans
            ((lookupOutside 10 (by simp)).trans equal)⟩
        · obtain ⟨contents, length, equal⟩ := represented.2 (.inr 11) rfl
          exact ⟨contents, length, (tableOutside 11 (by decide)).trans
            ((lookupOutside 11 (by simp)).trans equal)⟩
  have updateSizesReady (parameter : Parameter) :
      updateInitial (StandardArrayUpdate.sizeTapesSized parameter) = unary (assignment parameter) := by
    change afterTable (.inl parameter) = _
    rw [tableOutsideSize parameter]
    change afterLookup (lookupWiring (.inl parameter)) = _
    rw [lookupInputPreserved (.inl parameter) rfl]
    exact sizes parameter
  obtain ⟨updateTicks, updateOutput, updateFinal, updateCost, updateTrace,
      updateCorrect, updateExit⟩ :=
    updateRun assignment updateInput updateInitial valid updateEntry updateSizesReady
  let final := install updateWiring updateFinal afterTable
  have wiredLookup := lookupTrace.wire_of_eq lookupWiring
    (fun name => (domains parameterDomain elementDomain indexCapacity length name).width assignment)
    argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name immutable; cases name with | inl _ => rfl | inr name => fin_cases name <;> exact immutable)
    initial afterLookup (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have wiredTable := tableTrace.wire_of_eq tableWiring
    (fun name => (domains parameterDomain elementDomain indexCapacity length name).width assignment)
    argumentReadOnly (by intro name; fin_cases name <;> rfl)
    (by intro name immutable; fin_cases name <;> first | rfl | contradiction)
    afterLookup afterTable (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have wiredUpdate := updateTrace.wire_of_eq updateWiring
    (fun name => (domains parameterDomain elementDomain indexCapacity length name).width assignment)
    argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name immutable; cases name with
      | inl _ => rfl
      | inr name => fin_cases name <;> first | rfl | contradiction)
    afterTable final (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have complete := sequence_runs parameterDomain elementDomain operation _ _
    wiredLookup wiredTable wiredUpdate
  let output : Outputs (domains parameterDomain elementDomain indexCapacity length)
      outputTapes assignment := fun _ => updateOutput ()
  refine ⟨lookupTicks + tableTicks + updateTicks + 2, output, final, ?_, complete, ?_, ?_⟩
  · simp only [map_add, MvPolynomial.eval_C, map_ofNat]
    omega
  · obtain ⟨within, selected⟩ := lookupCorrect
    obtain ⟨updatedWithin, updated⟩ := updateCorrect
    refine ⟨valid, ?_⟩
    dsimp [lookupInput, tableInput, updateInput, output] at selected tableCorrect updated ⊢
    rw [tableCorrect, selected] at updated
    exact updated
  · intro name
    cases name
    exact (show final (updateWiring (.inr 3)) = updateFinal (.inr 3) from
      install_at _ _ _ _).trans (updateExit ())

end Polytime2.IndexedMap
