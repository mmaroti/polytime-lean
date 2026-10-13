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

import Polytime2.CatalogueMap

/-! # Contract for two catalogue maps sharing fixed-width scratch tapes -/

namespace Polytime2.CatalogueMap

open MultiTape CallingConvention
open Binary (Symbol word)

-- parameterLevel: names of immutable unary size arguments.
universe parameterLevel
variable {Parameter : Type parameterLevel} [Fintype Parameter]

omit [Fintype Parameter] in
private theorem first_outside (name : Fin 15)
    (outside : name = 1 ∨ name = 2 ∨ name = 5) :
    Sum.inr name ∉ Set.range (wiring (Parameter := Parameter) false) := by
  rintro ⟨localName, equal⟩
  cases localName with
  | inl parameter => cases equal
  | inr localName =>
    fin_cases localName <;> rcases outside with rfl | rfl | rfl <;>
      simp [wiring, data] at equal

private theorem encoded_buffer (domain : EncodedDomain Parameter)
    (assignment : Parameter → ℕ) (value : domain.Carrier assignment) :
    ∃ contents : List Symbol, contents.length = domain.width assignment ∧
      encoded domain assignment value = buffer contents := by
  exact ⟨word (List.ofFn (fun index : Fin (domain.width assignment) =>
    (domain.encode assignment value).getLsbD index.val)), by simp [word], rfl⟩

set_option maxHeartbeats 1200000 in
/-- Both active coordinates are transformed in order. Inputs remain unchanged;
all private scratch is canonical on return, even from blank initial regions. -/
theorem contract (elementDomain : EncodedDomain Empty)
    (indexCapacity : Parameter) (length : MvPolynomial Parameter ℕ)
    (first second : ∀ assignment,
      elementDomain.Carrier assignment → elementDomain.Carrier assignment) :
    CallingConvention.Realizes (domains elementDomain indexCapacity length)
      argumentReadOnly sizeTapes (algorithm elementDomain first second)
      (entry (elementDomain.width Empty.elim)) (exit (elementDomain.width Empty.elim))
      (fun assignment input =>
        (input ⟨.inr 2, rfl⟩).val ≤ MvPolynomial.eval assignment length ∧
        (input ⟨.inr 0, rfl⟩).val < (input ⟨.inr 2, rfl⟩).val ∧
        (input ⟨.inr 1, rfl⟩).val < (input ⟨.inr 2, rfl⟩).val)
      (fun assignment input output =>
        ∃ firstWithin : (input ⟨.inr 0, rfl⟩).val < MvPolynomial.eval assignment length,
        ∃ secondWithin : (input ⟨.inr 1, rfl⟩).val < MvPolynomial.eval assignment length,
          output ⟨.inr 5, rfl⟩ = compute (first Empty.elim) (second Empty.elim)
            (input ⟨.inr 3, rfl⟩)
            ⟨(input ⟨.inr 0, rfl⟩).val, firstWithin⟩
            ⟨(input ⟨.inr 1, rfl⟩).val, secondWithin⟩) := by
  classical
  let localDomains := IndexedMap.domains unitDomain elementDomain indexCapacity length
  obtain ⟨_, firstHalt, firstBound, firstRun⟩ :=
    IndexedMap.contract unitDomain elementDomain indexCapacity length (fun assignment _ => first assignment)
  obtain ⟨_, secondHalt, secondBound, secondRun⟩ :=
    IndexedMap.contract unitDomain elementDomain indexCapacity length (fun assignment _ => second assignment)
  refine ⟨(by intro parameter; rfl), halt elementDomain first second, firstBound + secondBound + 1, ?_⟩
  intro assignment input initial valid represented sizes
  have firstWithin := lt_of_lt_of_le valid.2.1 valid.1
  have secondWithin := lt_of_lt_of_le valid.2.2 valid.1
  have unitInitial : initial (.inr 6) = encoded unitDomain.constant assignment (0 : Fin 1) := by
    obtain ⟨contents, width, equal⟩ := represented.2 (.inr 6) rfl
    have empty : contents = [] := List.eq_nil_of_length_eq_zero width
    subst contents
    exact equal
  let firstInput : Inputs localDomains IndexedMap.argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, immutable⟩
    cases name with
    | inl parameter => exact input ⟨.inl parameter, rfl⟩
    | inr name =>
      by_cases isIndex : name = 0
      · subst name; exact input ⟨.inr 0, rfl⟩
      · by_cases isArray : name = 1
        · subst name; exact input ⟨.inr 3, rfl⟩
        · have isUnit : name = 2 := by
            fin_cases name <;> first | rfl | contradiction
          subst name; exact (0 : Fin 1)
  let firstInitial := fun name => initial (wiring false name)
  have firstEntry : Entry localDomains IndexedMap.argumentReadOnly assignment firstInput firstInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter => exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · exact represented.1 (.inr 0) rfl
        · exact represented.1 (.inr 3) rfl
        · exact unitInitial
        all_goals contradiction
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        fin_cases name
        · contradiction
        · contradiction
        · contradiction
        · exact represented.2 (.inr 4) rfl
        · exact represented.2 (.inr 7) rfl
        · exact represented.2 (.inr 8) rfl
        · exact represented.2 (.inr 9) rfl
        · exact represented.2 (.inr 10) rfl
        · exact represented.2 (.inr 11) rfl
        · exact represented.2 (.inr 12) rfl
        · exact represented.2 (.inr 13) rfl
        · exact represented.2 (.inr 14) rfl
  obtain ⟨firstTicks, firstOutput, firstFinal, firstCost, firstTrace, firstCorrect, firstExit⟩ :=
    firstRun assignment firstInput firstInitial firstWithin firstEntry sizes
  let middle := install (wiring false) firstFinal initial
  have firstPreserved (name : Sum Parameter (Fin 12))
      (immutable : IndexedMap.argumentReadOnly name = true) :
      middle (wiring false name) = firstInitial name := by
    rw [show middle (wiring false name) = firstFinal name from install_at _ _ _ _]
    exact firstTrace.readOnly_tape name immutable
  have firstReturned (name : Sum Parameter (Fin 12))
      (writable : IndexedMap.argumentReadOnly name = false) :
      middle (wiring false name) = encoded (localDomains name) assignment (firstOutput ⟨name, writable⟩) := by
    rw [show middle (wiring false name) = firstFinal name from install_at _ _ _ _]
    exact firstExit name writable
  have firstBuffer (name : Sum Parameter (Fin 12))
      (writable : IndexedMap.argumentReadOnly name = false) :
      ∃ contents : List Symbol, contents.length = (localDomains name).width assignment ∧
        middle (wiring false name) = buffer contents := by
    obtain ⟨contents, width, equal⟩ := encoded_buffer (localDomains name) assignment (firstOutput ⟨name, writable⟩)
    exact ⟨contents, width, (firstReturned name writable).trans equal⟩
  have outsideFirst (name : Fin 15) (outside : name = 1 ∨ name = 2 ∨ name = 5) :
      middle (.inr name) = initial (.inr name) := install_outside _ _ _ _ (first_outside name outside)
  let secondInput : Inputs localDomains IndexedMap.argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, immutable⟩
    cases name with
    | inl parameter => exact input ⟨.inl parameter, rfl⟩
    | inr name =>
      by_cases isIndex : name = 0
      · subst name; exact input ⟨.inr 1, rfl⟩
      · by_cases isArray : name = 1
        · subst name; exact firstOutput ⟨.inr 3, rfl⟩
        · have isUnit : name = 2 := by
            fin_cases name <;> first | rfl | contradiction
          subst name; exact (0 : Fin 1)
  let secondInitial := fun name => middle (wiring true name)
  have secondEntry : Entry localDomains IndexedMap.argumentReadOnly assignment secondInput secondInitial := by
    constructor
    · intro name immutable
      cases name with
      | inl parameter =>
        change middle (wiring false (.inl parameter)) = _
        rw [firstPreserved (.inl parameter) rfl]
        exact represented.1 (.inl parameter) rfl
      | inr name =>
        fin_cases name
        · change middle (.inr 1) = _
          rw [outsideFirst 1 (by simp)]
          exact represented.1 (.inr 1) rfl
        · exact firstReturned (.inr 3) rfl
        · change middle (wiring false (.inr 2)) = _
          rw [firstPreserved (.inr 2) rfl]
          exact unitInitial
        all_goals contradiction
    · intro name writable
      cases name with
      | inl parameter => contradiction
      | inr name =>
        fin_cases name
        · contradiction
        · contradiction
        · contradiction
        · obtain ⟨contents, width, equal⟩ := represented.2 (.inr 5) rfl
          exact ⟨contents, width, (outsideFirst 5 (by simp)).trans equal⟩
        · exact firstBuffer (.inr 4) rfl
        · exact firstBuffer (.inr 5) rfl
        · exact firstBuffer (.inr 6) rfl
        · exact firstBuffer (.inr 7) rfl
        · exact firstBuffer (.inr 8) rfl
        · exact firstBuffer (.inr 9) rfl
        · exact firstBuffer (.inr 10) rfl
        · exact firstBuffer (.inr 11) rfl
  have secondSizes (parameter : Parameter) :
      secondInitial (IndexedMap.sizeTapes parameter) = unary (assignment parameter) := by
    change middle (wiring false (.inl parameter)) = _
    rw [firstPreserved (.inl parameter) rfl]
    exact sizes parameter
  obtain ⟨secondTicks, secondOutput, secondFinal, secondCost, secondTrace, secondCorrect, secondExit⟩ :=
    secondRun assignment secondInput secondInitial secondWithin secondEntry secondSizes
  let final := install (wiring true) secondFinal middle
  have secondReturned (name : Sum Parameter (Fin 12))
      (writable : IndexedMap.argumentReadOnly name = false) :
      final (wiring true name) = encoded (localDomains name) assignment (secondOutput ⟨name, writable⟩) := by
    rw [show final (wiring true name) = secondFinal name from install_at _ _ _ _]
    exact secondExit name writable
  have secondPreserved (name : Sum Parameter (Fin 12))
      (immutable : IndexedMap.argumentReadOnly name = true) :
      final (wiring true name) = secondInitial name := by
    rw [show final (wiring true name) = secondFinal name from install_at _ _ _ _]
    exact secondTrace.readOnly_tape name immutable
  have wiredFirst := firstTrace.wire_of_eq (wiring false)
    (fun name => (domains elementDomain indexCapacity length name).width assignment) argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name immutable; cases name with
      | inl _ => rfl
      | inr name => fin_cases name <;> first | rfl | contradiction)
    initial middle (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  have wiredSecond := secondTrace.wire_of_eq (wiring true)
    (fun name => (domains elementDomain indexCapacity length name).width assignment) argumentReadOnly
    (by intro name; cases name with | inl _ => rfl | inr name => fin_cases name <;> rfl)
    (by intro name immutable; cases name with
      | inl _ => rfl
      | inr name => fin_cases name <;> first | rfl | contradiction)
    middle final (by intro name; rfl) (by intro name; exact install_at _ _ _ _)
    (by intro name outside; exact install_outside _ _ _ _ outside)
  let output : Outputs (domains elementDomain indexCapacity length) argumentReadOnly assignment := fun name => by
    rcases name with ⟨name, writable⟩
    cases name with
    | inl parameter => contradiction
    | inr name =>
      by_cases is4 : name = 4
      · subst name; exact firstOutput ⟨.inr 3, rfl⟩
      ·
        by_cases is5 : name = 5
        · subst name; exact secondOutput ⟨.inr 3, rfl⟩
        ·
          by_cases is6 : name = 6
          · subst name; exact (0 : Fin 1)
          ·
            by_cases is7 : name = 7
            · subst name; exact secondOutput ⟨.inr 4, rfl⟩
            ·
              by_cases is8 : name = 8
              · subst name; exact secondOutput ⟨.inr 5, rfl⟩
              ·
                by_cases is9 : name = 9
                · subst name; exact secondOutput ⟨.inr 6, rfl⟩
                ·
                  by_cases is10 : name = 10
                  · subst name; exact secondOutput ⟨.inr 7, rfl⟩
                  ·
                    by_cases is11 : name = 11
                    · subst name; exact secondOutput ⟨.inr 8, rfl⟩
                    ·
                      by_cases is12 : name = 12
                      · subst name; exact secondOutput ⟨.inr 9, rfl⟩
                      ·
                        by_cases is13 : name = 13
                        · subst name; exact secondOutput ⟨.inr 10, rfl⟩
                        ·
                          by_cases is14 : name = 14
                          · subst name; exact secondOutput ⟨.inr 11, rfl⟩
                          ·
                            have invalid : name.val < 4 := by
                              fin_cases name <;> first | decide | contradiction
                            simp [argumentReadOnly, invalid] at writable
  refine ⟨firstTicks + secondTicks + 1, output, final, ?_,
    sequence_runs elementDomain first second _ _ wiredFirst wiredSecond, ?_, ?_⟩
  · simp only [map_add, map_one]
    omega
  · obtain ⟨_, firstCorrect⟩ := firstCorrect
    obtain ⟨_, secondCorrect⟩ := secondCorrect
    refine ⟨firstWithin, secondWithin, ?_⟩
    dsimp [firstInput, secondInput, output] at firstCorrect secondCorrect ⊢
    rw [firstCorrect] at secondCorrect
    exact secondCorrect
  · intro name writable
    cases name with
    | inl parameter => contradiction
    | inr name =>
      fin_cases name
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · change final (wiring true (.inr 1)) = _
        rw [secondPreserved (.inr 1) rfl]
        exact firstReturned (.inr 3) rfl
      · exact secondReturned (.inr 3) rfl
      · change final (wiring true (.inr 2)) = _
        rw [secondPreserved (.inr 2) rfl]
        change middle (wiring false (.inr 2)) = _
        rw [firstPreserved (.inr 2) rfl]
        exact unitInitial
      · exact secondReturned (.inr 4) rfl
      · exact secondReturned (.inr 5) rfl
      · exact secondReturned (.inr 6) rfl
      · exact secondReturned (.inr 7) rfl
      · exact secondReturned (.inr 8) rfl
      · exact secondReturned (.inr 9) rfl
      · exact secondReturned (.inr 10) rfl
      · exact secondReturned (.inr 11) rfl

end Polytime2.CatalogueMap
