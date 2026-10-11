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

import Polytime.MatrixStorage

/-! # One active SMP catalogue coordinate

Apply a specialization-fixed catalogue table to one selected generator entry.
The matrix has reserved dimensions; the active coordinate count is runtime data,
stored in the preserved suffix. Inactive columns and all other entries survive.
This is a storage operation used by catalogue quotient/projection algorithms,
not a realization of the entire SMP preparation algorithm.
-/

namespace Polytime.Examples.CatalogueMap

open Matrices TupleMachine

-- slotLevel: the fixed tagged carrier shared by catalogue entries.
-- sortLevel: the specialization-fixed catalogue identifiers.
universe slotLevel sortLevel

abbrev Value (slots : FixedPresentation.{slotLevel}) (sizes : SizeAssignment context) :=
  ℕ × MatrixStorage.Value slots sizes

noncomputable section ActiveCoordinates

variable (slots : FixedPresentation.{slotLevel})

abbrev valid (sizes : SizeAssignment context) (value : Value slots sizes) : Prop :=
  value.1 ≤ sizes .L ∧ value.2.1 < sizes .K ∧ value.2.2.1 < value.1

def representation (sizes : SizeAssignment context) (right : List Symbol)
    (value : Value slots sizes) (tape : Turing.Tape Symbol) : Prop :=
  MatrixStorage.representation slots sizes (UnaryMachine.fields [value.1] ++ right) value.2 tape

def advance (operation : slots.Carrier → slots.Carrier)
    (sizes : SizeAssignment context) (value : Value slots sizes) : Value slots sizes :=
  (value.1, MatrixStorage.advance slots operation sizes value.2)

/-- The active count remains data. The fixed map can depend on the selected
catalogue sort, but neither the matrix nor its active count specializes it. -/
theorem contract [Nontrivial slots.Carrier] {Catalogue : Type sortLevel}
    (maps : Catalogue → slots.Carrier → slots.Carrier) (sort : Catalogue) :
    Realization.Realizes (representation slots) (representation slots) (valid slots)
      (fun sizes initial final => final = advance slots (maps sort) sizes initial) := by
  apply (MatrixStorage.map_contract slots (maps sort)).adapt
    (fun _ value => value.2)
    (fun _ right value => UnaryMachine.fields [value.1] ++ right)
    (fun _ initial final => (initial.1, final))
    (representation slots) (representation slots) (valid slots)
    (fun sizes initial final => final = advance slots (maps sort) sizes initial)
  · intro sizes value bounded
    exact ⟨bounded.2.1, bounded.2.2.trans_le bounded.1⟩
  · intros; assumption
  · intro sizes initial final _ equal
    exact congrArg (fun result => (initial.1, result)) equal
  · intros; assumption

/-- The selected active entry changes by the catalogue map; padding and other
rows are preserved, and the cursor advances without changing the active count. -/
theorem advance_spec (operation : slots.Carrier → slots.Carrier)
    (sizes : SizeAssignment context) (value : Value slots sizes) (bounded : valid slots sizes value) :
    let final := advance slots operation sizes value
    final.1 = value.1 ∧ final.2.1 = value.2.1 ∧ final.2.2.1 = value.2.2.1 + 1 ∧
      ∀ row column, final.2.2.2 row column =
        if row.val = value.2.1 ∧ column.val = value.2.2.1 then
          operation (value.2.2.2 row column) else value.2.2.2 row column := by
  classical
  have inRange : MatrixStorage.valid slots sizes value.2 :=
    ⟨bounded.2.1, bounded.2.2.trans_le bounded.1⟩
  simp only [advance, MatrixStorage.advance, dite_eq_left inRange]
  refine ⟨trivial, trivial, trivial, ?_⟩
  intro row column
  by_cases sameRow : row = (⟨value.2.1, bounded.2.1⟩ : Fin (sizes .K))
  · subst row
    by_cases sameColumn : column = (⟨value.2.2.1, inRange.2⟩ : Fin (sizes .L))
    · subst column
      simp [Function.update]
    · have distinct : column.val ≠ value.2.2.1 := fun equal => sameColumn (Fin.ext equal)
      simp [Function.update, Fin.ext_iff, distinct]
  · have distinct : row.val ≠ value.2.1 := fun equal => sameRow (Fin.ext equal)
    simp [Function.update, Fin.ext_iff, distinct]


/-- Two fixed catalogue maps share one prepared frame. Only mathematical
bounds establish the handoff; caller data and temporary storage stay internal. -/
theorem two_coordinates_contract [Nontrivial slots.Carrier] {Catalogue : Type sortLevel}
    (maps : Catalogue → slots.Carrier → slots.Carrier) (first second : Catalogue) :
    Realization.Realizes (representation slots) (representation slots)
      (fun sizes value => valid slots sizes value ∧ value.2.2.1 + 1 < value.1)
      (fun sizes initial final => final =
        advance slots (maps second) sizes (advance slots (maps first) sizes initial)) := by
  have firstContract : Realization.Realizes (representation slots) (representation slots)
      (fun sizes value => valid slots sizes value ∧ value.2.2.1 + 1 < value.1)
      (fun sizes initial final => final = advance slots (maps first) sizes initial ∧ valid slots sizes final) := by
    apply (contract slots maps first).consequence (by intro sizes value good; exact good.1)
    intro sizes initial final good equal
    subst final
    refine ⟨rfl, ?_⟩
    have specification := advance_spec slots (maps first) sizes initial good.1
    change (advance slots (maps first) sizes initial).1 ≤ sizes .L ∧
      (advance slots (maps first) sizes initial).2.1 < sizes .K ∧
      (advance slots (maps first) sizes initial).2.2.1 < (advance slots (maps first) sizes initial).1
    rw [specification.1, specification.2.1, specification.2.2.1]
    exact ⟨good.1.1, good.1.2.1, good.2⟩
  exact (firstContract.sequence (contract slots maps second)
    (by intro sizes initial middle _ correct; exact correct.2)).consequence
      (by intros; assumption) (by
        intro sizes initial final _ composed
        obtain ⟨middle, firstCorrect, secondCorrect⟩ := composed
        rw [secondCorrect, firstCorrect.1])

end ActiveCoordinates

section ConcreteQuotient

/-- Tagged residues: 0,...,3 belong to Z/4 and 4,5 to its quotient Z/2.
The quotient map sends a source residue to the tagged parity residue. -/
def parityQuotient (slot : Fin 6) : Fin 6 :=
  if slot.val < 4 then ⟨4 + slot.val % 2, by omega⟩ else slot

#guard parityQuotient 0 = 4
#guard parityQuotient 3 = 5
#guard parityQuotient 4 = 4

/-- The tag and payload of the quotient agree with reduction modulo two. -/
theorem parityQuotient_source (residue : Fin 4) :
    (parityQuotient ⟨residue.val, by omega⟩).val = 4 + residue.val % 2 := by
  simp [parityQuotient, residue.isLt]

/-- The concrete precomputed quotient table has the same polynomial-time
storage contract as the generic catalogue operation. -/
theorem parity_contract :
    Realization.Realizes (representation (FixedPresentation.fin 6))
      (representation (FixedPresentation.fin 6)) (valid (FixedPresentation.fin 6))
      (fun sizes initial final => final = advance (FixedPresentation.fin 6) parityQuotient sizes initial) := by
  let slotNontrivial : Nontrivial (FixedPresentation.fin 6).Carrier := inferInstanceAs (Nontrivial (Fin 6))
  exact contract (FixedPresentation.fin 6) (fun (_sort : Unit) => parityQuotient) ()

/-- An inactive column is preserved even when its stored value is not padding. -/
theorem inactive_preserved (slots : FixedPresentation.{slotLevel})
    (operation : slots.Carrier → slots.Carrier) (sizes : SizeAssignment context)
    (value : Value slots sizes) (bounded : valid slots sizes value)
    (row : Fin (sizes .K)) (column : Fin (sizes .L)) (inactive : value.1 ≤ column.val) :
    (advance slots operation sizes value).2.2.2 row column = value.2.2.2 row column := by
  have specification := advance_spec slots operation sizes value bounded
  have different : column.val ≠ value.2.2.1 := by omega
  simpa only [different, and_false, ite_false] using specification.2.2.2 row column

end ConcreteQuotient
end Polytime.Examples.CatalogueMap
