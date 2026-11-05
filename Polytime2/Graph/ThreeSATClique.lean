import Polytime2.SAT.ThreeSAT
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.FinCases

/-! # The occurrence graph of a three-literal formula

Vertices are actual clause occurrences and literal positions. Edges join
occurrences from different clauses whose literals can hold simultaneously.
The graph and witness contracts are independent of encodings and machines.
-/

namespace Polytime2.SAT

universe variableLevel
variable {Variable : Type variableLevel} {count : ℕ}

/-- Literal occurrences retain repeated clauses and repeated literals. -/
abbrev Occurrence (count : ℕ) := Fin count × Fin 3

/-- Two literals are compatible unless they demand opposite values of the
same variable. -/
def Literal.Compatible (first second : Literal Variable) : Prop :=
  first.1 ≠ second.1 ∨ first.2 = second.2

/-- The standard simple occurrence graph, with no edges within a clause. -/
def occurrenceGraph (clauses : Fin count → Clause Variable) : SimpleGraph (Occurrence count) where
  Adj first second := first.1 ≠ second.1 ∧
    Literal.Compatible (clauses first.1 first.2) (clauses second.1 second.2)
  symm := ⟨by
    intro first second adjacent
    exact ⟨adjacent.1.symm, adjacent.2.elim (fun distinct => Or.inl distinct.symm)
      (fun equal => Or.inr equal.symm)⟩⟩
  loopless := ⟨by intro vertex adjacent; exact adjacent.1 rfl⟩

/-- A fixed three-way choice, suitable for a finite-table realization. -/
def truePosition (flags : Fin 3 → Bool) : Fin 3 :=
  if flags 0 then 0 else if flags 1 then 1 else 2

theorem truePosition_true (flags : Fin 3 → Bool) (present : ∃ index, flags index = true) :
    flags (truePosition flags) = true := by
  unfold truePosition
  split_ifs with first second
  · exact first
  · exact second
  · obtain ⟨index, accepted⟩ := present
    fin_cases index <;> simp_all

/-- Select a true literal in each clause, using the fixed three-way choice. -/
noncomputable def assignmentPositions (clauses : Fin count → Clause Variable)
    (assignment : Variable → Bool) : Fin count → Fin 3 := by
  classical
  exact fun clause => truePosition (fun position => decide (Literal.Satisfied assignment (clauses clause position)))

/-- Forward witness: one selected occurrence per clause. -/
noncomputable def assignmentClique (clauses : Fin count → Clause Variable)
    (assignment : Variable → Bool) : Finset (Occurrence count) :=
  Finset.univ.image (fun clause => (clause, assignmentPositions clauses assignment clause))

theorem assignmentPositions_satisfied (clauses : Fin count → Clause Variable)
    (assignment : Variable → Bool) (satisfied : Formula.Satisfied assignment (List.ofFn clauses))
    (clause : Fin count) : Literal.Satisfied assignment
      (clauses clause (assignmentPositions clauses assignment clause)) := by
  classical
  apply of_decide_eq_true
  change (fun position => decide (Literal.Satisfied assignment (clauses clause position)))
    (truePosition (fun position => decide (Literal.Satisfied assignment (clauses clause position)))) = true
  obtain ⟨position, accepted⟩ := satisfied _ (List.mem_ofFn.mpr ⟨clause, rfl⟩)
  exact truePosition_true (fun position => decide (Literal.Satisfied assignment (clauses clause position)))
    ⟨position, decide_eq_true accepted⟩

theorem assignmentClique_isNClique (clauses : Fin count → Clause Variable)
    (assignment : Variable → Bool) (satisfied : Formula.Satisfied assignment (List.ofFn clauses)) :
    (occurrenceGraph clauses).IsNClique count (assignmentClique clauses assignment) := by
  classical
  refine ⟨?_, ?_⟩
  · intro first firstMember second secondMember different
    obtain ⟨firstClause, _, rfl⟩ := Finset.mem_image.mp firstMember
    obtain ⟨secondClause, _, rfl⟩ := Finset.mem_image.mp secondMember
    have clauseDifferent : firstClause ≠ secondClause := by
      intro equal
      subst secondClause
      exact different rfl
    refine ⟨clauseDifferent, ?_⟩
    by_cases sameVariable : (clauses firstClause (assignmentPositions clauses assignment firstClause)).1 =
        (clauses secondClause (assignmentPositions clauses assignment secondClause)).1
    · right
      have firstTrue := assignmentPositions_satisfied clauses assignment satisfied firstClause
      have secondTrue := assignmentPositions_satisfied clauses assignment satisfied secondClause
      unfold Literal.Satisfied at firstTrue secondTrue
      rw [sameVariable] at firstTrue
      cases firstBit : (clauses firstClause (assignmentPositions clauses assignment firstClause)).2 <;>
        cases secondBit : (clauses secondClause (assignmentPositions clauses assignment secondClause)).2 <;>
        cases assigned : assignment (clauses secondClause (assignmentPositions clauses assignment secondClause)).1 <;>
        simp_all
    · exact Or.inl sameVariable
  · rw [assignmentClique, Finset.card_image_iff.mpr]
    · exact Finset.card_fin _
    · intro first _ second _ equal
      exact congrArg Prod.fst equal


/-- A clique has at most one occurrence in each clause. -/
theorem clique_clause_injective (clauses : Fin count → Clause Variable)
    (selected : Finset (Occurrence count)) (clique : (occurrenceGraph clauses).IsClique selected) :
    Set.InjOn Prod.fst (selected : Set (Occurrence count)) := by
  intro first firstMember second secondMember equal
  by_contra different
  exact (clique firstMember secondMember different).1 equal

/-- A clique of the required cardinality meets every clause. -/
theorem clique_meets_clause (clauses : Fin count → Clause Variable)
    (selected : Finset (Occurrence count))
    (clique : (occurrenceGraph clauses).IsNClique count selected) (clause : Fin count) :
    ∃ position, (clause, position) ∈ selected := by
  classical
  have imageCard : (selected.image Prod.fst).card = count :=
    (Finset.card_image_iff.mpr (clique_clause_injective clauses selected clique.isClique)).trans clique.card_eq
  have imageAll : selected.image Prod.fst = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using imageCard.ge)
  have member : clause ∈ selected.image Prod.fst := by rw [imageAll]; exact Finset.mem_univ _
  obtain ⟨vertex, present, equal⟩ := Finset.mem_image.mp member
  exact ⟨vertex.2, by simpa only [← equal] using present⟩

/-- Reverse witness: selected positive occurrences demand truth; all other
variables receive false, including variables absent from the formula. -/
noncomputable def cliqueAssignment (clauses : Fin count → Clause Variable)
    (selected : Finset (Occurrence count)) : Variable → Bool := by
  classical
  exact fun atom => decide (∃ vertex ∈ selected, clauses vertex.1 vertex.2 = (atom, false))

theorem cliqueAssignment_satisfies_selected (clauses : Fin count → Clause Variable)
    (selected : Finset (Occurrence count)) (clique : (occurrenceGraph clauses).IsClique selected)
    (vertex : Occurrence count) (member : vertex ∈ selected) :
    Literal.Satisfied (cliqueAssignment clauses selected) (clauses vertex.1 vertex.2) := by
  classical
  have compatible (other : Occurrence count) (present : other ∈ selected) :
      Literal.Compatible (clauses vertex.1 vertex.2) (clauses other.1 other.2) := by
    by_cases equal : vertex = other
    · subst other; exact Or.inr rfl
    · exact (clique member present equal).2
  unfold Literal.Satisfied cliqueAssignment
  cases bit : (clauses vertex.1 vertex.2).2 with
  | false =>
    have positive : ∃ other ∈ selected,
        clauses other.1 other.2 = ((clauses vertex.1 vertex.2).1, false) :=
      ⟨vertex, member, Prod.ext rfl bit⟩
    simp [positive]
  | true =>
    have negative : ¬ ∃ other ∈ selected,
        clauses other.1 other.2 = ((clauses vertex.1 vertex.2).1, false) := by
      rintro ⟨other, present, equal⟩
      have relation := compatible other present
      unfold Literal.Compatible at relation
      rw [equal] at relation
      simp [bit] at relation
    simp [negative]

/-- Every full-size clique yields an assignment satisfying every source clause. -/
theorem cliqueAssignment_satisfied (clauses : Fin count → Clause Variable)
    (selected : Finset (Occurrence count))
    (clique : (occurrenceGraph clauses).IsNClique count selected) :
    Formula.Satisfied (cliqueAssignment clauses selected) (List.ofFn clauses) := by
  intro clause member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  obtain ⟨position, present⟩ := clique_meets_clause clauses selected clique index
  exact ⟨position, cliqueAssignment_satisfies_selected clauses selected clique.isClique (index, position) present⟩

/-- Satisfiability is equivalent to a clique of exactly the clause count,
including the zero-clause formula. -/
theorem satisfiable_iff_occurrence_clique (clauses : Fin count → Clause Variable) :
    Formula.Satisfiable (List.ofFn clauses) ↔
      ∃ selected, (occurrenceGraph clauses).IsNClique count selected := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨assignmentClique clauses assignment, assignmentClique_isNClique clauses assignment satisfied⟩
  · rintro ⟨selected, clique⟩
    exact ⟨cliqueAssignment clauses selected, cliqueAssignment_satisfied clauses selected clique⟩

end Polytime2.SAT
