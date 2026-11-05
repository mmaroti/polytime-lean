import Polytime2.Graph.Reduction

/-! # Edge cases of the certified occurrence-graph reduction

These checks cover empty formulas (including zero variables), repeated
literals, contradictory occurrences, and variables absent from the formula.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT.Examples

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Zero clauses produce the required empty clique, for any variable count. -/
theorem empty_graph (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (empty : MvPolynomial.eval sizes clauses = 0)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires))) :
    ((cliqueGraph wires clauses).compute sizes ⟨fun _ => formula, trivial⟩).IsNClique
      (MvPolynomial.eval sizes clauses) ∅ := by
  simpa only [empty] using (SimpleGraph.isNClique_empty.mpr rfl :
    ((cliqueGraph wires clauses).compute sizes ⟨fun _ => formula, trivial⟩).IsNClique 0 ∅)

/-- With zero clauses, reverse transport returns false for every variable. -/
theorem empty_assignment (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (empty : MvPolynomial.eval sizes clauses = 0)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (selected : Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))))
    (atom : Fin (MvPolynomial.eval sizes wires)) :
    (reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩ atom = false := by
  apply reverseClique_absent
  intro row
  exact Fin.elim0 (row.cast empty)

/-- In particular, the completely empty source has a satisfying assignment. -/
example : Formula.Satisfiable (List.ofFn (fun row : Fin 0 => Fin.elim0 row : Fin 0 → Clause (Fin 0))) := by
  simpa using (Formula.satisfiable_nil (Variable := Fin 0))

private def repeatedOpposites : Fin 2 → Clause (Fin 1) :=
  fun row _ => (0, decide (row = 1))

private theorem repeatedOpposites_unsatisfiable :
    ¬ Formula.Satisfiable (List.ofFn repeatedOpposites) := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied (repeatedOpposites 0) (List.mem_ofFn.mpr ⟨0, rfl⟩)
  have negative := satisfied (repeatedOpposites 1) (List.mem_ofFn.mpr ⟨1, rfl⟩)
  simp [repeatedOpposites, Clause.Satisfied, Literal.Satisfied] at positive negative
  simp [positive] at negative

/-- Two opposite repeated unit clauses cannot produce a two-clique. -/
example : ¬ ∃ selected, (occurrenceGraph repeatedOpposites).IsNClique 2 selected :=
  fun clique => repeatedOpposites_unsatisfiable
    ((satisfiable_iff_occurrence_clique repeatedOpposites).mpr clique)

/-- Opposite occurrences have no edge even when they belong to distinct clauses. -/
example : ¬ (occurrenceGraph repeatedOpposites).Adj (0, 0) (1, 0) := by
  simp [occurrenceGraph, repeatedOpposites, Literal.Compatible]

/-- Repeated positive literals remain satisfiable and give a full-size clique. -/
example : ∃ selected, (occurrenceGraph (fun _ : Fin 2 => fun _ : Fin 3 =>
    ((0 : Fin 2), false))).IsNClique 2 selected := by
  apply (satisfiable_iff_occurrence_clique _).mp
  refine ⟨fun _ => true, ?_⟩
  intro clause member
  obtain ⟨row, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨0, by simp [Literal.Satisfied]⟩

/-- The unused second variable receives false, regardless of the chosen subset. -/
example (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (first second : Fin (MvPolynomial.eval sizes wires)) (different : first ≠ second)
    (selected : Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3)))) :
    (reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with
        | false => fun _ _ => (first, false) | true => selected), trivial⟩ second = false := by
  exact reverseClique_absent wires clauses sizes (fun _ _ => (first, false)) selected second
    (fun _ _ => different)

end Polytime2.SAT.Examples
