import Polytime2.Graph.ReverseClique

/-! # Polynomial three-SAT to CLIQUE reduction with certified witnesses

`cliqueGraph` constructs an ordinary simple graph; the required clique size is
the source clause count. Both witness conversions are total certified
computations, with correctness under their mathematical witness hypotheses.
This is a reduction between encoded mathematical instances. It does not claim
an all-word CLIQUE NP-completeness theorem.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- The actual certified graph has a clique of the clause count exactly when
the source formula is satisfiable. Both directions use the certified witness
algorithms, with no positivity assumption on either size. -/
theorem cliqueGraph_correct (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires))) :
    Formula.Satisfiable (List.ofFn formula) ↔
      ∃ selected, ((cliqueGraph wires clauses).compute sizes ⟨fun _ => formula, trivial⟩).IsNClique
        (MvPolynomial.eval sizes clauses) selected := by
  constructor
  · rintro ⟨assignment, satisfied⟩
    exact ⟨(forwardClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => assignment), trivial⟩,
      forwardClique_isNClique wires clauses sizes formula assignment satisfied⟩
  · rintro ⟨selected, clique⟩
    exact ⟨(reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩,
      reverseClique_satisfied wires clauses sizes formula selected clique⟩

omit [Fintype Parameter] in
/-- The graph has exactly three vertices per clause, independently of the
number of variables. -/
theorem cliqueGraph_vertexCount (clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    Fintype.card (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))) =
      3 * MvPolynomial.eval sizes clauses := by simp [Nat.mul_comm]

/-- The complete graph payload has exactly nine bits per ordered clause pair.
Runtime is measured against source words including their size headers. -/
theorem cliqueGraph_outputWidth (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    (cliqueGraph wires clauses).outputDomain.width sizes =
      9 * (MvPolynomial.eval sizes clauses) ^ 2 := by
  change (simpleGraphs (clauses * MvPolynomial.C 3)).width sizes = _
  rw [simpleGraphs_width]
  simp only [map_mul, MvPolynomial.eval_C]
  ring

/-- Variables absent from the formula receive false for every supplied subset,
without requiring that the subset is a clique. -/
theorem reverseClique_absent (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (formula : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (selected : Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))))
    (atom : Fin (MvPolynomial.eval sizes wires))
    (absent : ∀ row position, (formula row position).1 ≠ atom) :
    (reverseClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => formula | true => selected), trivial⟩ atom = false := by
  classical
  have absentValue : cliqueAssignment formula
      (selected.map (occurrenceNumbering clauses sizes).symm.toEmbedding) atom = false := by
    simp only [cliqueAssignment, decide_eq_false_iff_not]
    rintro ⟨vertex, _, literal⟩
    exact absent vertex.1 vertex.2 (congrArg Prod.fst literal)
  exact (congrFun (reverseClique_compute wires clauses sizes formula selected) atom).trans absentValue

end Polytime2.SAT
