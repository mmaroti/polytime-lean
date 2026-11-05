import Polytime2.Graph.AdjacencyTables
import Polytime2.Graph.Encoding

/-! # Certified construction of the three-SAT occurrence graph

The output is an ordinary simple graph on exactly three vertices per clause.
The dense adjacency implementation is internal to its realization certificate.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

/-- Construct the occurrence graph without any assumption on the formula. -/
noncomputable def cliqueGraph (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  Computation.mk (fun _ => (clauseDomain wires).arrayOfLength clauses)
    (simpleGraphs (clauses * MvPolynomial.C 3)) (fun _ _ => True)
    (fun sizes arguments => numberedOccurrenceGraph wires clauses sizes (arguments.val ()))

theorem cliqueGraph_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (cliqueGraph wires clauses).Realizable := by
  classical
  apply (occurrenceAdjacencyTables_realizable wires clauses).withEncodedOutput
    (simpleGraphs (clauses * MvPolynomial.C 3)) (cliqueGraph wires clauses).compute
    (fun _ => rfl)
  intro sizes arguments
  have tables : (fun first second => decide
      ((numberedOccurrenceGraph wires clauses sizes (arguments.val ())).Adj first second)) =
      (occurrenceAdjacencyTables wires clauses).compute sizes arguments := by
    funext first second
    obtain ⟨first, rfl⟩ := (occurrenceNumbering clauses sizes).surjective first
    obtain ⟨second, rfl⟩ := (occurrenceNumbering clauses sizes).surjective second
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, numberedOccurrenceGraph]
    have argumentEq : arguments = ⟨fun _ => arguments.val (), trivial⟩ := by
      apply Subtype.ext
      funext name
      cases name
      rfl
    rw [argumentEq]
    exact (SimpleGraph.map_adj_apply (f := (occurrenceNumbering clauses sizes).toEmbedding)).trans
      (occurrenceAdjacencyTables_correct wires clauses sizes (arguments.val ()) first second).symm
  change CallingConvention.encoded ((booleans.arrayOfLength (clauses * MvPolynomial.C 3)).arrayOfLength
    (clauses * MvPolynomial.C 3)) sizes _ = _
  exact congrArg (CallingConvention.encoded
    ((booleans.arrayOfLength (clauses * MvPolynomial.C 3)).arrayOfLength
      (clauses * MvPolynomial.C 3)) sizes) tables

/-- Standalone machine for the complete graph construction. -/
theorem cliqueGraph_tm0 (wires clauses : MvPolynomial Parameter ℕ) :
    (cliqueGraph wires clauses).TM0Realizable :=
  (cliqueGraph_realizable wires clauses).tm0

/-- Construction time and output length are polynomial in the serialized formula
and its size headers. -/
theorem cliqueGraph_polynomialTime (wires clauses : MvPolynomial Parameter ℕ) :
    Complexity.PolynomialTime (cliqueGraph wires clauses).inputWord
      (cliqueGraph wires clauses).outputWord (cliqueGraph wires clauses).result :=
  (cliqueGraph_realizable wires clauses).polynomialTime

end Polytime2.SAT
