import Polytime2.Graph.LiteralEvaluation
import Polytime2.Arrays.FlattenRecords
import Polytime2.Arrays.FiniteSubsets
import Polytime2.Complexity.Realizable

/-! # Certified construction of the forward clique witness

Select one position per clause, expand each position to three membership bits,
flatten in clause order, and return the actual finite subset of vertices.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def positionDomain : EncodedDomain Parameter :=
  (fixed (Parameter := Empty) (Equiv.refl (Fin 3))).constant

private noncomputable def positionFlags : Computation Parameter Unit :=
  Computation.mk (fun _ => positionDomain) (record 3 (fun _ => booleans))
    (fun _ _ => True) (fun _ arguments position => decide (position = arguments.val ()))

private theorem positionFlags_realizable : (positionFlags (Parameter := Parameter)).Realizable := by
  apply Realizable.recordOutputs
  intro position
  exact finitePredicate_realizable (fixed (Equiv.refl (Fin 3))) (fun selected => decide (position = selected))

/-- One numbered vertex per selected clause position. -/
noncomputable def positionsClique (clauses : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((mapArray positionDomain (record 3 (fun _ => booleans)) clauses
      (fun _ selected position => decide (position = selected))).followedBy
    (arrayFlattenRecords booleans 3 clauses) rfl (by intros; trivial)).followedBy
      (finiteSubsetFromFlags (clauses * MvPolynomial.C 3)) rfl (by intros; trivial)

theorem positionsClique_realizable (clauses : MvPolynomial Parameter ℕ) :
    (positionsClique clauses).Realizable :=
  ((mapArray_realizable positionDomain (record 3 (fun _ => booleans)) clauses
      (fun _ selected position => decide (position = selected)) positionFlags_realizable).followedBy
    (arrayFlattenRecords_realizable booleans 3 clauses) rfl (by intros; trivial)).followedBy
      (finiteSubsetFromFlags_realizable (clauses * MvPolynomial.C 3)) rfl (by intros; trivial)

/-- Construct the numbered candidate finset. Satisfying assignments produce
actual cliques, as `forwardClique_isNClique` proves. -/
noncomputable def forwardClique (wires clauses : MvPolynomial Parameter ℕ) : Computation Parameter Bool :=
  (chooseFormulaPositions wires clauses).followedBy (positionsClique clauses) rfl (by intros; trivial)

theorem forwardClique_realizable (wires clauses : MvPolynomial Parameter ℕ) :
    (forwardClique wires clauses).Realizable :=
  (chooseFormulaPositions_realizable wires clauses).followedBy (positionsClique_realizable clauses)
    rfl (by intros; trivial)


/-- Clause order followed by literal position is the canonical vertex order. -/
noncomputable def occurrenceNumbering (clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ) :
    Occurrence (MvPolynomial.eval sizes clauses) ≃
      Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3)) :=
  finProdFinEquiv.trans (finCongr (by simp))

/-- The graph on the exact numbered finite vertex set used by the codec. -/
noncomputable def numberedOccurrenceGraph (wires clauses : MvPolynomial Parameter ℕ)
    (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires))) :
    SimpleGraph (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))) :=
  (occurrenceGraph input).map (occurrenceNumbering clauses sizes).toEmbedding

/-- Membership in the constructed finite subset selects exactly one position
in each clause. -/
theorem positionsClique_mem (clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (positions : Fin (MvPolynomial.eval sizes clauses) → Fin 3)
    (vertex : Occurrence (MvPolynomial.eval sizes clauses)) :
    occurrenceNumbering clauses sizes vertex ∈
      (show Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))) from
        (positionsClique clauses).compute sizes ⟨fun _ => positions, trivial⟩) ↔
      vertex.2 = positions vertex.1 := by
  classical
  dsimp only [positionsClique, followedBy]
  rw [finiteSubsetFromFlags_mem]
  simp [arrayFlattenRecords, encodingMap, unaryMap, mapArray, MatrixEncoding.flattenEquiv,
    occurrenceNumbering]


/-- The certified construction returns exactly the mathematical witness,
transported through the canonical occurrence numbering. -/
theorem forwardClique_compute (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (assignment : Fin (MvPolynomial.eval sizes wires) → Bool) :
    (forwardClique wires clauses).compute sizes
      ⟨(fun name => match name with | false => input | true => assignment), trivial⟩ =
      (assignmentClique input assignment).map (occurrenceNumbering clauses sizes).toEmbedding := by
  classical
  apply Finset.ext
  intro index
  obtain ⟨vertex, rfl⟩ := (occurrenceNumbering clauses sizes).surjective index
  change occurrenceNumbering clauses sizes vertex ∈
    (show Finset (Fin (MvPolynomial.eval sizes (clauses * MvPolynomial.C 3))) from
      (positionsClique clauses).compute sizes
        ⟨fun _ => assignmentPositions input assignment, trivial⟩) ↔ _
  rw [positionsClique_mem]
  have mapped : (occurrenceNumbering clauses sizes) vertex ∈
      (assignmentClique input assignment).map (occurrenceNumbering clauses sizes).toEmbedding ↔
      vertex ∈ assignmentClique input assignment := by
    simp
  rw [mapped]
  rcases vertex with ⟨row, position⟩
  simp [assignmentClique, Prod.mk.injEq, eq_comm]

/-- Every satisfying assignment produces a clique of exactly the clause count
in the actual numbered output graph. -/
theorem forwardClique_isNClique (wires clauses : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (input : Fin (MvPolynomial.eval sizes clauses) → Clause (Fin (MvPolynomial.eval sizes wires)))
    (assignment : Fin (MvPolynomial.eval sizes wires) → Bool)
    (satisfied : Formula.Satisfied assignment (List.ofFn input)) :
    (numberedOccurrenceGraph wires clauses sizes input).IsNClique (MvPolynomial.eval sizes clauses)
      ((forwardClique wires clauses).compute sizes
        ⟨(fun name => match name with | false => input | true => assignment), trivial⟩) := by
  rw [forwardClique_compute]
  exact (assignmentClique_isNClique input assignment satisfied).map


/-- Standalone finite-machine realization of the complete forward witness. -/
theorem forwardClique_tm0 (wires clauses : MvPolynomial Parameter ℕ) :
    (forwardClique wires clauses).TM0Realizable :=
  (forwardClique_realizable wires clauses).tm0

/-- Time and witness length are polynomial in the complete source encoding,
including every unary size header, the formula, and the assignment. -/
theorem forwardClique_polynomialTime (wires clauses : MvPolynomial Parameter ℕ) :
    Complexity.PolynomialTime (forwardClique wires clauses).inputWord
      (forwardClique wires clauses).outputWord (forwardClique wires clauses).result :=
  (forwardClique_realizable wires clauses).polynomialTime

end Polytime2.SAT
