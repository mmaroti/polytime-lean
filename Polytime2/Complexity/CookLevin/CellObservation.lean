import Polytime2.Complexity.CookLevin.CellCircuit

/-! # Linear-size observations of one-hot cell arrays

An explicit list of position/cell pairs supplies the one-hot wires to disjoin.
Its length determines the exact observer size; no filtering is needed during
uniform circuit construction. Observing never copies the simulated circuit.
-/

namespace Polytime2.Complexity.CookLevin

open Circuit

variable {Symbol State : Type} [Fintype Symbol] [Fintype State]

/-- One wire for each explicitly observed position/cell pair. -/
noncomputable def observedCellWires {positions : ℕ}
    (observed : List (Fin positions × Cell Symbol State)) : List ℕ :=
  observed.map (fun observation =>
    (finProdFinEquiv (observation.1, (Fintype.equivFin (Cell Symbol State)) observation.2)).val)

theorem observedCellWires_valid {positions : ℕ}
    (observed : List (Fin positions × Cell Symbol State)) :
    ∀ wire ∈ observedCellWires observed, wire < positions * cellWidth Symbol State := by
  intro wire member
  obtain ⟨observation, _member, equal⟩ := List.mem_map.mp member
  exact equal ▸ (finProdFinEquiv (observation.1, (Fintype.equivFin (Cell Symbol State)) observation.2)).isLt

/-- The observer accepts exactly when one of its listed cells occurs. -/
theorem observedCellWires_correct {positions : ℕ}
    (observed : List (Fin positions × Cell Symbol State)) (contents : Fin positions → Cell Symbol State) :
    (observedCellWires observed).any (inputValues (encodeCells contents)) = true ↔
      ∃ observation ∈ observed, contents observation.1 = observation.2 := by
  classical
  simp only [observedCellWires, List.any_map, List.any_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨observation, member, hit⟩
    refine ⟨observation, member, ?_⟩
    simpa only [inputValues, dite_eq_left (finProdFinEquiv
      (observation.1, (Fintype.equivFin (Cell Symbol State)) observation.2)).isLt,
      Fin.eta, encodeCells, Equiv.symm_apply_apply, encodeCell, Equiv.symm_apply_apply, decide_eq_true_eq] using hit
  · rintro ⟨observation, member, equal⟩
    refine ⟨observation, member, ?_⟩
    simp only [inputValues, dite_eq_left (finProdFinEquiv
      (observation.1, (Fintype.equivFin (Cell Symbol State)) observation.2)).isLt,
      Fin.eta, encodeCells, Equiv.symm_apply_apply, encodeCell, Equiv.symm_apply_apply, equal, decide_true]

/-- Compile finite cell dynamics and the explicitly listed final observations. -/
noncomputable def cellObservationCircuit [Inhabited Symbol] (positions steps : ℕ)
    (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (observed : List (Fin positions × Cell Symbol State)) : Network :=
  localObservationCircuit (positions * cellWidth Symbol State) (3 * cellWidth Symbol State) steps
    (cellSources positions neighbors) (cellTables positions update)
    (Expression.anyWire (observedCellWires observed))

theorem cellObservationCircuit_spec [Inhabited Symbol] (positions steps : ℕ)
    (neighbors : Fin positions → Fin 3 → Fin positions)
    (update : Fin positions → (Fin 3 → Cell Symbol State) → Cell Symbol State)
    (observed : List (Fin positions × Cell Symbol State)) :
    Circuit.Valid (positions * cellWidth Symbol State)
      (cellObservationCircuit positions steps neighbors update observed) ∧
    (cellObservationCircuit positions steps neighbors update observed).1.length ≤
      steps * (positions * cellWidth Symbol State) * (5 * 2 ^ (3 * cellWidth Symbol State)) +
        (5 * observed.length + 1) ∧
    ∀ contents, evaluate (positions * cellWidth Symbol State)
      (cellObservationCircuit positions steps neighbors update observed) (encodeCells contents) = true ↔
        ∃ observation ∈ observed,
          (cellTransition neighbors update)^[steps] contents observation.1 = observation.2 := by
  have specification := localObservationCircuit_spec _ _ steps (cellSources positions neighbors)
    (cellTables positions update) _ (Expression.anyWire_valid (observedCellWires_valid observed))
  refine ⟨specification.1, ?_, ?_⟩
  · simpa only [cellObservationCircuit, Expression.anyWire_gateCount, observedCellWires, List.length_map] using specification.2.1
  · intro contents
    rw [show evaluate _ (cellObservationCircuit positions steps neighbors update observed)
        (encodeCells contents) = _ from specification.2.2 (encodeCells contents),
      cellTransition_iterate_encode, Expression.anyWire_eval, observedCellWires_correct]

end Polytime2.Complexity.CookLevin
