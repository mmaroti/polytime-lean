import Polytime2.Complexity.CookLevin.FinalWire
import Polytime2.Complexity.CookLevin.Acceptance
import Polytime2.Arrays.Tabulate

/-! # Uniform acceptance-observer references

Each possible accepting head position is shifted into the finite tape window.
For each machine state, the constructor reads the final one-hot wire of the
accepting marked cell. The output ordering is that of acceptingObservations.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

private noncomputable def headPositions : MvPolynomial Unit ℕ := 2 * MvPolynomial.X () + 1

private noncomputable def headCell : Computation Unit Unit :=
  specification (fun _ => arrayPosition headPositions) (arrayPosition layoutPositions) (fun _ _ => True)
    (fun sizes arguments => ⟨(arguments.val ()).val + sizes (), by
      have bounded : (arguments.val ()).val < MvPolynomial.eval sizes headPositions := (arguments.val ()).isLt
      simp only [headPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X] at bounded
      simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
      omega⟩)

private theorem headPositions_le_window (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes headPositions ≤ MvPolynomial.eval sizes layoutPositions := by
  simp only [headPositions, layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
  omega

private theorem headCell_realizable : headCell.Realizable := by
  have shifted := (wireOfPosition_realizable headPositions layoutPositions headPositions_le_window).followedBy
    (wireAffine_realizable layoutPositions (MvPolynomial.X ()) 1) rfl (by
      intro sizes arguments accepted
      change MvPolynomial.eval sizes (MvPolynomial.X ()) + 1 *
        ((wireOfPosition headPositions layoutPositions headPositions_le_window).compute sizes ⟨arguments, accepted⟩).val <
          MvPolynomial.eval sizes layoutPositions
      rw [wireOfPosition_value]
      have bounded : (arguments ()).val < MvPolynomial.eval sizes headPositions := (arguments ()).isLt
      simp only [headPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X] at bounded
      simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X, Nat.one_mul]
      omega)
  apply shifted.withSpecification headCell.precondition headCell.compute (by intros; trivial)
  intro sizes arguments accepted
  apply Fin.ext
  simp only [headCell, specification_compute]
  change MvPolynomial.eval sizes (MvPolynomial.X ()) + 1 *
    ((wireOfPosition headPositions layoutPositions headPositions_le_window).compute sizes ⟨arguments, trivial⟩).val =
      (arguments ()).val + sizes ()
  rw [wireOfPosition_value, MvPolynomial.eval_X]
  change sizes () + 1 * (arguments ()).val = (arguments ()).val + sizes ()
  omega

private noncomputable def stateReferences (accepting : Symbol) : Computation Unit Unit where
  inputDomains _ := arrayPosition headPositions
  outputDomain := record (Fintype.card State) (fun _ => arrayPosition (layoutWires Symbol State))
  precondition _ _ := True
  compute sizes arguments state := (finalWire ((Fintype.equivFin (Cell Symbol State))
    (accepting, some ((Fintype.equivFin State).symm state)))).compute sizes
      ⟨(fun _ => headCell.compute sizes arguments), trivial⟩

private theorem stateReferences_realizable (accepting : Symbol) :
    (stateReferences (State := State) accepting).Realizable := by
  apply Realizable.recordOutputs
  intro state
  exact headCell_realizable.followedBy
    (finalWire_realizable ((Fintype.equivFin (Cell Symbol State))
      (accepting, some ((Fintype.equivFin State).symm state)))) rfl (by intros; trivial)

/-- Final wire references for every reachable accepting head position and
machine state, in the explicit mathematical observation order. -/
noncomputable def acceptanceReferences (accepting : Symbol) : Computation Unit Empty :=
  arrayTabulate (fun empty => nomatch empty) (stateReferences (State := State) accepting).outputDomain headPositions
    (fun sizes _ position => (stateReferences (State := State) accepting).compute sizes ⟨(fun _ => position), trivial⟩)

theorem acceptanceReferences_realizable (accepting : Symbol) :
    (acceptanceReferences (State := State) accepting).Realizable := by
  unfold acceptanceReferences
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Unit :=
    Sum.elim (fun empty => nomatch empty) (fun _ => arrayPosition headPositions)
  have prepared := (stateReferences_realizable (State := State) accepting).onArguments inputs (fun _ _ => True)
    (fun _ => Sum.inr ()) (by intros; rfl) (by intros; trivial)
  exact prepared.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

/-- Each emitted reference selects precisely the corresponding accepting
one-hot cell in the final layer of mathematical unrolling. -/
theorem acceptanceReferences_correct (accepting : Symbol) (sizes : Unit → ℕ)
    (arguments : (acceptanceReferences (State := State) accepting).Arguments sizes)
    (position : Fin (2 * sizes () + 1)) (state : Fin (Fintype.card State)) :
    ((acceptanceReferences (State := State) accepting).compute sizes ⟨arguments, trivial⟩
      (position.cast (by simp [headPositions])) state).val =
      stepInputWire (MvPolynomial.eval sizes layoutPositions * cellWidth Symbol State)
        (cellBlockSize Symbol State) (sizes ())
        (finProdFinEquiv (⟨position.val + sizes (), by
          have bounded := position.isLt
          simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
          omega⟩, (Fintype.equivFin (Cell Symbol State))
            (accepting, some ((Fintype.equivFin State).symm state)))) := by
  simp only [acceptanceReferences, arrayTabulate, stateReferences]
  rw [finalWire_correct]
  congr 1
  apply Fin.ext
  simp only [headCell, specification_compute, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_cast]

end Polytime2.Complexity.CookLevin
