import Polytime2.Complexity.CookLevin.MachineLayout

/-! # Certified starting wire of a machine transition block

The input coordinates are an actual time step and an actual tape-window cell.
The selected output bit is fixed specialization data. The output is the start
of that block in the mathematical unrolled circuit; all arithmetic capacities
are derived from the full wire layout.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

/-- False names the time coordinate, true the window-cell coordinate. -/
noncomputable def blockBaseInputs : Bool → EncodedDomain Unit :=
  fun name => if name then arrayPosition layoutPositions else arrayPosition (MvPolynomial.X ())

private noncomputable def blockTime (sizes : Unit → ℕ)
    (arguments : ∀ name, (blockBaseInputs name).Carrier sizes) : Fin (sizes ()) :=
  (arguments false).cast (by simp)

/-- Mathematical start wire for one output bit of one local transition. -/
noncomputable def blockBase (bit : Fin (cellWidth Symbol State)) : Computation Unit Bool :=
  specification blockBaseInputs (arrayPosition (layoutWires Symbol State)) (fun _ _ => True)
    (fun sizes arguments =>
      ⟨cellBaseValue sizes (blockTime sizes arguments.val) (arguments.val true) bit,
        cellBase_bounded sizes (blockTime sizes arguments.val) (arguments.val true) bit⟩)

theorem blockBase_correct (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (blockBase bit).Arguments sizes) :
    ((blockBase bit).compute sizes ⟨arguments, trivial⟩).val =
      MvPolynomial.eval sizes (layoutWidth Symbol State) +
        (arguments false).val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
        (arguments true).val * (cellWidth Symbol State * cellBlockSize Symbol State) +
        bit.val * cellBlockSize Symbol State := by
  simp only [blockBase, specification_compute, cellBaseValue, blockTime, Fin.val_cast]

theorem blockBase_result_fits (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (blockBase bit).Arguments sizes) :
    ((blockBase bit).compute sizes ⟨arguments, trivial⟩).val + cellBlockSize Symbol State ≤
      MvPolynomial.eval sizes (layoutWires Symbol State) := by
  simp only [blockBase, specification_compute]
  exact cellBase_fits sizes (blockTime sizes arguments) (arguments true) bit

theorem blockBase_realizable (bit : Fin (cellWidth Symbol State)) : (blockBase bit).Realizable := by
  let wires := layoutWires Symbol State
  let inputs := blockBaseInputs
  let allowed : ∀ sizes, (∀ name, (inputs name).Carrier sizes) → Prop := fun _ _ => True
  let readTime := (wireOfPosition (MvPolynomial.X ()) wires (layoutTime_le_wires (Symbol := Symbol) (State := State))).withArguments
    inputs (MultiTape.oneTape false) (fun _ => rfl)
  have readTimeReady : readTime.Realizable :=
    (wireOfPosition_realizable (MvPolynomial.X ()) wires (layoutTime_le_wires (Symbol := Symbol) (State := State))).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)
  let readCell := (wireOfPosition layoutPositions wires (layoutPositions_le_wires (Symbol := Symbol) (State := State))).withArguments
    inputs (MultiTape.oneTape true) (fun _ => rfl)
  have readCellReady : readCell.Realizable :=
    (wireOfPosition_realizable layoutPositions wires (layoutPositions_le_wires (Symbol := Symbol) (State := State))).withArguments
      inputs (MultiTape.oneTape true) (fun _ => rfl)
  let readLayer := (positionPolynomial (layoutLayerGates Symbol State) wires).onResults inputs allowed
    (fun empty => nomatch empty) (by
      intro sizes arguments
      exact layoutLayer_bounded sizes (blockTime sizes arguments.val))
  have readLayerReady : readLayer.Realizable := by
    apply (positionPolynomial_realizable (layoutLayerGates Symbol State) wires).onResults
    intro empty
    exact nomatch empty
  let stride := cellWidth Symbol State * cellBlockSize Symbol State
  have fullBound (sizes : Unit → ℕ) (arguments : ∀ name, (inputs name).Carrier sizes) :
      MvPolynomial.eval sizes (layoutWidth Symbol State) +
        (arguments false).val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
        (arguments true).val * stride + bit.val * cellBlockSize Symbol State < MvPolynomial.eval sizes wires := by
    simpa only [cellBaseValue, blockTime, Fin.val_cast, wires, stride] using
      cellBase_bounded sizes (blockTime sizes arguments) (arguments true) bit
  let timeOffset := (wireMultiply wires).onResults inputs allowed
    (fun choice sizes arguments => if choice then readLayer.compute sizes arguments else readTime.compute sizes arguments)
    (by
      intro sizes arguments
      change (arguments.val false).val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) < MvPolynomial.eval sizes wires
      have fits := fullBound sizes arguments.val
      omega)
  have timeOffsetReady : timeOffset.Realizable := by
    apply (wireMultiply_realizable wires).onResults
    intro choice
    cases choice
    · exact readTimeReady
    · exact readLayerReady
  let prefixValue := layoutWidth Symbol State + MvPolynomial.C (bit.val * cellBlockSize Symbol State)
  let cellAddress := readCell.followedBy (wireAffine wires prefixValue stride) rfl (by
    intro sizes arguments allowed
    change MvPolynomial.eval sizes prefixValue + stride * (arguments true).val < MvPolynomial.eval sizes wires
    have fits := fullBound sizes arguments
    simp only [prefixValue, map_add, MvPolynomial.eval_C]
    rw [Nat.mul_comm stride]
    omega)
  have cellAddressReady : cellAddress.Realizable :=
    readCellReady.followedBy (wireAffine_realizable wires prefixValue stride) rfl _
  have complete := (wireAdd_realizable wires).onResults inputs allowed
    (fun choice sizes arguments => if choice then timeOffset.compute sizes arguments else cellAddress.compute sizes arguments)
    (by
      intro sizes arguments
      change MvPolynomial.eval sizes prefixValue + stride * (arguments.val true).val +
        (arguments.val false).val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) < MvPolynomial.eval sizes wires
      have fits := fullBound sizes arguments.val
      simp only [prefixValue, map_add, MvPolynomial.eval_C]
      rw [Nat.mul_comm stride]
      omega)
    (by
      intro choice
      cases choice
      · exact cellAddressReady
      · exact timeOffsetReady)
  unfold blockBase
  apply complete.specification
  intro sizes arguments valid
  apply Fin.ext
  change MvPolynomial.eval sizes prefixValue + stride * (arguments true).val +
    (arguments false).val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) =
      cellBaseValue sizes (blockTime sizes arguments) (arguments true) bit
  simp only [prefixValue, stride, map_add, MvPolynomial.eval_C, cellBaseValue, blockTime, Fin.val_cast]
  ring

end Polytime2.Complexity.CookLevin
