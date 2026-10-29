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
  let bounds : Bool → MvPolynomial Unit ℕ := fun name => if name then layoutPositions else MvPolynomial.X ()
  let expression : MvPolynomial (Unit ⊕ Bool) ℕ :=
    MvPolynomial.rename Sum.inl (layoutWidth Symbol State) +
      MvPolynomial.X (Sum.inr false) * MvPolynomial.rename Sum.inl (layoutLayerGates Symbol State) +
      MvPolynomial.X (Sum.inr true) * MvPolynomial.C (cellWidth Symbol State * cellBlockSize Symbol State) +
      MvPolynomial.C (bit.val * cellBlockSize Symbol State)
  have ready := (polynomialPosition_realizable bounds expression (layoutWires Symbol State)).onArguments
    blockBaseInputs (fun _ _ => True) id (by intro name; cases name <;> rfl) (by
      intro sizes arguments
      simpa [polynomialPosition, expression, MvPolynomial.eval_rename, Function.comp_def,
        cellBaseValue, blockTime] using cellBase_bounded sizes (blockTime sizes arguments.val) (arguments.val true) bit)
  unfold blockBase
  apply ready.specification
  intro sizes arguments valid
  apply Fin.ext
  simp [polynomialPosition, expression, MvPolynomial.eval_rename, Function.comp_def,
    cellBaseValue, blockTime]

end Polytime2.Complexity.CookLevin
