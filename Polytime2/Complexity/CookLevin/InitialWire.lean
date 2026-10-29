import Polytime2.Complexity.CookLevin.BlockBase

/-! # Certified initial configuration wire coordinates

The mathematical input wire for a cell bit is its row-major configuration
coordinate. The shared transition-constructor context supplies time and cell;
only its cell coordinate determines the initial input wire.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

omit [Inhabited Symbol] in
private theorem initialWire_bounded (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : ∀ name, (blockBaseInputs name).Carrier sizes) :
    (arguments true).val * cellWidth Symbol State + bit.val <
      MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have slotBound := (finProdFinEquiv (arguments true, bit)).isLt
  have widthBound : MvPolynomial.eval sizes (layoutWidth Symbol State) ≤
      MvPolynomial.eval sizes (layoutWires Symbol State) := by
    simp only [layoutWires, map_add]
    omega
  have bounded : (arguments true).val * cellWidth Symbol State + bit.val <
      MvPolynomial.eval sizes (layoutWidth Symbol State) := by
    simpa only [layoutWidth, map_mul, MvPolynomial.eval_C, finProdFinEquiv,
      Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using slotBound
  omega

/-- Initial input wire corresponding to a window cell and fixed one-hot bit. -/
noncomputable def initialWire (bit : Fin (cellWidth Symbol State)) : Computation Unit Bool :=
  specification blockBaseInputs (arrayPosition (layoutWires Symbol State)) (fun _ _ => True)
    (fun sizes arguments => ⟨(arguments.val true).val * cellWidth Symbol State + bit.val,
      initialWire_bounded bit sizes arguments.val⟩)

theorem initialWire_correct (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (initialWire bit).Arguments sizes) :
    ((initialWire bit).compute sizes ⟨arguments, trivial⟩).val =
      (arguments true).val * cellWidth Symbol State + bit.val := by
  simp only [initialWire, specification_compute]

theorem initialWire_realizable (bit : Fin (cellWidth Symbol State)) : (initialWire bit).Realizable := by
  have ready := (polynomialPosition_realizable (fun _ : Unit => layoutPositions)
    (MvPolynomial.X (Sum.inr ()) * MvPolynomial.C (cellWidth Symbol State) + MvPolynomial.C bit.val)
    (layoutWires Symbol State)).onArguments blockBaseInputs (fun _ _ => True) (fun _ => true)
    (by intros; rfl) (by
      intro sizes arguments
      simpa [polynomialPosition] using initialWire_bounded bit sizes arguments.val)
  apply ready.withSpecification (initialWire bit).precondition (initialWire bit).compute (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  simp [onResults, polynomialPosition, initialWire, specification_compute]

end Polytime2.Complexity.CookLevin
