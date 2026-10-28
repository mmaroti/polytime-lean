import Polytime2.Complexity.CookLevin.CellTemplates

/-! # Mathematical wire layout of the bounded simulation

The sole size parameter is the time allowance. The radius is twice that
allowance, and each local output uses the fixed machine block size. Every
block address is bounded by the actual number of input and simulation wires.
The bounds also cover zero time, when there are no block coordinates.
-/

namespace Polytime2.Complexity.CookLevin

open Circuit

variable {Symbol State : Type} [Inhabited Symbol]
variable [Fintype Symbol] [Fintype State]

noncomputable def layoutPositions : MvPolynomial Unit ℕ := 4 * MvPolynomial.X () + 1

noncomputable def layoutWidth (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Unit ℕ :=
  layoutPositions * MvPolynomial.C (cellWidth Symbol State)

noncomputable def layoutLayerGates (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Unit ℕ :=
  layoutWidth Symbol State * MvPolynomial.C (cellBlockSize Symbol State)

noncomputable def layoutWires (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Unit ℕ :=
  layoutWidth Symbol State + MvPolynomial.X () * layoutLayerGates Symbol State

theorem cellWidth_positive : 0 < cellWidth Symbol State := Fintype.card_pos

theorem layoutWidth_positive (sizes : Unit → ℕ) : 0 < MvPolynomial.eval sizes (layoutWidth Symbol State) := by
  have cellPositive := cellWidth_positive (Symbol := Symbol) (State := State)
  simp only [layoutWidth, layoutPositions, map_mul, map_add, map_ofNat, map_one, MvPolynomial.eval_X,
    MvPolynomial.eval_C]
  exact Nat.mul_pos (by omega) cellPositive

theorem layoutPositions_le_wires (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes layoutPositions ≤ MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have positive := cellWidth_positive (Symbol := Symbol) (State := State)
  have scaled := Nat.mul_le_mul_left (MvPolynomial.eval sizes layoutPositions) (Nat.succ_le_of_lt positive)
  simp only [Nat.mul_one] at scaled
  simp only [layoutWires, layoutWidth, map_add, map_mul, MvPolynomial.eval_C]
  omega

theorem layoutTime_le_wires (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes (MvPolynomial.X ()) ≤ MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have positions := layoutPositions_le_wires (Symbol := Symbol) (State := State) sizes
  simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X] at positions ⊢
  omega

theorem layoutLayer_bounded (sizes : Unit → ℕ) (time : Fin (sizes ())) :
    MvPolynomial.eval sizes (layoutLayerGates Symbol State) < MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have timePositive : 1 ≤ sizes () := by have bound := time.isLt; omega
  have scaled := Nat.mul_le_mul_right (MvPolynomial.eval sizes (layoutLayerGates Symbol State)) timePositive
  simp only [Nat.one_mul] at scaled
  have widthPositive := layoutWidth_positive (Symbol := Symbol) (State := State) sizes
  simp only [layoutWires, map_add, map_mul, MvPolynomial.eval_X]
  omega

/-- Start of the block for one time, cell, and chosen output bit. -/
noncomputable def cellBaseValue (sizes : Unit → ℕ) (time : Fin (sizes ()))
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (bit : Fin (cellWidth Symbol State)) : ℕ :=
  MvPolynomial.eval sizes (layoutWidth Symbol State) +
    time.val * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
      cell.val * (cellWidth Symbol State * cellBlockSize Symbol State) + bit.val * cellBlockSize Symbol State

omit [Inhabited Symbol] in
theorem cellBase_fits (sizes : Unit → ℕ) (time : Fin (sizes ()))
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (bit : Fin (cellWidth Symbol State)) :
    cellBaseValue sizes time cell bit + cellBlockSize Symbol State ≤ MvPolynomial.eval sizes (layoutWires Symbol State) := by
  let width := MvPolynomial.eval sizes (layoutWidth Symbol State)
  let layer := MvPolynomial.eval sizes (layoutLayerGates Symbol State)
  have slotBound : cell.val * cellWidth Symbol State + bit.val < width := by
    have bounded := (finProdFinEquiv (cell, bit)).isLt
    simpa only [width, layoutWidth, map_mul, MvPolynomial.eval_C, finProdFinEquiv, Equiv.coe_fn_mk,
      Nat.mul_comm, Nat.add_comm] using bounded
  have localBound : (cell.val * cellWidth Symbol State + bit.val + 1) * cellBlockSize Symbol State ≤ layer := by
    simpa only [layer, layoutLayerGates, map_mul, MvPolynomial.eval_C] using
      Nat.mul_le_mul_right (cellBlockSize Symbol State) (Nat.succ_le_of_lt slotBound)
  have stepBound := Nat.mul_le_mul_right layer (Nat.succ_le_of_lt time.isLt)
  simp only [layoutWires, map_add, map_mul, MvPolynomial.eval_X]
  change cellBaseValue sizes time cell bit + cellBlockSize Symbol State ≤ width + sizes () * layer
  calc
    _ = width + (time.val * layer + (cell.val * cellWidth Symbol State + bit.val + 1) * cellBlockSize Symbol State) := by
      dsimp [cellBaseValue, width, layer]
      ring
    _ ≤ width + (time.val * layer + layer) := Nat.add_le_add_left (Nat.add_le_add_left localBound _) _
    _ = width + (time.val + 1) * layer := by ring
    _ ≤ width + sizes () * layer := Nat.add_le_add_left stepBound _

omit [Inhabited Symbol] in
theorem cellBase_bounded (sizes : Unit → ℕ) (time : Fin (sizes ()))
    (cell : Fin (MvPolynomial.eval sizes layoutPositions)) (bit : Fin (cellWidth Symbol State)) :
    cellBaseValue sizes time cell bit < MvPolynomial.eval sizes (layoutWires Symbol State) := by
  have fits := cellBase_fits sizes time cell bit
  have positive := cellBlockSize_positive (Symbol := Symbol) (State := State)
  omega

end Polytime2.Complexity.CookLevin
