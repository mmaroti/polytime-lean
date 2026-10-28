import Polytime2.Complexity.CookLevin.InitialWire
import Polytime2.Computation.Conditional

/-! # Certified predecessor wires for machine transition blocks

At time zero the source is an initial configuration input. At later times it
is the final wire of the corresponding block in the preceding layer.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

/-- Wire carrying a chosen cell bit before the current transition. -/
noncomputable def sourceWire (bit : Fin (cellWidth Symbol State)) : Computation Unit Bool :=
  specification blockBaseInputs (arrayPosition (layoutWires Symbol State)) (fun _ _ => True)
    (fun sizes arguments => if (arguments.val false).val = 0 then
      (initialWire bit).compute sizes arguments
    else ⟨((blockBase bit).compute sizes arguments).val + (cellBlockSize Symbol State - 1) -
      MvPolynomial.eval sizes (layoutLayerGates Symbol State), by
        have fits : ((blockBase bit).compute sizes arguments).val + cellBlockSize Symbol State ≤
            MvPolynomial.eval sizes (layoutWires Symbol State) :=
          blockBase_result_fits bit sizes arguments.val
        have positive := cellBlockSize_positive (Symbol := Symbol) (State := State)
        change ((blockBase bit).compute sizes arguments).val + (cellBlockSize Symbol State - 1) -
          MvPolynomial.eval sizes (layoutLayerGates Symbol State) <
          MvPolynomial.eval sizes (layoutWires Symbol State)
        omega⟩)

/-- Direct predecessor address, independent of the arithmetic realization. -/
theorem sourceWire_correct (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (sourceWire bit).Arguments sizes) :
    ((sourceWire bit).compute sizes ⟨arguments, trivial⟩).val =
      if (arguments false).val = 0 then (arguments true).val * cellWidth Symbol State + bit.val
      else MvPolynomial.eval sizes (layoutWidth Symbol State) +
        ((arguments false).val - 1) * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
        ((arguments true).val * cellWidth Symbol State + bit.val + 1) * cellBlockSize Symbol State - 1 := by
  cases time : (arguments false).val with
  | zero => simp [sourceWire, specification_compute, time, initialWire_correct]
  | succ previous =>
    simp only [sourceWire, specification_compute, time, Nat.add_one_ne_zero, ↓reduceIte,
      blockBase_correct, Nat.add_sub_cancel]
    have positive := cellBlockSize_positive (Symbol := Symbol) (State := State)
    have widthPositive := layoutWidth_positive (Symbol := Symbol) (State := State) sizes
    have arithmetic :
        MvPolynomial.eval sizes (layoutWidth Symbol State) +
          (previous + 1) * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
          (arguments true).val * (cellWidth Symbol State * cellBlockSize Symbol State) +
          bit.val * cellBlockSize Symbol State + cellBlockSize Symbol State =
        (MvPolynomial.eval sizes (layoutWidth Symbol State) +
          previous * MvPolynomial.eval sizes (layoutLayerGates Symbol State) +
          ((arguments true).val * cellWidth Symbol State + bit.val + 1) * cellBlockSize Symbol State) +
          MvPolynomial.eval sizes (layoutLayerGates Symbol State) := by ring
    omega

/-- The direct address is the wire naming used by circuit unrolling. -/
theorem sourceWire_stepInputWire (bit : Fin (cellWidth Symbol State)) (sizes : Unit → ℕ)
    (arguments : (sourceWire bit).Arguments sizes) :
    ((sourceWire bit).compute sizes ⟨arguments, trivial⟩).val =
      stepInputWire (MvPolynomial.eval sizes layoutPositions * cellWidth Symbol State)
        (cellBlockSize Symbol State) (arguments false).val (finProdFinEquiv (arguments true, bit)) := by
  rw [sourceWire_correct]
  cases time : (arguments false).val <;>
    simp [stepInputWire, layoutWidth, layoutLayerGates, finProdFinEquiv,
      Nat.mul_comm, Nat.add_comm]

theorem sourceWire_realizable (bit : Fin (cellWidth Symbol State)) : (sourceWire bit).Realizable := by
  let computation := sourceWire bit
  let inputs := blockBaseInputs
  let wires := layoutWires Symbol State
  let condition := fun sizes (arguments : computation.Arguments sizes) => decide ((arguments false).val < 1)
  apply Realizable.ofCases condition
  · have tested := (positionWithin_realizable (MvPolynomial.X ()) 1).withArguments
      inputs (MultiTape.oneTape false) (fun _ => rfl)
    exact tested.withSpecification computation.precondition (fun sizes arguments => condition sizes arguments.val)
      (by intros; trivial) (by intros; simp [condition, withArguments, positionWithin])
  · have copied := (initialWire_realizable bit).withPrecondition
      (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
      (by intros; trivial)
    apply copied.withSpecification _ _ (by intros; assumption)
    intro sizes arguments allowed
    have zero : (arguments false).val = 0 := by simpa [condition] using allowed.2
    simp [computation, sourceWire, specification_compute, withPrecondition, zero]
  · let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
      computation.precondition sizes arguments ∧ condition sizes arguments = false
    let last := (wireShift wires (cellBlockSize Symbol State - 1)).onResults inputs allowed
      (fun _ sizes arguments => (blockBase bit).compute sizes ⟨arguments.val, trivial⟩) (by
        intro sizes arguments
        have fits : ((blockBase bit).compute sizes ⟨arguments.val, trivial⟩).val +
            cellBlockSize Symbol State ≤ MvPolynomial.eval sizes (layoutWires Symbol State) :=
          blockBase_result_fits bit sizes arguments.val
        have positive := cellBlockSize_positive (Symbol := Symbol) (State := State)
        change ((blockBase bit).compute sizes ⟨arguments.val, trivial⟩).val +
          (cellBlockSize Symbol State - 1) < MvPolynomial.eval sizes (layoutWires Symbol State)
        omega)
    have lastReady : last.Realizable := by
      apply (wireShift_realizable wires (cellBlockSize Symbol State - 1)).onResults
      intro name
      exact (blockBase_realizable bit).withPrecondition allowed (by intros; trivial)
    let layer := (wirePolynomial (layoutLayerGates Symbol State) wires).onResults inputs allowed
      (fun empty => nomatch empty) (by
        intro sizes arguments
        exact layoutLayer_bounded sizes ((arguments.val false).cast (by simp)))
    have layerReady : layer.Realizable := by
      apply (wirePolynomial_realizable (layoutLayerGates Symbol State) wires).onResults
      intro empty
      exact nomatch empty
    have subtracted := (wireSubtract_realizable wires).onResults inputs allowed
      (fun choice sizes arguments => if choice then layer.compute sizes arguments
        else last.compute sizes arguments) (by
        intro sizes arguments
        have nonzero : ¬ (arguments.val false).val < 1 := by simpa [condition] using arguments.property.2
        have base := blockBase_correct bit sizes arguments.val
        have scaled := Nat.mul_le_mul_right (MvPolynomial.eval sizes (layoutLayerGates Symbol State))
          (show 1 ≤ (arguments.val false).val by omega)
        simp only [Nat.one_mul] at scaled
        change MvPolynomial.eval sizes (layoutLayerGates Symbol State) ≤
          ((blockBase bit).compute sizes ⟨arguments.val, trivial⟩).val + (cellBlockSize Symbol State - 1)
        omega) (by
        intro choice
        cases choice
        · exact lastReady
        · exact layerReady)
    apply subtracted.withSpecification _ _ (by intros; assumption)
    intro sizes arguments accepted
    apply Fin.ext
    have nonzero : (arguments false).val ≠ 0 := by simpa [condition] using accepted.2
    simp [computation, sourceWire, specification_compute, onResults, wireSubtract,
      layer, wirePolynomial, last, wireShift, unaryMap, nonzero]

end Polytime2.Complexity.CookLevin
