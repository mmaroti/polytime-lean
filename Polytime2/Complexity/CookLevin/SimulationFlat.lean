import Polytime2.Complexity.CookLevin.SimulationCorrect
import Polytime2.Arrays.FlattenRecords

/-! # Canonical flat simulation gate arrays

Fixed bit/template records and variable time/cell arrays all use row-major
canonical bits. Their flattening produces a single mathematical gate array
without introducing a different serialization convention.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def flattenLayer (Symbol State : Type) [Fintype Symbol] [Fintype State] : Computation Unit Unit :=
  (arrayFlattenRecords (record (cellBlockSize Symbol State) (fun _ => gateDomain (layoutWires Symbol State)))
    (cellWidth Symbol State) layoutPositions).followedBy
    (arrayFlattenRecords (gateDomain (layoutWires Symbol State)) (cellBlockSize Symbol State)
      (layoutWidth Symbol State)) rfl (by intros; trivial)

private theorem flattenLayer_realizable : (flattenLayer Symbol State).Realizable :=
  (arrayFlattenRecords_realizable (record (cellBlockSize Symbol State) (fun _ => gateDomain (layoutWires Symbol State)))
    (cellWidth Symbol State) layoutPositions).followedBy
    (arrayFlattenRecords_realizable (gateDomain (layoutWires Symbol State)) (cellBlockSize Symbol State)
      (layoutWidth Symbol State)) rfl (by intros; trivial)

/-- Construct the simulation's canonical row-major array of bounded gates. -/
noncomputable def simulationFlatProgram (machine : TM0.Machine Symbol State) : Computation Unit Empty :=
  ((simulationProgram machine).followedBy
    (mapArray ((flattenLayer Symbol State).inputDomains ()) (flattenLayer Symbol State).outputDomain
      (MvPolynomial.X ()) (fun sizes layer => (flattenLayer Symbol State).compute sizes ⟨(fun _ => layer), trivial⟩))
    rfl (by intros; trivial)).followedBy
    (arrayFlatten (gateDomain (layoutWires Symbol State)) (MvPolynomial.X ()) (layoutLayerGates Symbol State))
    rfl (by intros; trivial)

theorem simulationFlatProgram_realizable (machine : TM0.Machine Symbol State) :
    (simulationFlatProgram machine).Realizable := by
  have step := (flattenLayer_realizable (Symbol := Symbol) (State := State)).withSpecification (fun _ _ => True)
    (fun sizes arguments => (flattenLayer Symbol State).compute sizes ⟨(fun _ => arguments.val ()), trivial⟩)
    (by intros; trivial) (by intros; rfl)
  have mapped := mapArray_realizable ((flattenLayer Symbol State).inputDomains ()) (flattenLayer Symbol State).outputDomain
    (MvPolynomial.X ()) (fun sizes layer => (flattenLayer Symbol State).compute sizes ⟨(fun _ => layer), trivial⟩) step
  exact ((simulationProgram_realizable machine).followedBy mapped rfl (by intros; trivial)).followedBy
    (arrayFlatten_realizable (gateDomain (layoutWires Symbol State)) (MvPolynomial.X ()) (layoutLayerGates Symbol State))
    rfl (by intros; trivial)

private theorem flattenLayer_list (sizes : Unit → ℕ)
    (arguments : {arguments : (flattenLayer Symbol State).Arguments sizes // True}) :
    List.ofFn ((flattenLayer Symbol State).compute sizes arguments) =
      (List.ofFn (fun cell => (List.ofFn (fun bit => List.ofFn (arguments.val () cell bit))).flatten)).flatten := by
  simp only [flattenLayer, followedBy]
  rw [arrayFlattenRecords_list, List.ofFn_comp' _ List.ofFn, arrayFlattenRecords_list]
  simp only [List.map_flatten, List.map_ofFn, List.flatten_flatten, Function.comp_def]

/-- Flat canonical output retains exactly the mathematical simulation gates. -/
theorem simulationFlatProgram_value (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ) :
    List.ofFn (fun index => gateValue ((simulationFlatProgram machine).compute sizes
      ⟨(fun empty => nomatch empty), trivial⟩ index)) = simulationGates machine sizes := by
  simp only [simulationFlatProgram, followedBy]
  rw [List.ofFn_comp' _ gateValue, arrayFlatten_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def, mapArray]
  unfold simulationGates
  rw [List.ofFn_congr (show MvPolynomial.eval sizes (MvPolynomial.X ()) = sizes () by simp)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext time
  rw [List.ofFn_comp' _ gateValue, flattenLayer_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [List.ofFn_congr (show MvPolynomial.eval sizes layoutPositions = 2 * (2 * sizes ()) + 1 by
    simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
    omega)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext cell
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext bit
  apply congrArg List.ofFn
  funext slot
  rfl

end Polytime2.Complexity.CookLevin
