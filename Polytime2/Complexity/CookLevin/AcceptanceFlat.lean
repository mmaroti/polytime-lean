import Polytime2.Complexity.CookLevin.AcceptanceObserver
import Polytime2.Complexity.CookLevin.SimulationFlat
import Polytime2.Circuit.GateWiden
import Polytime2.Computation.Specification
import Polytime2.Complexity.Realizable

/-! # Canonical bounded-machine acceptance gate arrays

Simulation and observer gates share the completed circuit's reference codec.
The existing array append computation combines them in mathematical gate
order. No alternative machine or circuit serialization convention is used.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def simulationAtObserverBound (machine : TM0.Machine Symbol State) : Computation Unit Empty :=
  (simulationFlatProgram machine).followedBy
    (mapArray (gateDomain (layoutWires Symbol State))
      (gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State)))
      (MvPolynomial.X () * layoutLayerGates Symbol State) (fun sizes gate =>
        (gateWiden (layoutWires Symbol State)
          (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires).compute
          sizes ⟨(fun _ => gate), trivial⟩)) rfl (by intros; trivial)

private theorem simulationAtObserverBound_realizable (machine : TM0.Machine Symbol State) :
    (simulationAtObserverBound machine).Realizable := by
  have mapped := mapArray_realizable (gateDomain (layoutWires Symbol State))
    (gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State)))
    (MvPolynomial.X () * layoutLayerGates Symbol State) (fun sizes gate =>
      (gateWiden (layoutWires Symbol State)
        (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires).compute
        sizes ⟨(fun _ => gate), trivial⟩)
    (gateWiden_realizable (layoutWires Symbol State)
      (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires)
  exact (simulationFlatProgram_realizable machine).followedBy mapped rfl (by intros; trivial)

private theorem simulationAtObserverBound_value (machine : TM0.Machine Symbol State) (sizes : Unit → ℕ)
    (arguments : {arguments : (simulationAtObserverBound machine).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((simulationAtObserverBound machine).compute sizes arguments index)) =
      simulationGates machine sizes := by
  cases arguments with
  | mk arguments allowed =>
    have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
    subst arguments
    simp only [simulationAtObserverBound, followedBy, mapArray, gateWiden_value]
    exact simulationFlatProgram_value machine sizes

/-- Construct every acceptance-circuit gate in one canonical bounded array. -/
noncomputable def acceptanceGateProgram (machine : TM0.Machine Symbol State) (accepting : Symbol) : Computation Unit Empty :=
  let inputs : Empty → EncodedDomain Unit := Empty.elim
  let simulation := (simulationAtObserverBound machine).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial)
  let observer := (acceptanceObserverFlatProgram (State := State) accepting).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial)
  (arrayAppend (gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State)))
    (MvPolynomial.X () * layoutLayerGates Symbol State) (disjunctionGateCount (observationCount State))).onResults
      inputs (fun _ _ => True) (fun _ sizes arguments =>
        (simulation.compute sizes arguments, observer.compute sizes arguments)) (by intros; trivial)

theorem acceptanceGateProgram_realizable (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    (acceptanceGateProgram machine accepting).Realizable := by
  let inputs : Empty → EncodedDomain Unit := Empty.elim
  have simulation := (simulationAtObserverBound_realizable machine).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have observer := (acceptanceObserverFlatProgram_realizable (State := State) accepting).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  unfold acceptanceGateProgram
  apply (arrayAppend_realizable _ _ _).onResults
  intro name
  cases name
  exact simulation.prodMk observer

/-- The canonical gate array is the complete mathematical acceptance circuit's
program, including the zero-time case. -/
theorem acceptanceGateProgram_value (machine : TM0.Machine Symbol State) (accepting : Symbol) (sizes : Unit → ℕ) :
    List.ofFn (fun index => gateValue ((acceptanceGateProgram machine accepting).compute sizes
      ⟨(fun empty => nomatch empty), trivial⟩ index)) =
      (acceptanceCircuit machine accepting (sizes ())).1 := by
  simp only [acceptanceGateProgram, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  rw [simulationAtObserverBound_value]
  refine Eq.trans ?_ (acceptanceObserverFlatProgram_gates machine accepting sizes)
  apply congrArg (List.append (simulationGates machine sizes))
  apply congrArg List.ofFn
  funext index
  apply congrArg gateValue
  apply congrArg (fun arguments => (acceptanceObserverFlatProgram (State := State) accepting).compute sizes arguments index)
  apply Subtype.ext
  funext empty
  cases empty

/-- The acceptance observer ends at this exact mathematical wire coordinate. -/
theorem acceptanceCircuit_output (machine : TM0.Machine Symbol State) (accepting : Symbol) (sizes : Unit → ℕ) :
    (acceptanceCircuit machine accepting (sizes ())).2 =
      MvPolynomial.eval sizes (layoutWires Symbol State + 5 * observationCount State) := by
  have length := congrArg List.length (acceptanceGateProgram_value machine accepting sizes)
  simp only [List.length_ofFn] at length
  change MvPolynomial.eval sizes (MvPolynomial.X () * layoutLayerGates Symbol State +
    disjunctionGateCount (observationCount State)) = (acceptanceCircuit machine accepting (sizes ())).1.length at length
  have output := observeLayer_output ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)
    (unroll (localExpressions ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State) (3 * cellWidth Symbol State)
      (cellSources (2 * (2 * sizes ()) + 1) (windowNeighbors (2 * sizes ())))
      (cellTables (2 * (2 * sizes ()) + 1) (windowUpdate machine (2 * sizes ())))) (sizes ()))
    (Expression.anyWire (observedCellWires (acceptingObservations (State := State) (sizes ()) accepting)))
    (by rw [Expression.anyWire_gateCount]; omega)
  change (acceptanceCircuit machine accepting (sizes ())).2 + 1 =
    (2 * (2 * sizes ()) + 1) * cellWidth Symbol State + (acceptanceCircuit machine accepting (sizes ())).1.length at output
  rw [← length] at output
  have total : (2 * (2 * sizes ()) + 1) * cellWidth Symbol State +
      MvPolynomial.eval sizes (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State)) =
      MvPolynomial.eval sizes (layoutWires Symbol State + 5 * observationCount State) + 1 := by
    simp only [layoutWires, layoutWidth, layoutPositions, disjunctionGateCount,
      map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_C, MvPolynomial.eval_X]
    ring
  omega

/-- Canonical gate-array/output-coordinate presentation of the acceptance
circuit. All dimensions are derived from its mathematical time allowance. -/
noncomputable def acceptanceCircuitDomain (Symbol State : Type) [Fintype Symbol] [Fintype State] : EncodedDomain Unit :=
  ((gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State))).arrayOfLength
    (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State))).prod
      (arrayPosition (disjunctionWires (layoutWires Symbol State) (observationCount State)))

/-- Observe a canonically encoded circuit as the ordinary mathematical network. -/
noncomputable def acceptanceProgramNetwork (Symbol State : Type) [Fintype Symbol] [Fintype State]
    (sizes : Unit → ℕ) (program : (acceptanceCircuitDomain Symbol State).Carrier sizes) : Network :=
  programValue program

private theorem output_fits (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes (layoutWires Symbol State + 5 * observationCount State) <
      MvPolynomial.eval sizes (disjunctionWires (layoutWires Symbol State) (observationCount State)) := by
  simp only [disjunctionWires, map_add, map_one]
  omega

private noncomputable def acceptanceImplementation (machine : TM0.Machine Symbol State) (accepting : Symbol) : Computation Unit Empty where
  inputDomains := Empty.elim
  outputDomain := acceptanceCircuitDomain Symbol State
  precondition _ _ := True
  compute sizes arguments := ((acceptanceGateProgram machine accepting).compute sizes arguments,
    ⟨MvPolynomial.eval sizes (layoutWires Symbol State + 5 * observationCount State), output_fits sizes⟩)

private theorem acceptanceImplementation_realizable (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    (acceptanceImplementation machine accepting).Realizable := by
  have output := (positionPolynomial_realizable (layoutWires Symbol State + 5 * observationCount State)
    (disjunctionWires (layoutWires Symbol State) (observationCount State))).onResults
      (Empty.elim : Empty → EncodedDomain Unit) (fun _ _ => True) (fun empty => nomatch empty)
      (by intro sizes arguments; exact output_fits sizes) (fun empty => nomatch empty)
  exact (acceptanceGateProgram_realizable machine accepting).prodMk output

private theorem acceptanceImplementation_correct (machine : TM0.Machine Symbol State) (accepting : Symbol) (sizes : Unit → ℕ)
    (arguments : {arguments : (acceptanceImplementation machine accepting).Arguments sizes // True}) :
    acceptanceProgramNetwork Symbol State sizes ((acceptanceImplementation machine accepting).compute sizes arguments) =
      acceptanceCircuit machine accepting (sizes ()) := by
  cases arguments with
  | mk arguments allowed =>
    have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
    subst arguments
    apply Prod.ext
    · exact acceptanceGateProgram_value machine accepting sizes
    · exact (acceptanceCircuit_output machine accepting sizes).symm

private theorem acceptanceCircuit_fits (machine : TM0.Machine Symbol State) (accepting : Symbol)
    (sizes : Unit → ℕ) (arguments : {arguments : ∀ name : Empty, (Empty.elim name : EncodedDomain.{0, 0} Unit).Carrier sizes // True}) :
    ∃ result : (acceptanceCircuitDomain Symbol State).Carrier sizes,
      acceptanceProgramNetwork Symbol State sizes result = acceptanceCircuit machine accepting (sizes ()) :=
  ⟨(acceptanceImplementation machine accepting).compute sizes arguments,
    acceptanceImplementation_correct machine accepting sizes arguments⟩

/-- Construct the bounded-machine acceptance circuit. The specification is the
ordinary mathematical network, independently of its canonical array codec. -/
noncomputable def acceptanceProgram (machine : TM0.Machine Symbol State) (accepting : Symbol) : Computation Unit Empty :=
  specificationBy Empty.elim (acceptanceCircuitDomain Symbol State) (fun _ _ => True)
    (acceptanceProgramNetwork Symbol State) (fun sizes _ => acceptanceCircuit machine accepting (sizes ()))
    (acceptanceCircuit_fits machine accepting)

theorem acceptanceProgram_realizable (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    (acceptanceProgram machine accepting).Realizable := by
  apply (acceptanceImplementation_realizable machine accepting).specificationBy
    (acceptanceProgramNetwork Symbol State) (fun sizes _ => acceptanceCircuit machine accepting (sizes ()))
    (acceptanceCircuit_fits machine accepting) (fun _ => programValue_injective)
  intro sizes arguments allowed
  exact acceptanceImplementation_correct machine accepting sizes ⟨arguments, allowed⟩

/-- The exported constructor returns exactly the specified mathematical circuit. -/
theorem acceptanceProgram_correct (machine : TM0.Machine Symbol State) (accepting : Symbol) (sizes : Unit → ℕ)
    (arguments : (acceptanceProgram machine accepting).Arguments sizes) :
    acceptanceProgramNetwork Symbol State sizes ((acceptanceProgram machine accepting).compute sizes ⟨arguments, trivial⟩) =
      acceptanceCircuit machine accepting (sizes ()) := by
  simp only [acceptanceProgram, specificationBy_correct]

/-- Standalone word-level execution includes canonical size-input preparation,
TM0 simulation, and extraction of the circuit's encoded output word. -/
theorem acceptanceProgram_polynomialTime (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    PolynomialTime (acceptanceProgram machine accepting).inputWord (acceptanceProgram machine accepting).outputWord
      (acceptanceProgram machine accepting).result :=
  (acceptanceProgram_realizable machine accepting).polynomialTime

end Polytime2.Complexity.CookLevin
