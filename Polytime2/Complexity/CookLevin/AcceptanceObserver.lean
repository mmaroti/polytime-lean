import Polytime2.Complexity.CookLevin.AcceptanceReferences
import Polytime2.Complexity.CookLevin.SimulationCorrect
import Polytime2.Circuit.DisjunctionFlat
import Polytime2.Arrays.FlattenRecords

/-! # Certified acceptance observer construction

The machine's reachable accepting cells give a polynomial-length reference
array. Row-major flattening preserves their order, and coordinate widening
prepares the canonical reference width for the appended disjunction program.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Fintype Symbol] [Fintype State]

/-- Exact number of accepting marked-cell observations. -/
noncomputable def observationCount (State : Type) [Fintype State] : MvPolynomial Unit ℕ :=
  (2 * MvPolynomial.X () + 1) * MvPolynomial.C (Fintype.card State)

/-- Appending the observer preserves the bound on every simulation reference. -/
theorem layoutWires_le_observerWires (sizes : Unit → ℕ) :
    MvPolynomial.eval sizes (layoutWires Symbol State) ≤
      MvPolynomial.eval sizes (disjunctionWires (layoutWires Symbol State) (observationCount State)) := by
  simp only [disjunctionWires, map_add]
  omega

private noncomputable def observerReferences (accepting : Symbol) : Computation Unit Empty :=
  ((acceptanceReferences (State := State) accepting).followedBy
    (arrayFlattenRecords (arrayPosition (layoutWires Symbol State)) (Fintype.card State)
      (2 * MvPolynomial.X () + 1)) rfl (by intros; trivial)).followedBy
    (mapArray (arrayPosition (layoutWires Symbol State))
      (arrayPosition (disjunctionWires (layoutWires Symbol State) (observationCount State)))
      (observationCount State) (fun sizes value =>
        (wireOfPosition (layoutWires Symbol State)
          (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires).compute
          sizes ⟨(fun _ => value), trivial⟩)) rfl (by intros; trivial)

private theorem observerReferences_realizable (accepting : Symbol) :
    (observerReferences (State := State) accepting).Realizable := by
  have flattened := (acceptanceReferences_realizable (State := State) accepting).followedBy
    (arrayFlattenRecords_realizable (arrayPosition (layoutWires Symbol State)) (Fintype.card State)
      (2 * MvPolynomial.X () + 1)) rfl (by intros; trivial)
  have widened := mapArray_realizable (arrayPosition (layoutWires Symbol State))
    (arrayPosition (disjunctionWires (layoutWires Symbol State) (observationCount State)))
    (observationCount State) (fun sizes value =>
      (wireOfPosition (layoutWires Symbol State)
        (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires).compute
        sizes ⟨(fun _ => value), trivial⟩) (wireOfPosition_realizable (layoutWires Symbol State)
      (disjunctionWires (layoutWires Symbol State) (observationCount State)) layoutWires_le_observerWires)
  exact flattened.followedBy widened rfl (by intros; trivial)

private theorem observerReferences_list (accepting : Symbol) (sizes : Unit → ℕ)
    (arguments : {arguments : (observerReferences (State := State) accepting).Arguments sizes // True}) :
    List.ofFn (fun index => ((observerReferences (State := State) accepting).compute sizes arguments index).val) =
      (List.ofFn (fun row : Fin (MvPolynomial.eval sizes (2 * MvPolynomial.X () + 1)) =>
        List.ofFn (fun state : Fin (Fintype.card State) =>
          ((acceptanceReferences (State := State) accepting).compute sizes ⟨arguments.val, trivial⟩ row state).val))).flatten := by
  cases arguments
  simp only [observerReferences, followedBy, mapArray, wireOfPosition_value]
  rw [List.ofFn_comp' _ Fin.val, arrayFlattenRecords_list]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]

private theorem stepInputWire_eq {source target : ℕ} (widthEqual : source = target)
    (blockSize steps : ℕ) (first : Fin source) (second : Fin target) (sameValue : first.val = second.val) :
    stepInputWire source blockSize steps first = stepInputWire target blockSize steps second := by
  cases steps with
  | zero => exact sameValue
  | succ steps => simp only [stepInputWire, sameValue, widthEqual]

private theorem observerReferences_names (accepting : Symbol) (sizes : Unit → ℕ)
    (arguments : {arguments : (observerReferences (State := State) accepting).Arguments sizes // True}) :
    List.ofFn (fun index => ((observerReferences (State := State) accepting).compute sizes arguments index).val) =
      (observedCellWires (acceptingObservations (State := State) (sizes ()) accepting)).map
        (layerNames (stepInputWire ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)
          (cellBlockSize Symbol State) (sizes ()))) := by
  rw [observerReferences_list]
  simp only [observedCellWires, acceptingObservations, List.map_map, List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [List.ofFn_congr (show MvPolynomial.eval sizes (2 * MvPolynomial.X () + 1) = 2 * sizes () + 1 by simp)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext position
  apply congrArg List.ofFn
  funext state
  have names (index : Fin ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)) :
      layerNames (stepInputWire ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)
        (cellBlockSize Symbol State) (sizes ())) index.val =
        stepInputWire ((2 * (2 * sizes ()) + 1) * cellWidth Symbol State)
          (cellBlockSize Symbol State) (sizes ()) index := by
    exact dite_eq_left index.isLt
  simp only [names]
  rw [acceptanceReferences_correct]
  apply stepInputWire_eq
  · simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
    ring
  · rfl

/-- Construct the complete final acceptance observer from the time allowance.
The accepting symbol and machine alphabets are fixed specialization data. -/
noncomputable def acceptanceObserverProgram (accepting : Symbol) : Computation Unit Empty :=
  (observerReferences (State := State) accepting).followedBy
    (disjunctionProgram (layoutWires Symbol State) (observationCount State)) rfl (by intros; trivial)

theorem acceptanceObserverProgram_realizable (accepting : Symbol) :
    (acceptanceObserverProgram (State := State) accepting).Realizable :=
  (observerReferences_realizable (State := State) accepting).followedBy
    (disjunctionProgram_realizable (layoutWires Symbol State) (observationCount State)) rfl (by intros; trivial)

/-- The certified simulation and observer concatenate to exactly the bounded
machine acceptance circuit, including zero time and all boundary cells. -/
theorem acceptanceObserverProgram_gates [Inhabited State] (machine : TM0.Machine Symbol State)
    (accepting : Symbol) (sizes : Unit → ℕ) :
    simulationGates machine sizes ++ disjunctionGateList sizes
      ((acceptanceObserverProgram (State := State) accepting).compute sizes
        ⟨(fun empty => nomatch empty), trivial⟩) =
      (acceptanceCircuit machine accepting (sizes ())).1 := by
  let width := (2 * (2 * sizes ()) + 1) * cellWidth Symbol State
  let expressions := localExpressions width (3 * cellWidth Symbol State)
    (cellSources (2 * (2 * sizes ()) + 1) (windowNeighbors (2 * sizes ())))
    (cellTables (2 * (2 * sizes ()) + 1) (windowUpdate machine (2 * sizes ())))
  have uniform : ∀ index, (expressions index).gateCount = cellBlockSize Symbol State := by
    intro index
    rw [show expressions index = _ from localCellExpression_eq machine (2 * sizes ()) index,
      Expression.rename_gateCount, cellExpression_gateCount]
  have outputs : (unroll expressions (sizes ())).2 = stepInputWire width (cellBlockSize Symbol State) (sizes ()) := by
    funext index
    exact unroll_uniform_output expressions (cellBlockSize Symbol State) uniform cellBlockSize_positive (sizes ()) index
  have baseEqual : MvPolynomial.eval sizes (layoutWires Symbol State) = width + (unroll expressions (sizes ())).1.length := by
    rw [unroll_uniform_length expressions (cellBlockSize Symbol State) uniform]
    simp only [layoutWires, layoutWidth, layoutLayerGates, layoutPositions, map_add, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, map_ofNat, map_one]
    dsimp only [width]
    ring
  rw [simulationGates_eq]
  change (unroll expressions (sizes ())).1 ++ _ =
    (unroll expressions (sizes ())).1 ++
      (((Expression.anyWire (observedCellWires (acceptingObservations (sizes ()) accepting))).rename
        (layerNames (unroll expressions (sizes ())).2)).compile
        (width + (unroll expressions (sizes ())).1.length)).1
  apply congrArg (List.append (unroll expressions (sizes ())).1)
  change disjunctionGateList sizes ((disjunctionProgram (layoutWires Symbol State) (observationCount State)).compute sizes
    ⟨(fun _ => (observerReferences (State := State) accepting).compute sizes
      ⟨(fun empty => nomatch empty), trivial⟩), trivial⟩) = _
  rw [disjunctionProgram_value, observerReferences_names, ← Expression.anyWire_rename, outputs, baseEqual]

/-- Construct the observer directly in the canonical flat gate-array codec. -/
noncomputable def acceptanceObserverFlatProgram (accepting : Symbol) : Computation Unit Empty :=
  (observerReferences (State := State) accepting).followedBy
    (disjunctionFlatProgram (layoutWires Symbol State) (observationCount State)) rfl (by intros; trivial)

theorem acceptanceObserverFlatProgram_realizable (accepting : Symbol) :
    (acceptanceObserverFlatProgram (State := State) accepting).Realizable :=
  (observerReferences_realizable (State := State) accepting).followedBy
    (disjunctionFlatProgram_realizable (layoutWires Symbol State) (observationCount State)) rfl (by intros; trivial)

/-- Flat observer output retains the bounded acceptance circuit's exact gates. -/
theorem acceptanceObserverFlatProgram_gates [Inhabited State] (machine : TM0.Machine Symbol State)
    (accepting : Symbol) (sizes : Unit → ℕ) :
    simulationGates machine sizes ++ List.ofFn (fun index => gateValue
      ((acceptanceObserverFlatProgram (State := State) accepting).compute sizes
        ⟨(fun empty => nomatch empty), trivial⟩ index)) =
      (acceptanceCircuit machine accepting (sizes ())).1 := by
  rw [← acceptanceObserverProgram_gates machine accepting sizes]
  apply congrArg (List.append (simulationGates machine sizes))
  change List.ofFn (fun index => gateValue ((disjunctionFlatProgram (layoutWires Symbol State) (observationCount State)).compute sizes
    ⟨(fun _ => (observerReferences (State := State) accepting).compute sizes
      ⟨(fun empty => nomatch empty), trivial⟩), trivial⟩ index)) = _
  rw [disjunctionFlatProgram_value]
  change _ = disjunctionGateList sizes ((disjunctionProgram (layoutWires Symbol State) (observationCount State)).compute sizes
    ⟨(fun _ => (observerReferences (State := State) accepting).compute sizes
      ⟨(fun empty => nomatch empty), trivial⟩), trivial⟩)
  rw [disjunctionProgram_value]


end Polytime2.Complexity.CookLevin
