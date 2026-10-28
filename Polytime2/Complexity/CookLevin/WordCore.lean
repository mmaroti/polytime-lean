import Polytime2.Complexity.CookLevin.AcceptanceFlat
import Polytime2.Complexity.CookLevin.WordAliases
import Polytime2.Circuit.GateRename
import Polytime2.Arrays.Capacity

/-! # Acceptance gates at word-constructor sizes

Time is the false size and word length the true size. Renaming the existing
constructor changes its mathematical indexing while retaining canonical bits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Exact number of simulation and acceptance-observer gates. -/
noncomputable def wordCoreGateCount (Symbol State : Type) [Fintype Symbol] [Fintype State] :
    MvPolynomial Bool ℕ :=
  MvPolynomial.rename (fun _ : Unit => false)
    (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State))

/-- All original configuration inputs and acceptance-gate wires. -/
noncomputable def wordCoreWires (Symbol State : Type) [Fintype Symbol] [Fintype State] :
    MvPolynomial Bool ℕ :=
  MvPolynomial.rename (fun _ : Unit => false)
    (disjunctionWires (layoutWires Symbol State) (observationCount State))

/-- Construct the existing acceptance gates in the caller's two-size codec. -/
noncomputable def wordCoreGateProgram (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    Computation Bool Empty :=
  ((((acceptanceGateProgram machine accepting).renameParameters (fun _ => false)).followedBy
    (arrayOfLengthRename
      (gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State)))
      (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State))
      (fun _ : Unit => false)) rfl (by intros; trivial)).followedBy
    (mapArray
      ((gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State))).renameParameters (fun _ => false))
      (gateDomain (wordCoreWires Symbol State)) (wordCoreGateCount Symbol State)
      (fun sizes gate => (gateRename
        (disjunctionWires (layoutWires Symbol State) (observationCount State)) (fun _ : Unit => false)).compute
          sizes ⟨(fun _ => gate), trivial⟩)) rfl (by intros; trivial)).onResults
    Empty.elim (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)

theorem wordCoreGateProgram_realizable (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    (wordCoreGateProgram machine accepting).Realizable := by
  have renamed := ((acceptanceGateProgram_realizable machine accepting).renameParameters (fun _ => false)).followedBy
    (arrayOfLengthRename_realizable
      (gateDomain (disjunctionWires (layoutWires Symbol State) (observationCount State)))
      (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State))
      (fun _ : Unit => false)) rfl (by intros; trivial)
  have converted := renamed.followedBy (mapArray_realizable _ _ _ _
    (gateRename_realizable (disjunctionWires (layoutWires Symbol State) (observationCount State))
      (fun _ : Unit => false))) rfl (by intros; trivial)
  exact converted.onResults Empty.elim (fun _ _ => True) (fun empty => nomatch empty)
    (by intros; trivial) (fun empty => nomatch empty)

/-- The reindexed canonical array is still the complete mathematical
acceptance-circuit gate list at exactly the given time allowance. -/
theorem wordCoreGateProgram_value (machine : TM0.Machine Symbol State) (accepting : Symbol)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (wordCoreGateProgram machine accepting).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordCoreGateProgram machine accepting).compute sizes arguments index)) =
      (acceptanceCircuit machine accepting (sizes false)).1 := by
  simp only [wordCoreGateProgram, onResults, followedBy, mapArray, gateRename_value,
    arrayOfLengthRename, encodingMap, Computation.renameParameters]
  have reindexed := List.ofFn_congr (MvPolynomial.eval_rename (fun _ : Unit => false) sizes
    (MvPolynomial.X () * layoutLayerGates Symbol State + disjunctionGateCount (observationCount State))).symm
    (fun index => gateValue ((acceptanceGateProgram machine accepting).compute (sizes ∘ (fun _ : Unit => false))
      ⟨(fun empty => nomatch empty), trivial⟩ index))
  exact reindexed.symm.trans (acceptanceGateProgram_value machine accepting (sizes ∘ (fun _ : Unit => false)))

theorem wordCoreWires_eq : wordCoreWires Symbol State =
    wordConfigurationWidth Symbol State + wordCoreGateCount Symbol State := by
  simp only [wordCoreWires, wordCoreGateCount, wordConfigurationWidth, wordPositions,
    disjunctionWires, disjunctionGateCount, layoutWires, layoutLayerGates, layoutWidth,
    layoutPositions, map_add, map_mul, map_one, map_ofNat, MvPolynomial.rename_X, MvPolynomial.rename_C]
  ring

end Polytime2.Complexity.CookLevin
