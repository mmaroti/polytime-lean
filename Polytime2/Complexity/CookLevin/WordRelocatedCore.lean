import Polytime2.Complexity.CookLevin.WordCore
import Polytime2.Circuit.SpliceProgram

/-! # Relocating acceptance gates through the initial-word aliases -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private theorem coreDomain_equal :
    (gateDomain (wordCoreWires Symbol State)).arrayOfLength (wordCoreGateCount Symbol State) =
      (gateDomain (wordConfigurationWidth Symbol State + wordCoreGateCount Symbol State)).arrayOfLength
        (wordCoreGateCount Symbol State) := by rw [wordCoreWires_eq]

private noncomputable def coreAtCompositionBound (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    Computation Bool Empty :=
  (wordCoreGateProgram machine accepting).reinterpretOutput
    ((gateDomain (wordConfigurationWidth Symbol State + wordCoreGateCount Symbol State)).arrayOfLength
      (wordCoreGateCount Symbol State))
    (fun _ gates => (coreDomain_equal (Symbol := Symbol) (State := State)) ▸ gates)

private theorem coreAtCompositionBound_realizable (machine : TM0.Machine Symbol State) (accepting : Symbol) :
    (coreAtCompositionBound machine accepting).Realizable := by
  apply (wordCoreGateProgram_realizable machine accepting).reinterpretOutput
  · intro sizes
    exact congrArg (fun domain : EncodedDomain Bool => domain.width sizes) (coreDomain_equal (Symbol := Symbol) (State := State)).symm
  · intro sizes gates
    have transport (source target : EncodedDomain Bool) (equal : source = target)
        (value : source.Carrier sizes) :
        ArrayEncoding.bits (target.encode sizes (equal ▸ value)) = ArrayEncoding.bits (source.encode sizes value) := by
      cases equal
      rfl
    exact transport _ _ (coreDomain_equal (Symbol := Symbol) (State := State)) gates

private theorem coreAtCompositionBound_value (machine : TM0.Machine Symbol State) (accepting : Symbol)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (coreAtCompositionBound machine accepting).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((coreAtCompositionBound machine accepting).compute sizes arguments index)) =
      (acceptanceCircuit machine accepting (sizes false)).1 := by
  have transport (source target count : MvPolynomial Bool ℕ) (equal : source = target)
      (gates : ((gateDomain source).arrayOfLength count).Carrier sizes) :
      List.ofFn (fun index => gateValue (((congrArg (fun bound => (gateDomain bound).arrayOfLength count) equal) ▸ gates) index)) =
        List.ofFn (fun index => gateValue (gates index)) := by
    cases equal
    rfl
  let gates : ((gateDomain (wordCoreWires Symbol State)).arrayOfLength (wordCoreGateCount Symbol State)).Carrier sizes :=
    (wordCoreGateProgram machine accepting).compute sizes arguments
  change List.ofFn (fun index => gateValue (((coreDomain_equal (Symbol := Symbol) (State := State)) ▸ gates) index)) = _
  rw [transport _ _ _ (wordCoreWires_eq (Symbol := Symbol) (State := State))]
  exact wordCoreGateProgram_value machine accepting sizes arguments

/-- Relocate the acceptance program through all actual word-input aliases.
The two constant gates are supplied by the surrounding word program. -/
noncomputable def wordRelocatedCore (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (spliceProgram (wordConfigurationWidth Symbol State) wordPreparedWires (wordCoreGateCount Symbol State)).onResults
    Empty.elim (fun _ _ => True)
    (fun name sizes arguments => match name with
      | .inl () => (wordAliases entry letters).compute sizes arguments
      | .inr () => (coreAtCompositionBound machine (letters (Sum.inl true))).compute sizes arguments)
    (by intros; trivial)

theorem wordRelocatedCore_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (wordRelocatedCore machine entry letters).Realizable := by
  apply (spliceProgram_realizable (wordConfigurationWidth Symbol State) wordPreparedWires
    (wordCoreGateCount Symbol State)).onResults
  intro name
  cases name with
  | inl singleton => cases singleton; exact wordAliases_realizable entry letters
  | inr singleton => cases singleton; exact coreAtCompositionBound_realizable machine _

/-- The relocated array is the acceptance program renamed through precisely
the certified alias array, with gate order preserved. -/
theorem wordRelocatedCore_value (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordRelocatedCore machine entry letters).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordRelocatedCore machine entry letters).compute sizes arguments index)) =
      (acceptanceCircuit machine (letters (Sum.inl true)) (sizes false)).1.map
        (Gate.rename (spliceNames (MvPolynomial.eval sizes (wordConfigurationWidth Symbol State))
          (MvPolynomial.eval sizes wordPreparedWires)
          (fun index => ((wordAliases entry letters).compute sizes arguments index).val))) := by
  change List.ofFn (fun index => gateValue
    ((spliceProgram (wordConfigurationWidth Symbol State) wordPreparedWires (wordCoreGateCount Symbol State)).compute sizes
      ⟨(fun name => match name with
        | .inl () => (wordAliases entry letters).compute sizes arguments
        | .inr () => (coreAtCompositionBound machine (letters (Sum.inl true))).compute sizes arguments), trivial⟩ index)) = _
  rw [spliceProgram_value, coreAtCompositionBound_value]

private theorem wordAliasNames (entry : State) (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordAliases entry letters).Arguments sizes // True}) :
    spliceNames (MvPolynomial.eval sizes (wordConfigurationWidth Symbol State))
      (MvPolynomial.eval sizes wordPreparedWires)
      (fun index => ((wordAliases entry letters).compute sizes arguments index).val) =
    spliceNames ((2 * (2 * sizes false) + 1) * cellWidth Symbol State)
      (sizes true * Fintype.card Letter + 2)
      (wiringLayer (sizes true * Fintype.card Letter)
        (initialChoices (2 * sizes false) (sizes true) entry letters)).2 := by
  funext wire
  have sourceEqual := wordConfigurationWidth_eval (Symbol := Symbol) (State := State) sizes
  have targetEqual : MvPolynomial.eval sizes wordPreparedWires = sizes true * Fintype.card Letter + 2 := by
    simp only [wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
  unfold spliceNames
  by_cases before : wire < MvPolynomial.eval sizes (wordConfigurationWidth Symbol State)
  · have beforeActual : wire < (2 * (2 * sizes false) + 1) * cellWidth Symbol State := by omega
    simp only [dite_eq_left before, dite_eq_left beforeActual]
    exact wordAliases_correct entry letters sizes arguments ⟨wire, beforeActual⟩
  · have afterActual : ¬ wire < (2 * (2 * sizes false) + 1) * cellWidth Symbol State := by omega
    simp only [dite_eq_right before, dite_eq_right afterActual, sourceEqual, targetEqual]

/-- Prepending the two constant gates gives exactly the mathematical
word-input circuit's complete gate list. -/
theorem wordRelocatedCore_gates (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordRelocatedCore machine entry letters).Arguments sizes // True}) :
    [.inl false, .inl true] ++
      List.ofFn (fun index => gateValue ((wordRelocatedCore machine entry letters).compute sizes arguments index)) =
      (wordCircuit machine entry letters (sizes false) (sizes true)).1 := by
  rw [wordRelocatedCore_value, wordAliasNames]
  rfl

end Polytime2.Complexity.CookLevin
