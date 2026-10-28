import Polytime2.Complexity.CookLevin.WordProgram
import Polytime2.Complexity.CookLevin.CheckedGuardProgram

/-! # Complete canonical gate arrays for checked word circuits -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Wire count before appending the letter-code guard. -/
noncomputable def wordCircuitWires (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  wordPreparedWires + wordCoreGateCount Symbol State

/-- Existing word-circuit output, as a polynomial reference. -/
noncomputable def wordCircuitOutput (Symbol State : Type) [Fintype Symbol] [Fintype State] : MvPolynomial Bool ℕ :=
  wordPreparedWires + wordCoreOutputOffset Symbol State

private theorem wordBits_available (sizes : Bool → ℕ) :
    sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes (wordCircuitWires Symbol State) := by
  simp only [wordCircuitWires, wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
  omega

private theorem wordOutput_bounded (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (wordCircuitOutput Symbol State) < MvPolynomial.eval sizes (wordCircuitWires Symbol State) :=
  wordCircuitOutput_fits sizes

private theorem originalWires_bounded (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (wordCircuitWires Symbol State) ≤
      MvPolynomial.eval sizes (checkedGuardWires (wordCircuitWires Symbol State)) := by
  simp only [checkedGuardWires, map_add, map_mul, map_ofNat]
  omega

private noncomputable def checkedOriginalGates (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (wordGateProgram machine entry letters).followedBy
    (mapArray (gateDomain (wordCircuitWires Symbol State))
      (gateDomain (checkedGuardWires (wordCircuitWires Symbol State))) (2 + wordCoreGateCount Symbol State)
      (fun sizes gate => (gateWiden (wordCircuitWires Symbol State)
        (checkedGuardWires (wordCircuitWires Symbol State)) originalWires_bounded).compute sizes
          ⟨(fun _ => gate), trivial⟩)) rfl (by intros; trivial)

private theorem checkedOriginalGates_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (checkedOriginalGates machine entry letters).Realizable := by
  exact (wordGateProgram_realizable machine entry letters).followedBy
    (mapArray_realizable _ _ _ _ (gateWiden_realizable _ _ originalWires_bounded)) rfl (by intros; trivial)

private theorem checkedOriginalGates_value (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedOriginalGates machine entry letters).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedOriginalGates machine entry letters).compute sizes arguments index)) =
      (wordCircuit machine entry letters (sizes false) (sizes true)).1 := by
  rcases arguments with ⟨arguments, accepted⟩
  have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
  subst arguments
  simp only [checkedOriginalGates, followedBy, mapArray, gateWiden_value]
  exact wordGateProgram_value machine entry letters sizes ⟨(fun empty => nomatch empty), trivial⟩

/-- Emit the original word circuit and every letter-code guard gate in one
canonical array, preserving the mathematical circuit's gate order. -/
noncomputable def checkedWordGateProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (arrayAppend (gateDomain (checkedGuardWires (wordCircuitWires Symbol State)))
    (2 + wordCoreGateCount Symbol State)
    (((wordGuardGateCount + 1) + (wordGuardGateCount + wordGuardGateCount)) + 4)).onResults
    Empty.elim (fun _ _ => True) (fun _ sizes arguments =>
      ((checkedOriginalGates machine entry letters).compute sizes arguments,
       (checkedGuardProgram (wordCircuitWires Symbol State) (wordCircuitOutput Symbol State)
         wordBits_available wordOutput_bounded).compute sizes arguments)) (by intros; trivial)

theorem checkedWordGateProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (checkedWordGateProgram machine entry letters).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (checkedOriginalGates_realizable machine entry letters).prodMk
    (checkedGuardProgram_realizable _ _ wordBits_available wordOutput_bounded)

/-- The guard starts immediately after the mathematical word circuit. -/
theorem wordCircuit_base (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) :
    sizes true * Fintype.card Letter + (wordCircuit machine entry letters (sizes false) (sizes true)).1.length =
      MvPolynomial.eval sizes (wordCircuitWires Symbol State) := by
  have length := congrArg List.length (wordGateProgram_value machine entry letters sizes
    ⟨(fun empty => nomatch empty), trivial⟩)
  simp only [List.length_ofFn] at length
  change MvPolynomial.eval sizes (2 + wordCoreGateCount Symbol State) = _ at length
  rw [← length]
  simp only [wordCircuitWires, wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
  omega

/-- The constructed array is the entire original checked-word circuit. -/
theorem checkedWordGateProgram_value (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedWordGateProgram machine entry letters).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedWordGateProgram machine entry letters).compute sizes arguments index)) =
      (checkedWordCircuit machine entry letters (sizes false) (sizes true)).1 := by
  simp only [checkedWordGateProgram, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  rw [checkedOriginalGates_value, checkedGuardProgram_value]
  simp only [checkedWordCircuit, Circuit.guard, wordCircuit_base, wordCircuit_output]
  rfl

end Polytime2.Complexity.CookLevin
