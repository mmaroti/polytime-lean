import Polytime2.Complexity.CookLevin.WordRelocatedCore
import Polytime2.Circuit.ConstantGates

/-! # Complete canonical word-input gate arrays -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Emit the initial constants followed by the relocated acceptance program. -/
noncomputable def wordGateProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (arrayAppend (gateDomain (wordPreparedWires + wordCoreGateCount Symbol State)) 2
    (wordCoreGateCount Symbol State)).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes arguments =>
      ((twoConstantGates (wordPreparedWires + wordCoreGateCount Symbol State)).compute sizes arguments,
       (wordRelocatedCore machine entry letters).compute sizes arguments)) (by intros; trivial)

theorem wordGateProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (wordGateProgram machine entry letters).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (twoConstantGates_realizable _).prodMk (wordRelocatedCore_realizable machine entry letters)

/-- The constructor emits every gate of the mathematical word circuit,
including its two initial constants, in the same order. -/
theorem wordGateProgram_value (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordGateProgram machine entry letters).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGateProgram machine entry letters).compute sizes arguments index)) =
      (wordCircuit machine entry letters (sizes false) (sizes true)).1 := by
  simp only [wordGateProgram, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  erw [twoConstantGates_value]
  exact wordRelocatedCore_gates machine entry letters sizes ⟨(fun empty => nomatch empty), trivial⟩

end Polytime2.Complexity.CookLevin
