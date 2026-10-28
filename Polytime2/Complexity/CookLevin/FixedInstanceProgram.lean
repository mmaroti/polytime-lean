import Polytime2.Complexity.CookLevin.FixedFormulaProgram
import Polytime2.CSP.ThreeSATProgram

/-! # Certified construction of relational verifier instances

Compose the prefix-fixed verifier formula with the dense eight-relation
compiler. The only public size is the original word length. The resulting
structure has precisely the formula's finite variable set and is satisfiable
exactly for an accepting witness. Native instance-word framing remains a
separate output operation.
-/

namespace Polytime2.Complexity.CookLevin

open Turing Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Construct the existing relational three-SAT instance for a fixed verifier. -/
noncomputable def fixedInstanceProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) : Computation Unit Unit :=
  (fixedFormulaProgram machine entry letters timeBound witnessLength).followedBy
    (CSP.ThreeSAT.instanceProgram (fixedFormulaWireCount Symbol State timeBound witnessLength)
      (fixedFormulaClauseCount Symbol State timeBound witnessLength)) rfl (by intros; trivial)

theorem fixedInstanceProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (fixedInstanceProgram machine entry letters timeBound witnessLength).Realizable :=
  (fixedFormulaProgram_realizable machine entry letters timeBound witnessLength).followedBy
    (CSP.ThreeSAT.instanceProgram_realizable (fixedFormulaWireCount Symbol State timeBound witnessLength)
      (fixedFormulaClauseCount Symbol State timeBound witnessLength)) rfl (by intros; trivial)

/-- Every computed dense instance has exactly the satisfiability of the
prefix-fixed formula, before any word serialization. -/
theorem fixedInstanceProgram_satisfiable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (sizes : Unit → ℕ)
    (arguments : (fixedInstanceProgram machine entry letters timeBound witnessLength).Arguments sizes) :
    CSP.Instance.Satisfiable CSP.ThreeSAT.language
      ((fixedInstanceProgram machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩) Bool ↔
    SAT.Formula.Satisfiable (SAT.formulaValue
      ((fixedFormulaProgram machine entry letters timeBound witnessLength).compute sizes ⟨arguments, trivial⟩)) := by
  exact CSP.ThreeSAT.instanceProgram_satisfiable _ _ _ _

/-- Includes all instance construction, internal size preparation, and dense
binary output; native unary-header word framing is not included here. -/
theorem fixedInstanceProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    PolynomialTime (fixedInstanceProgram machine entry letters timeBound witnessLength).inputWord
      (fixedInstanceProgram machine entry letters timeBound witnessLength).outputWord
      (fixedInstanceProgram machine entry letters timeBound witnessLength).result :=
  (fixedInstanceProgram_realizable machine entry letters timeBound witnessLength).polynomialTime

end Polytime2.Complexity.CookLevin
