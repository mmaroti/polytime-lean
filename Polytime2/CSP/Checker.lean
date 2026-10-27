import Polytime2.CSP.Encoding
import Polytime2.CSP.CheckerMath
import Polytime2.Computation.Specification

/-! # Mathematical assignment checker for finite relational CSP

The input is a dense relational instance and an assignment of actual template
values to its variables. The Boolean answer is true precisely when the
assignment is a homomorphism. The template, including its relation tables, is
fixed before the checker is specialized. No satisfiability or reflexivity
precondition is imposed on instances. Nullary and empty relations are covered
by the same preservation predicate.
-/

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language _root_.Polytime2.Computation


variable (L : Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

/-- The two inputs are the mathematical instance and its proposed assignment. -/
noncomputable def checkerInputs : Bool → EncodedDomain Unit :=
  fun choice => if choice then assignmentDomain Carrier else instanceDomain L

/-- The public checker specifies preservation independently of its realization. -/
noncomputable def assignmentChecker : Computation Unit Bool :=
  decision (checkerInputs L Carrier) (fun _ _ => True)
    (fun sizes arguments => Preserves L Carrier (sizes ()) (arguments false) (arguments true))

/-- Checking one assignment returns true exactly when that assignment is a
homomorphism into the template. -/
theorem assignmentChecker_correct (sizes : Unit → ℕ)
    (arguments : (assignmentChecker L Carrier).Arguments sizes) :
    (assignmentChecker L Carrier).compute sizes ⟨arguments, trivial⟩ = true ↔
      Preserves L Carrier (sizes ()) (arguments false) (arguments true) :=
  decision_correct _ _ _ sizes ⟨arguments, trivial⟩

/-- Assignment witnesses characterize CSP satisfiability, including instances
with no variables or with nullary constraints. -/
theorem assignmentChecker_exists_iff (variableCount : ℕ) (input : Instance L variableCount) :
    Instance.Satisfiable L input Carrier ↔
      ∃ assignment : Fin variableCount → Carrier,
        (assignmentChecker L Carrier).compute (fun _ => variableCount)
          ⟨(fun choice => match choice with | false => input | true => assignment), trivial⟩ = true := by
  rw [satisfiable_iff_exists_preserves]
  apply exists_congr
  intro assignment
  exact (assignmentChecker_correct L Carrier (fun _ => variableCount)
    (fun choice => match choice with | false => input | true => assignment)).symm

end Polytime2.CSP
