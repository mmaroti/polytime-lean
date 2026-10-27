import Polytime2.Computation.Substitution
import Polytime2.Encoding.ParameterRename

/-! # Renaming computation size parameters

A named size projection is polynomial substitution by variables. Public
carriers use the direct projected assignment and retain their canonical bits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

variable {Parameter NewParameter InputName : Type}
variable [Fintype Parameter] [Fintype NewParameter] [Fintype InputName]

/-- Execute a computation at selected caller size parameters. -/
noncomputable def renameParameters (computation : Computation Parameter InputName)
    (names : Parameter → NewParameter) : Computation NewParameter InputName where
  inputDomains name := (computation.inputDomains name).renameParameters names
  outputDomain := computation.outputDomain.renameParameters names
  precondition sizes := computation.precondition (sizes ∘ names)
  compute sizes := computation.compute (sizes ∘ names)

theorem Realizable.renameParameters {computation : Computation Parameter InputName}
    (ready : computation.Realizable) (names : Parameter → NewParameter) :
    (computation.renameParameters names).Realizable := by
  have assignmentEqual : SizeSubstitution.assignment (fun name =>
      (MvPolynomial.X (names name) : MvPolynomial NewParameter ℕ)) =
      (fun sizes => sizes ∘ names) := funext (SizeSubstitution.assignment_X names)
  have computationEqual : computation.substitute (fun name => MvPolynomial.X (names name)) =
      computation.renameParameters names := by
    unfold Computation.substitute Computation.renameParameters
    congr! 8 <;> simp_all only [EncodedDomain.substitute_X]
  rw [← computationEqual]
  exact ready.substitute _

end Polytime2.Computation
