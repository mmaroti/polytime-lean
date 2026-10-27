import Polytime2.Computation.Substitution
import Polytime2.Encoding.ParameterRename

/-! # Renaming computation size parameters

A named size projection is polynomial substitution by variables. Public
carriers use the direct projected assignment and retain their canonical bits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

private theorem dependentApplyHEq {Index : Type} {Input Output : Index → Sort _}
    (operation : ∀ index, Input index → Output index) {first second : Index}
    (sameIndex : first = second) {firstValue : Input first} {secondValue : Input second}
    (sameValue : HEq firstValue secondValue) :
    HEq (operation first firstValue) (operation second secondValue) := by
  cases sameIndex
  cases sameValue
  rfl

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
      (fun sizes => sizes ∘ names) := by
    funext sizes name
    simp [SizeSubstitution.assignment]
  have polynomialEqual : SizeSubstitution.polynomial (fun name =>
      (MvPolynomial.X (names name) : MvPolynomial NewParameter ℕ)) =
      (fun polynomial => MvPolynomial.rename names polynomial) := by
    funext polynomial
    induction polynomial using MvPolynomial.induction_on with
    | C number => simp [SizeSubstitution.polynomial]
    | add first second firstEqual secondEqual =>
      simpa [SizeSubstitution.polynomial] using congrArg₂ (· + ·) firstEqual secondEqual
    | mul_X polynomial name equal =>
      simpa [SizeSubstitution.polynomial] using congrArg (· * MvPolynomial.X (names name)) equal
  have domainEqual (domain : EncodedDomain Parameter) :
      domain.substitute (fun name => MvPolynomial.X (names name)) = domain.renameParameters names := by
    unfold EncodedDomain.substitute EncodedDomain.renameParameters EncodedDomain.ofCodec
    congr! 8 <;> try simp_all only
    · apply dependentApplyHEq domain.encode
      · simp_all only
      · assumption
    · apply dependentApplyHEq domain.decode
      · simp_all only
      · congr!; simp_all only
  have computationEqual : computation.substitute (fun name => MvPolynomial.X (names name)) =
      computation.renameParameters names := by
    unfold Computation.substitute Computation.renameParameters
    congr! 8 <;> try simp_all only
    all_goals exact domainEqual _
  rw [← computationEqual]
  exact ready.substitute _

end Polytime2.Computation
