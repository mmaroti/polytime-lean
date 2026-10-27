import Polytime2.CSP.DecodeField
import Polytime2.CSP.DecodeAssignment
import Polytime2.CSP.CheckerAtCount
import Polytime2.CSP.WordVerifier
import Polytime2.Computation.OptionalDecision

/-! # Checking decoded instance and witness fields

The variable count is supplied separately. Each stored word field is decoded
strictly; absence of either result returns false. The certified checker runs
only on the actual relational instance and assignment.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

private noncomputable def optionalChecker : Computation Bool Bool :=
  optionalDecision (assignmentCheckerAtCount L Carrier).inputDomains
    (fun sizes arguments => (assignmentCheckerAtCount L Carrier).compute sizes ⟨arguments, trivial⟩)

private theorem optionalChecker_realizable : (optionalChecker L Carrier).Realizable :=
  optionalDecision_realizable _ _ (assignmentCheckerAtCount_realizable L Carrier)

private noncomputable def wordField : EncodedDomain Bool :=
  boundedArray ((fixed (Fintype.equivFin Complexity.Letter) : EncodedDomain Empty).constant)
    (MvPolynomial.X false)

private noncomputable def decodedFields (sizes : Bool → ℕ)
    (arguments : Bool → (wordField).Carrier sizes) :
    (optionalChecker L Carrier).Arguments sizes :=
  fun choice => match choice with
    | false => (decodeInstanceWordField L).compute sizes ⟨(fun _ => arguments false), trivial⟩
    | true => (decodeAssignmentWitnessField Carrier).compute sizes ⟨(fun _ => arguments true), trivial⟩

/-- Check stored instance-table and witness words at a supplied variable count.
All field decoding failures return false. -/
noncomputable def fieldChecker : Computation Bool Bool :=
  (optionalChecker L Carrier).onResults (fun _ => wordField) (fun _ _ => True)
    (fun choice sizes arguments => decodedFields L Carrier sizes arguments.val choice)
    (by intros; trivial)

theorem fieldChecker_realizable : (fieldChecker L Carrier).Realizable := by
  apply (optionalChecker_realizable L Carrier).onResults (fun _ => wordField) (fun _ _ => True)
    (fun choice sizes arguments => decodedFields L Carrier sizes arguments.val choice) (by intros; trivial)
  intro choice
  cases choice
  · exact (decodeInstanceWordField_realizable L).onArguments (fun _ : Bool => wordField)
      (fun _ _ => True) (fun _ => false) (by intros; rfl) (by intros; trivial)
  · exact (decodeAssignmentWitnessField_realizable Carrier).onArguments (fun _ : Bool => wordField)
      (fun _ _ => True) (fun _ => true) (by intros; rfl) (by intros; trivial)

/-- The composed field check has exactly the mathematical decoder/checker
behavior, with false on every instance or witness decoding failure. -/
theorem fieldChecker_correct (sizes : Bool → ℕ)
    (arguments : (fieldChecker L Carrier).Arguments sizes) :
    (fieldChecker L Carrier).compute sizes ⟨arguments, trivial⟩ =
      tableWordVerifier L Carrier (sizes true)
        (List.ofFn (arguments false).2) (List.ofFn (arguments true).2) := by
  unfold tableWordVerifier
  let first := (instanceDomain L).decodeWord (fun _ => sizes true) (List.ofFn (arguments false).2)
  let second := (assignmentDomain Carrier).decodeWord (fun _ => sizes true) (List.ofFn (arguments true).2)
  change (optionalDecision (assignmentCheckerAtCount L Carrier).inputDomains
    (fun sizes values => (assignmentCheckerAtCount L Carrier).compute sizes ⟨values, trivial⟩)).compute sizes
      ⟨decodedFields L Carrier sizes arguments, trivial⟩ = _
  have decoded : decodedFields L Carrier sizes arguments =
      (fun choice => match choice with | false => first | true => second) := by
    funext choice
    cases choice
    · exact decodeInstanceWordField_correct L sizes (arguments false)
    · exact decodeAssignmentWitnessField_correct Carrier sizes (arguments true)
  rw [decoded]
  clear decoded
  dsimp only [first, second]
  cases (instanceDomain L).decodeWord (fun _ => sizes true) (List.ofFn (arguments false).2) <;>
    cases (assignmentDomain Carrier).decodeWord (fun _ => sizes true) (List.ofFn (arguments true).2) <;>
      simp [optionalDecision, Bool.forall_bool]
  change (assignmentChecker L Carrier).compute (fun _ => sizes true) _ = _
  congr 2
  funext choice
  cases choice <;> rfl

end Polytime2.CSP
