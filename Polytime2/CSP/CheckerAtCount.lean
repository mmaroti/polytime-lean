import Polytime2.CSP.CheckerRealizable
import Polytime2.Computation.ParameterRename

/-! # Assignment checking at a parsed variable count

The true size parameter is the mathematical variable count. Both decoded
inputs retain their canonical named codecs. The false parameter is available
to the word parser as a host capacity and does not enter the checker contract.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

/-- Check an instance and assignment at the parsed variable count, independently
of the parser's host capacity. -/
noncomputable def assignmentCheckerAtCount : Computation Bool Bool :=
  ((assignmentChecker L Carrier).renameParameters (fun _ : Unit => true)).reinterpretOutput
    booleans (fun _ value => value)

theorem assignmentCheckerAtCount_realizable : (assignmentCheckerAtCount L Carrier).Realizable := by
  apply ((assignmentChecker_realizable L Carrier).renameParameters (fun _ : Unit => true)).reinterpretOutput
    booleans (fun _ value => value)
  · intro sizes
    simp [Computation.renameParameters, assignmentChecker, decision, width,
      renameParameters_widthPolynomial, booleans, specification]
  · intro sizes value
    change ArrayEncoding.bits (booleans.encode sizes value) =
      ArrayEncoding.bits (((booleans : EncodedDomain Unit).renameParameters
        (fun _ : Unit => true)).encode sizes value)
    rw [renameParameters_bits]
    simp only [booleans, fixed_encode_bits]

/-- The renamed checker still tests precisely relational preservation. -/
theorem assignmentCheckerAtCount_correct (sizes : Bool → ℕ)
    (arguments : (assignmentCheckerAtCount L Carrier).Arguments sizes) :
    (assignmentCheckerAtCount L Carrier).compute sizes ⟨arguments, trivial⟩ = true ↔
      Preserves L Carrier (sizes true) (arguments false) (arguments true) :=
  assignmentChecker_correct L Carrier (fun _ => sizes true) arguments

end Polytime2.CSP
