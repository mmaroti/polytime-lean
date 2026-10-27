import Polytime2.Complexity.PairFields
import Polytime2.Computation.Optional

/-! # Total parsing of input/witness word pairs

The prefix count is computed before validation. Extraction runs only after the
complete header and payload bound have passed. Failure returns none, with no
invented field values. Successful outputs are exact bounded arrays.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private theorem fieldsFit (sizes : Unit → ℕ) (arguments : pairFields.Arguments sizes)
    (agrees : prefixCountAgrees sizes arguments)
    (accepted : (decodePair (List.ofFn (arguments true))).isSome = true) :
    pairFields.precondition sizes arguments := by
  have bounds := of_decide_eq_true ((Bool.and_eq_true_iff.mp
    ((decodePair_isSome _).symm.trans accepted)).2)
  have length : (List.ofFn (arguments true)).length = sizes () := by simp
  change (arguments false).val = _ at agrees
  rw [← agrees] at bounds
  change 2 * (arguments false).val < sizes ()
  omega

private noncomputable def guardedFields : Computation Unit Bool where
  inputDomains := pairFields.inputDomains
  outputDomain := optional pairFields.outputDomain
  precondition := prefixCountAgrees
  compute sizes arguments :=
    if accepted : (decodePair (List.ofFn (arguments.val true))).isSome = true then
      some (pairFields.compute sizes ⟨arguments.val, fieldsFit sizes arguments.val arguments.property accepted⟩)
    else none

private theorem guardedFields_realizable : guardedFields.Realizable := by
  have guard := pairValid_realizable.onArguments pairFields.inputDomains prefixCountAgrees
    (fun _ => true) (by intros; rfl) (by intros; trivial)
  exact pairFields_realizable.optionalGuard prefixCountAgrees
    (fun _ arguments => (decodePair (List.ofFn (arguments true))).isSome) fieldsFit guard

private theorem guardedFields_correct (sizes : Unit → ℕ) (arguments : pairFields.Arguments sizes)
    (agrees : prefixCountAgrees sizes arguments) :
    (guardedFields.compute sizes ⟨arguments, agrees⟩).map
      (fun result => (List.ofFn result.1.2, List.ofFn result.2.2)) =
        decodePair (List.ofFn (arguments true)) := by
  dsimp only [guardedFields]
  split_ifs with accepted
  · simp only [Option.map_some]
    cases parsed : readPairHeader (List.ofFn (arguments true)) with
    | none =>
      simp only [decodePair, parsed] at accepted
      change false = true at accepted
      cases accepted
    | some pair =>
      rcases pair with ⟨count, payload⟩
      have counted : (arguments false).val = count := agrees.trans (readPairHeader_count parsed)
      exact (pairFields_decodePair sizes arguments (fieldsFit sizes arguments agrees accepted) payload
        (by simpa only [counted] using parsed)).symm
  · simp only [Option.map_none]
    cases decoded : decodePair (List.ofFn (arguments true)) <;> simp_all

/-- Parse an arbitrary word into its exact input and witness arrays, rejecting
malformed headers and truncated input fields. -/
noncomputable def pairParser : Computation Unit Unit :=
  afterPrefix guardedFields.outputDomain guardedFields.compute

theorem pairParser_realizable : pairParser.Realizable :=
  afterPrefix_realizable _ _ guardedFields_realizable

/-- Total parsing agrees with `decodePair` on every word, including all failed
parses. Successful outputs contain only the actual input and witness letters. -/
theorem pairParser_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (pairParser.compute sizes ⟨(fun _ => letters), trivial⟩).map
      (fun result => (List.ofFn result.1.2, List.ofFn result.2.2)) =
        decodePair (List.ofFn letters) :=
  guardedFields_correct sizes
    (fun choice => match choice with
      | false => unaryPrefixLength.compute sizes ⟨(fun _ => letters), trivial⟩
      | true => letters) (unaryPrefixLength_correct sizes letters)

end Polytime2.Complexity
