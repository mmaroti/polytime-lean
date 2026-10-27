import Polytime2.CSP.PairWordCheck
import Polytime2.Complexity.PairParser

/-! # Total polynomial-time verification and CSP membership in NP

The outer parser, prepared-count call, strict instance/witness decoders, and
assignment checker compose on all words. Failed framing or field codes reject.
The word-array bridge exports an actual finite-machine polynomial-time bound.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

private noncomputable def pairConsumer : Computation Unit Unit :=
  optionalElim pairFields.outputDomain booleans (fun _ => false)
    (fun sizes pair => (pairWordChecker L Carrier).compute sizes ⟨(fun _ => pair), trivial⟩)

private theorem pairConsumer_realizable : (pairConsumer L Carrier).Realizable := by
  have rejected := (booleanOperation_realizable (Parameter := Unit) (fun _ : Empty → Bool => false)).onResults
    (Empty.elim : Empty → EncodedDomain Unit) (fun _ _ => True)
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  exact optionalElim_realizable pairFields.outputDomain booleans (fun _ => false)
    (fun sizes pair => (pairWordChecker L Carrier).compute sizes ⟨(fun _ => pair), trivial⟩)
    rejected (pairWordChecker_realizable L Carrier)

private noncomputable def wordArrayVerifier : Computation Unit Unit :=
  pairParser.followedBy (pairConsumer L Carrier) rfl (by intros; trivial)

private theorem wordArrayVerifier_realizable : (wordArrayVerifier L Carrier).Realizable :=
  pairParser_realizable.followedBy (pairConsumer_realizable L Carrier) rfl (by intros; trivial)

private theorem wordArrayVerifier_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (wordArrayVerifier L Carrier).compute sizes ⟨(fun _ => letters), trivial⟩ =
      wordVerifier L Carrier (List.ofFn letters) := by
  let parsed := pairParser.compute sizes ⟨(fun _ => letters), trivial⟩
  have checked : (wordArrayVerifier L Carrier).compute sizes ⟨(fun _ => letters), trivial⟩ =
      parsed.elim false (fun pair => wordVerifier L Carrier
        (encodePair (List.ofFn pair.1.2, List.ofFn pair.2.2))) := by
    change parsed.elim false (fun pair => (pairWordChecker L Carrier).compute sizes
      ⟨(fun _ => pair), trivial⟩) = _
    cases parsed <;> simp [pairWordChecker_correct]
  rw [checked, wordVerifier_pairElim]
  have observed := congrArg
    (fun result : Option (Word × Word) => result.elim false
      (fun pair => wordVerifier L Carrier (encodePair pair))) (pairParser_correct sizes letters)
  simpa only [Option.elim_map, Function.comp_def, parsed] using observed

/-- The mathematical verifier has a total polynomial-time finite-machine
realization on every word, including malformed framing and field encodings. -/
theorem wordVerifier_polynomialTime : PolynomialTime id encodeBool (wordVerifier L Carrier) := by
  apply Computation.Realizable.onWordDecision (wordVerifier L Carrier)
  apply (wordArrayVerifier_realizable L Carrier).withSpecification (fun _ _ => True)
    (fun _ arguments => wordVerifier L Carrier (List.ofFn (arguments.val ()))) (by intros; trivial)
  intro sizes arguments valid
  exact wordArrayVerifier_correct L Carrier sizes (arguments ())

/-- Every fixed finite relational CSP word language belongs to NP. Witnesses
are canonical assignments of linear length; all malformed words reject. No
inhabitance, reflexivity, or polymorphism assumption on the template is needed. -/
theorem language_inNP : InNP (language L Carrier) :=
  ⟨wordVerifier L Carrier, witnessBound Carrier, wordVerifier_polynomialTime L Carrier,
    wordVerifier_malformed_pair L Carrier, wordVerifier_witnesses L Carrier⟩

end Polytime2.CSP
