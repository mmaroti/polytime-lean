import Polytime2.Complexity.PairParser

/-! # Total parsing of a unary count and its remaining payload

This parser is suitable for instance fields: unlike word-pair framing, it does
not require another count-sized field after the separator. Prefix preparation,
guarded execution, and exact slicing are shared with the pair parser.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private theorem headerFits (sizes : Unit → ℕ) (arguments : headerFields.Arguments sizes)
    (agrees : prefixCountAgrees sizes arguments)
    (accepted : (readPairHeader (List.ofFn (arguments true))).isSome = true) :
    headerFields.precondition sizes arguments := by
  cases parsed : readPairHeader (List.ofFn (arguments true)) with
  | none => simp only [parsed, Option.isSome_none, Bool.false_eq_true] at accepted
  | some pair =>
    rcases pair with ⟨count, payload⟩
    have counted : (arguments false).val = count := agrees.trans (readPairHeader_count parsed)
    have lengths := congrArg List.length (readPairHeader_canonical parsed)
    have size : (List.ofFn (arguments true)).length = sizes () := by simp
    simp only [List.length_append, List.length_replicate, List.length_cons] at lengths
    change (arguments false).val < sizes ()
    omega

private noncomputable def guardedHeader : Computation Unit Bool :=
  headerFields.optionalGuard prefixCountAgrees
    (fun _ arguments => (readPairHeader (List.ofFn (arguments true))).isSome) headerFits

private theorem guardedHeader_realizable : guardedHeader.Realizable := by
  have checked := unaryHeaderValid_realizable.onArguments headerFields.inputDomains prefixCountAgrees
    (fun _ => true) (by intros; rfl) (by intros; trivial)
  have guard := checked.withSpecification prefixCountAgrees
    (fun _ arguments => (readPairHeader (List.ofFn (arguments.val true))).isSome)
    (by intros; assumption) (by
      intro sizes arguments valid
      exact unaryHeaderValid_correct sizes (arguments true))
  exact headerFields_realizable.optionalGuard prefixCountAgrees
    (fun _ arguments => (readPairHeader (List.ofFn (arguments true))).isSome) headerFits guard

private theorem guardedHeader_correct (sizes : Unit → ℕ) (arguments : headerFields.Arguments sizes)
    (agrees : prefixCountAgrees sizes arguments) :
    (guardedHeader.compute sizes ⟨arguments, agrees⟩).map
      (fun result => (result.1.val, List.ofFn result.2.2)) =
        readPairHeader (List.ofFn (arguments true)) := by
  dsimp only [guardedHeader, optionalGuard]
  split_ifs with accepted
  · simp only [Option.map_some]
    cases parsed : readPairHeader (List.ofFn (arguments true)) with
    | none => simp only [parsed, Option.isSome_none, Bool.false_eq_true] at accepted
    | some pair =>
      rcases pair with ⟨count, payload⟩
      have counted : (arguments false).val = count := agrees.trans (readPairHeader_count parsed)
      exact (headerFields_readPairHeader sizes arguments (headerFits sizes arguments agrees accepted) payload
        (by simpa only [counted] using parsed)).symm.trans parsed
  · simp only [Option.map_none]
    cases parsed : readPairHeader (List.ofFn (arguments true)) <;> simp_all

/-- Parse every word into its unary count and exact suffix, or return none for
an invalid header. Empty payloads are accepted, including a lone separator. -/
noncomputable def headerParser : Computation Unit Unit :=
  afterPrefix guardedHeader.outputDomain guardedHeader.compute

theorem headerParser_realizable : headerParser.Realizable :=
  afterPrefix_realizable _ _ guardedHeader_realizable

/-- Successful and failed parses agree with the mathematical header decoder. -/
theorem headerParser_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (headerParser.compute sizes ⟨(fun _ => letters), trivial⟩).map
      (fun result => (result.1.val, List.ofFn result.2.2)) = readPairHeader (List.ofFn letters) :=
  guardedHeader_correct sizes
    (fun choice => match choice with
      | false => unaryPrefixLength.compute sizes ⟨(fun _ => letters), trivial⟩
      | true => letters) (unaryPrefixLength_correct sizes letters)

end Polytime2.Complexity
