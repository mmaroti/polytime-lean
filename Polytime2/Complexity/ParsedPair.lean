import Polytime2.Complexity.PairParser

/-! # Exact pair fields after a successful framing check

The calling precondition is exactly successful mathematical pair decoding.
Field extraction reuses the existing total parser and guarded optional value
projection. No framing or padding convention is added.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private theorem parsed_isSome (sizes : Unit → ℕ)
    (arguments : pairParser.Arguments sizes)
    (accepted : (decodePair (List.ofFn (arguments ()))).isSome = true) :
    (pairParser.compute sizes ⟨arguments, trivial⟩).isSome = true := by
  have parsed := pairParser_correct sizes (arguments ())
  have same := congrArg Option.isSome parsed
  simpa only [Option.isSome_map] using same.trans accepted

/-- Extract exact fields after successful pair decoding. -/
noncomputable def parsedPair : Computation Unit Unit :=
  (pairParser.withPrecondition (fun _ arguments => (decodePair (List.ofFn (arguments ()))).isSome = true)
    (by intros; trivial)).followedBy (optionalGet pairFields.outputDomain) rfl
    (by intro sizes arguments accepted; exact parsed_isSome sizes arguments accepted)

theorem parsedPair_realizable : parsedPair.Realizable :=
  (pairParser_realizable.withPrecondition
    (fun _ arguments => (decodePair (List.ofFn (arguments ()))).isSome = true) (by intros; trivial)).followedBy
    (optionalGet_realizable pairFields.outputDomain) rfl
    (by intro sizes arguments accepted; exact parsed_isSome sizes arguments accepted)

/-- Every field contains exactly the decoded mathematical word. -/
theorem parsedPair_correct (sizes : Unit → ℕ) (arguments : parsedPair.Arguments sizes)
    (valid : parsedPair.precondition sizes arguments) (input witness : Word)
    (decoded : decodePair (List.ofFn (arguments ())) = some (input, witness)) :
    let fields := parsedPair.compute sizes ⟨arguments, valid⟩
    (List.ofFn fields.1.2, List.ofFn fields.2.2) = (input, witness) := by
  have represented := pairParser_correct sizes (arguments ())
  have eta : (fun _ : Unit => arguments ()) = arguments := by funext name; cases name; rfl
  rw [eta, decoded] at represented
  have produced : pairParser.compute sizes ⟨arguments, trivial⟩ =
      some (parsedPair.compute sizes ⟨arguments, valid⟩) :=
    (Option.some_get (parsed_isSome sizes arguments valid)).symm
  rw [produced] at represented
  exact Option.some.inj represented

end Polytime2.Complexity
