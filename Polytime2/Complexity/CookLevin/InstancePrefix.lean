import Polytime2.Complexity.WordArrays
import Polytime2.Complexity.CookLevin.WordAssignment
import Polytime2.Complexity.Languages
import Polytime2.Arrays.Append
import Polytime2.Arrays.Tabulate
import Polytime2.Primitives.ConstantOperations

/-! # Certified instance prefixes for the verifier reduction

An input word becomes its ordinary pair header followed by its letters.
The existential witness is appended later. Exact array concatenation uses the
existing letter codec, including the empty input's single separator.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open EncodedDomain Polytime2.Computation

private noncomputable def repeatedLetters (length : MvPolynomial Unit ℕ) (letter : Letter) : Computation Unit Empty :=
  arrayTabulate Empty.elim letterDomain length (fun _ _ _ => letter)

private theorem repeatedLetters_realizable (length : MvPolynomial Unit ℕ) (letter : Letter) :
    (repeatedLetters length letter).Realizable := by
  have value := (constant_realizable (fixed (Fintype.equivFin Letter)) (fun _ => letter)).withConstantSizes (Parameter := Unit)
  apply arrayTabulate_realizable
  exact value.onResults _ (fun _ _ => True) (fun empty => nomatch empty)
    (by intros; trivial) (fun empty => nomatch empty)

private noncomputable def pairHeader : Computation Unit Empty :=
  (arrayAppend letterDomain (MvPolynomial.X ()) 1).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes _ => ((repeatedLetters (MvPolynomial.X ()) (.inr 1)).compute sizes ⟨(fun empty => nomatch empty), trivial⟩,
      (repeatedLetters 1 (.inr 0)).compute sizes ⟨(fun empty => nomatch empty), trivial⟩)) (by intros; trivial)

private theorem pairHeader_realizable : pairHeader.Realizable := by
  have counts := repeatedLetters_realizable (MvPolynomial.X ()) (.inr 1)
  have separator := repeatedLetters_realizable 1 (.inr 0)
  apply (arrayAppend_realizable letterDomain (MvPolynomial.X ()) 1).onResults
  intro singleton
  cases singleton
  exact counts.prodMk separator

private theorem pairHeader_correct (sizes : Unit → ℕ) (arguments : pairHeader.Arguments sizes) :
    List.ofFn (pairHeader.compute sizes ⟨arguments, trivial⟩) =
      List.replicate (sizes ()) (.inr 1) ++ [.inr 0] := by
  simp only [pairHeader, onResults]
  rw [arrayAppend_list]
  simp [repeatedLetters, arrayTabulate, List.ofFn_const]

/-- The exact number of letters before the witness in the existing pair frame. -/
noncomputable def instancePrefixLength : MvPolynomial Unit ℕ := (MvPolynomial.X () + 1) + MvPolynomial.X ()

/-- Construct the complete framed instance prefix, leaving the witness absent. -/
noncomputable def instancePrefix : Computation Unit Unit :=
  (arrayAppend letterDomain (MvPolynomial.X () + 1) (MvPolynomial.X ())).onResults
    (fun _ => letterDomain.arrayOfLength (MvPolynomial.X ())) (fun _ _ => True)
    (fun _ sizes arguments => (pairHeader.compute sizes ⟨(fun empty => nomatch empty), trivial⟩, arguments.val ()))
    (by intros; trivial)

theorem instancePrefix_realizable : instancePrefix.Realizable := by
  let context : Unit → EncodedDomain Unit := fun _ => letterDomain.arrayOfLength (MvPolynomial.X ())
  have header := pairHeader_realizable.onResults context (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  apply (arrayAppend_realizable letterDomain (MvPolynomial.X () + 1) (MvPolynomial.X ())).onResults
  intro singleton
  cases singleton
  exact header.prodMk (Realizable.argument context () (fun _ _ => True))

/-- No witness, padding, or implementation data is added to the fixed prefix. -/
theorem instancePrefix_correct (sizes : Unit → ℕ) (arguments : instancePrefix.Arguments sizes) :
    List.ofFn (instancePrefix.compute sizes ⟨arguments, trivial⟩) = encodePair (List.ofFn (arguments ()), []) := by
  simp only [instancePrefix, onResults]
  rw [arrayAppend_list, pairHeader_correct]
  simp only [encodePair, List.length_ofFn, MvPolynomial.eval_X, List.append_nil]

/-- Prepare the exact Boolean prefix that will be fixed by unit clauses. -/
noncomputable def instancePrefixBits : Computation Unit Unit :=
  instancePrefix.followedBy (wordAssignment instancePrefixLength) rfl (by intros; trivial)

theorem instancePrefixBits_realizable : instancePrefixBits.Realizable :=
  instancePrefix_realizable.followedBy (wordAssignment_realizable instancePrefixLength) rfl (by intros; trivial)

/-- The constructed bits are precisely the one-hot blocks of the pair prefix. -/
theorem instancePrefixBits_correct (sizes : Unit → ℕ) (arguments : instancePrefixBits.Arguments sizes) :
    List.ofFn (instancePrefixBits.compute sizes ⟨arguments, trivial⟩) =
      List.ofFn (encodeWordBits (encodePair (List.ofFn (arguments ()), [])).get) := by
  change List.ofFn ((wordAssignment instancePrefixLength).compute sizes ⟨_, trivial⟩) = _
  rw [wordAssignment_list, instancePrefix_correct]

end Polytime2.Complexity.CookLevin
