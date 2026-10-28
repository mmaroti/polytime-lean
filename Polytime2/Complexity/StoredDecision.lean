import Polytime2.Complexity.PairValidation
import Polytime2.Complexity.CookLevin.VerifierDecision
import Polytime2.Arrays.FixedArrayCall
import Polytime2.Computation.RetainBoolean

/-! # Word decisions on exact stored fields

A stored field supplies its actual length and letters. The existing
computed-size call runs a certified verifier at that length and discards the
internal count frame from its Boolean result. Padding is never input data.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def arrayDecision (decision : Word → Bool) : Computation Unit Unit :=
  Computation.mk (fun _ : Unit => letterDomain.array ()) booleans (fun _ _ => True)
    (fun _ arguments => decision (List.ofFn (arguments.val ())))

/-- Apply a total word decision to exactly the letters in a stored field. -/
noncomputable def storedDecision (capacity : MvPolynomial Unit ℕ) (decision : Word → Bool) :
    Computation Unit Unit :=
  (callFixedArray (fixed (Fintype.equivFin Letter)) capacity (arrayDecision decision)
    rfl (by intros; trivial)).followedBy
    (retainComputedBoolean (fun _ : Unit => capacity)) rfl (by intros; trivial)

theorem storedDecision_realizable (capacity : MvPolynomial Unit ℕ) (decision : Word → Bool)
    (ready : PolynomialTime id encodeBool decision) : (storedDecision capacity decision).Realizable :=
  ((CookLevin.wordVerifier_realizable decision ready).callFixedArray
    (fixed (Fintype.equivFin Letter)) capacity rfl (by intros; trivial)).followedBy
      (retainComputedBoolean_realizable (fun _ : Unit => capacity)) rfl (by intros; trivial)

/-- The result is independent of host padding and uses precisely the stored
field contents, including an empty field. -/
theorem storedDecision_correct (capacity : MvPolynomial Unit ℕ) (decision : Word → Bool)
    (sizes : Unit → ℕ) (field : (boundedArray letterDomain capacity).Carrier sizes) :
    (storedDecision capacity decision).compute sizes ⟨(fun _ => field), trivial⟩ =
      decision (List.ofFn field.2) := by
  rfl

/-- Check a stored nested pair using the existing total framing validator. -/
noncomputable def storedPairValid (capacity : MvPolynomial Unit ℕ) : Computation Unit Unit :=
  storedDecision capacity (fun word => (decodePair word).isSome)

theorem storedPairValid_realizable (capacity : MvPolynomial Unit ℕ) :
    (storedPairValid capacity).Realizable :=
  storedDecision_realizable capacity _ decodePair_isSome_polynomialTime

end Polytime2.Complexity
