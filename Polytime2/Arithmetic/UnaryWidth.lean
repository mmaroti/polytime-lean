import Polytime2.Computation.ResizeBits
import Polytime2.Computation.Equality
import Polytime2.Computation.ComputedSizes
import Polytime2.Computation.RecordArguments

/-! # Comparing stored unary counts with polynomial sizes

Counts keep their ordinary finite-natural carriers. Widening appends canonical
zero padding, and comparison uses the existing encoded equality rule at a
shared derived capacity. No binary counter conversion is required.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Rebase a unary count into a larger capacity without changing its value.
The capacity comparison is mathematical; the stored count needs no extra bound. -/
noncomputable def boundedUnaryResize (source target : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit :=
  unaryMap (boundedUnary source) (boundedUnary target)
    (fun sizes _ => MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target)
    (fun sizes value => ⟨value.val.val, by have bounded := value.val.isLt; omega⟩)

theorem boundedUnaryResize_realizable (source target : MvPolynomial Parameter ℕ) :
    (boundedUnaryResize source target).Realizable := by
  have copied := (encode_realizable (boundedUnary source)).followedBy
    (resizeBits_realizable source target) rfl (by intros; trivial)
  have selected := copied.withPrecondition (boundedUnaryResize source target).precondition
    (by intros; trivial)
  apply selected.withEncodedOutput (boundedUnary target) (boundedUnaryResize source target).compute
    (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  change ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes target) _) =
    ArrayEncoding.bits ((BoundedUnary.encode (MvPolynomial.eval sizes source) (arguments.val ())).setWidth
      (MvPolynomial.eval sizes target))
  rw [bits_setWidth _ arguments.property, BoundedUnary.encode_bits, BoundedUnary.encode_bits]
  change BoundedUnary.bits (MvPolynomial.eval sizes target) (arguments.val ()).val = _
  simp only [BoundedUnary.bits]
  have bounded := (arguments.val ()).isLt
  have padding : MvPolynomial.eval sizes target - (arguments.val ()).val =
      (MvPolynomial.eval sizes source - (arguments.val ()).val) +
        (MvPolynomial.eval sizes target - MvPolynomial.eval sizes source) := by
    have fits := arguments.property
    change MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target at fits
    omega
  rw [padding, List.replicate_add, List.append_assoc]

/-- Enlarge a unary count's capacity without changing its mathematical value. -/
noncomputable def boundedUnaryWidenTo (capacity extra target : MvPolynomial Parameter ℕ)
    (sameCapacity : target = capacity + extra) : Computation Parameter Unit :=
  encodingMap (boundedUnary capacity) (boundedUnary target) (fun sizes count =>
    ⟨count.val, by
      rw [sameCapacity, map_add]
      have bounded := count.isLt
      omega⟩)

theorem boundedUnaryWidenTo_realizable (capacity extra target : MvPolynomial Parameter ℕ)
    (sameCapacity : target = capacity + extra) :
    (boundedUnaryWidenTo capacity extra target sameCapacity).Realizable := by
  have ready := (boundedUnaryResize_realizable capacity target).withPrecondition (fun _ _ => True) (by
    intro sizes arguments _
    change MvPolynomial.eval sizes capacity ≤ MvPolynomial.eval sizes target
    rw [sameCapacity, map_add]
    omega)
  exact ready.withSpecification (fun _ _ => True) (boundedUnaryWidenTo capacity extra target sameCapacity).compute
    (by intros; trivial) (by intros; rfl)

/-- Compare an actual stored count with a mathematical polynomial length. -/
noncomputable def boundedUnaryEqualsPolynomial (capacity requested : MvPolynomial Parameter ℕ) :
    Computation Parameter Unit where
  inputDomains _ := boundedUnary capacity
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := decide ((arguments.val ()).val = MvPolynomial.eval sizes requested)

theorem boundedUnaryEqualsPolynomial_realizable (capacity requested : MvPolynomial Parameter ℕ) :
    (boundedUnaryEqualsPolynomial capacity requested).Realizable := by
  let computation := boundedUnaryEqualsPolynomial capacity requested
  let common := capacity + requested
  let actual := boundedUnaryWidenTo capacity requested common rfl
  have actualReady : actual.Realizable := boundedUnaryWidenTo_realizable capacity requested common rfl
  let wanted := (polynomialUnarySize requested).followedBy
    (boundedUnaryWidenTo requested capacity common (by dsimp [common]; ring)) rfl (by intros; trivial)
  have wantedReady : wanted.Realizable := (polynomialUnarySize_realizable requested).followedBy
    (boundedUnaryWidenTo_realizable requested capacity common (by dsimp [common]; ring)) rfl (by intros; trivial)
  have wantedOnInputs := wantedReady.onResults computation.inputDomains computation.precondition
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  have compared := (elementsEqual_realizable (boundedUnary common)).onResults
    computation.inputDomains computation.precondition
    (fun choice sizes arguments => match choice with
    | false => actual.compute sizes arguments
    | true => wanted.compute sizes ⟨(fun empty => empty.elim), trivial⟩)
    (by intros; trivial) (by intro choice; cases choice; exact actualReady; exact wantedOnInputs)
  apply compared.withSpecification computation.precondition computation.compute (by intros; trivial)
  intro sizes arguments valid
  apply Bool.eq_iff_iff.mpr
  simp only [onResults, elementsEqual, computation, boundedUnaryEqualsPolynomial,
    actual, wanted, boundedUnaryWidenTo, followedBy, polynomialUnarySize, encodingMap, unaryMap,
    decide_eq_true_eq, Fin.val_last]
  exact Fin.ext_iff

end Polytime2.Computation
