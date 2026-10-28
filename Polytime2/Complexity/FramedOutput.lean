import Polytime2.Complexity.WordArrays
import Polytime2.Arithmetic.BitComparison
import Polytime2.Computation.ComputedSizes
import Polytime2.Encoding.Word

/-! # Native unary headers on total word output

Prepare the unary count, separator bit, and canonical payload by existing
composition. A two-state formatter emits count letters up to the separator,
then binary letters. The raw-word export includes formatting and cleanup.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

private def headerFormat (header bit : Bool) : Bool × Letter :=
  if header then (bit, if bit then .inr 1 else .inr 0) else (false, .inl bit)

private theorem headerFormat_payload (bits : List Bool) :
    formatBits headerFormat false bits = bits.map Sum.inl := by
  induction bits with
  | nil => rfl
  | cons bit bits hypothesis => simp [formatBits, headerFormat, hypothesis]

private theorem headerFormat_correct (count : ℕ) (bits : List Bool) :
    formatBits headerFormat true (List.replicate count true ++ false :: bits) =
      List.replicate count (.inr 1) ++ .inr 0 :: bits.map Sum.inl := by
  induction count with
  | zero => simp [formatBits, headerFormat, headerFormat_payload]
  | succ count hypothesis => simp [List.replicate_succ, formatBits, headerFormat, hypothesis]

end Polytime2.Complexity

namespace Polytime2.Computation.Realizable

open EncodedDomain Complexity

/-- Emit a polynomial unary count and canonical payload on every raw input
word, in the native instance-word alphabet. -/
theorem onWordOutputWithHeader (count : MvPolynomial Unit ℕ) (outputDomain : EncodedDomain Unit)
    (operation : (size : ℕ) → (Fin size → Letter) → outputDomain.Carrier (fun _ => size))
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ()) outputDomain
      (fun _ _ => True) (fun sizes arguments => operation (sizes ()) (arguments.val ()))).Realizable) :
    PolynomialTime id id (fun word =>
      List.replicate (MvPolynomial.eval (fun _ => word.length) count) (.inr 1) ++
        .inr 0 :: outputDomain.word (fun _ => word.length)
          (operation word.length (fun index => word[index]))) := by
  let inputs : Unit → EncodedDomain Unit := fun _ => letterDomain.array ()
  have header := (polynomialUnarySize_realizable count).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have separator := (booleanOperation_realizable (Parameter := Unit)
    (fun _ : Empty → Bool => false)).onResults inputs (fun _ _ => True)
    (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have combined := header.prodMk (separator.prodMk ready)
  have raw := onWordFormattedOutput ((boundedUnary count).prod (booleans.prod outputDomain))
    (fun size letters => (Fin.last (MvPolynomial.eval (fun _ => size) count), (false, operation size letters)))
    Complexity.headerFormat true combined
  have encodedBits (sizes : Unit → ℕ) (value : outputDomain.Carrier sizes) :
      ArrayEncoding.bits (((boundedUnary count).prod (booleans.prod outputDomain)).encode sizes
        (Fin.last (MvPolynomial.eval sizes count), (false, value))) =
      List.replicate (MvPolynomial.eval sizes count) true ++
        false :: ArrayEncoding.bits (outputDomain.encode sizes value) := by
    rw [bits_prod_encode, bits_prod_encode]
    simp only [boundedUnary, BoundedUnary.encode_bits, BoundedUnary.bits, Fin.val_last,
      Nat.sub_self, List.replicate_zero, List.append_nil, WordBits.boolean_bits,
      List.singleton_append]
  convert raw using 1
  funext word
  exact ((congrArg (formatBits Complexity.headerFormat true) (encodedBits _ _)).trans
    (Complexity.headerFormat_correct _ _)).symm

end Polytime2.Computation.Realizable
