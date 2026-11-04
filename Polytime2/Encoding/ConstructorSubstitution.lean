import Polytime2.Encoding.SizeSubstitution
import Mathlib.Data.Fin.Basic

/-! # Canonical constructors under polynomial substitution

Products, bounded coordinates, and arrays retain their canonical encodings
when caller polynomials replace size names. These equalities let certified
producers compose with a specialized consumer without local codec adapters.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

universe carrierLevel

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Polynomial substitution preserves product field order and codecs. -/
theorem prod_substitute (left right : EncodedDomain.{0, carrierLevel} NewParameter)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) :
    (left.prod right).substitute substitution =
      (left.substitute substitution).prod (right.substitute substitution) := by
  refine ext_of_encode_bits _ _ rfl ?_ ?_
  · simp only [substitute, ofCodec, SizeSubstitution.polynomial, map_add]
  · intro sizes value
    exact (substitute_prod_encode_bits left right substitution sizes value).symm

/-- Bounded coordinates keep their exact mathematical bound and binary width. -/
theorem boundedIndex_substitute (length : MvPolynomial NewParameter ℕ)
    (substitution : NewParameter → MvPolynomial Parameter ℕ) :
    (boundedIndex length).substitute substitution =
      boundedIndex (SizeSubstitution.polynomial substitution length) := by
  have carriers : ((boundedIndex length).substitute substitution).Carrier =
      (boundedIndex (SizeSubstitution.polynomial substitution length)).Carrier := by
    funext sizes
    exact congrArg Fin (SizeSubstitution.polynomial_eval substitution length sizes).symm
  refine ext_of_encode_bits _ _ carriers rfl ?_
  intro sizes value
  let transported := cast (congrFun carriers sizes) value
  have sameValue : value.val = transported.val := Fin.val_eq_val_of_heq (cast_heq _ value).symm
  simp only [substitute_encode_bits, boundedIndex, boundedIndexOfWidth, BitVec.ofNatLT_eq_ofNat]
  exact congrArg₂ (fun width number => ArrayEncoding.bits (BitVec.ofNat width number))
    (SizeSubstitution.polynomial_eval substitution length sizes).symm sameValue

private theorem cast_fin_function {Carrier : Type carrierLevel} {first second : ℕ}
    (same : first = second) (types : (Fin first → Carrier) = (Fin second → Carrier))
    (values : Fin first → Carrier) :
    cast types values = fun index => values (Fin.cast same.symm index) := by
  cases same
  rfl

/-- Polynomial substitution preserves every array element and its order,
including arrays of length zero. -/
theorem arrayOfLength_substitute (element : EncodedDomain.{0, carrierLevel} NewParameter)
    (length : MvPolynomial NewParameter ℕ) (substitution : NewParameter → MvPolynomial Parameter ℕ) :
    (element.arrayOfLength length).substitute substitution =
      (element.substitute substitution).arrayOfLength (SizeSubstitution.polynomial substitution length) := by
  have carriers : ((element.arrayOfLength length).substitute substitution).Carrier =
      ((element.substitute substitution).arrayOfLength (SizeSubstitution.polynomial substitution length)).Carrier := by
    funext sizes
    change (Fin _ → element.Carrier _) = (Fin _ → element.Carrier _)
    rw [SizeSubstitution.polynomial_eval]
  refine ext_of_encode_bits _ _ carriers ?_ ?_
  · simp only [substitute, ofCodec, arrayOfLength, SizeSubstitution.polynomial, map_mul]
  · intro sizes value
    rw [substitute_encode_bits, arrayOfLength_encode_bits, arrayOfLength_encode_bits]
    rw [cast_fin_function (SizeSubstitution.polynomial_eval substitution length sizes).symm]
    simp only [ArrayEncoding.bits_encode, substitute_encode_bits]
    exact congrArg List.flatten
      (List.ofFn_congr (SizeSubstitution.polynomial_eval substitution length sizes).symm
        (fun index => ArrayEncoding.bits (element.encode (SizeSubstitution.assignment substitution sizes) (value index))))

end Polytime2.EncodedDomain
