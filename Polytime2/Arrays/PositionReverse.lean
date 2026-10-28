import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arithmetic.NaturalArithmetic

/-! # Reversing a finite array coordinate

The mathematical operation is Fin.rev. Its implementation subtracts the
successor coordinate from the array length at the codec's derived width.
The empty domain needs no special element or caller-side padding.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def positionSuccessorWord (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (naturalIncrement (length + 1)).reinterpretInputs (fun _ => arrayPosition length)
    (fun _ sizes coordinate => ⟨coordinate.val, by
      simp only [map_add, map_one]
      exact coordinate.isLt.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩)
    (fun _ _ => True) (by intros; trivial)

private theorem positionSuccessorWord_realizable (length : MvPolynomial Parameter ℕ) :
    (positionSuccessorWord length).Realizable :=
  (naturalIncrement_realizable (length + 1)).reinterpretInputs (fun _ => arrayPosition length) _
    (by intros; rfl) (by intros; apply arrayPosition_binary_bits; rfl)
    (fun _ _ => True) (by intros; trivial)

private theorem positionSuccessorWord_value (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (positionSuccessorWord length).Arguments sizes // True}) :
    ((positionSuccessorWord length).compute sizes arguments).val = (arguments.val ()).val + 1 := by
  change ((arguments.val ()).val + 1) % 2 ^ MvPolynomial.eval sizes (length + 1) = _
  apply Nat.mod_eq_of_lt
  simp only [map_add, map_one]
  exact (Nat.succ_le_of_lt (arguments.val ()).isLt).trans_lt
    ((Nat.le_succ _).trans_lt Nat.lt_two_pow_self)

/-- Reverse an ordinary finite array coordinate, preserving the canonical
coordinate codec and its exact polynomial width. -/
noncomputable def arrayPositionReverse (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (arrayPosition length) (arrayPosition length) (fun _ _ => True) (fun _ coordinate => coordinate.val.rev)

theorem arrayPositionReverse_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayPositionReverse length).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => arrayPosition length
  let count := ((polynomialIntegerSize length).followedBy (integerMagnitude (length + 1)) rfl (by intros; trivial)).onResults
    inputs (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)
  have countReady : count.Realizable := by
    apply ((polynomialIntegerSize_realizable length).followedBy (integerMagnitude_realizable (length + 1))
      rfl (by intros; trivial)).onResults
    intro empty
    exact nomatch empty
  have subtracted := (naturalSubtract_realizable (length + 1)).onResults inputs (fun _ _ => True)
    (fun choice sizes arguments => if choice then (positionSuccessorWord length).compute sizes arguments
      else count.compute sizes arguments) (by
      intro sizes arguments
      change ((positionSuccessorWord length).compute sizes arguments).val ≤ MvPolynomial.eval sizes length
      rw [positionSuccessorWord_value]
      exact Nat.succ_le_of_lt (arguments.val ()).isLt) (by
      intro choice
      cases choice
      · exact countReady
      · exact positionSuccessorWord_realizable length)
  exact subtracted.withEncodedOutput (arrayPosition length) (arrayPositionReverse length).compute
    (by intros; rfl) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      apply arrayPosition_binary_bits length sizes
      change MvPolynomial.eval sizes length - ((positionSuccessorWord length).compute sizes arguments).val =
        (arguments.val ()).rev.val
      rw [positionSuccessorWord_value]
      simp only [Fin.rev, Fin.val_mk])

end Polytime2.Computation
