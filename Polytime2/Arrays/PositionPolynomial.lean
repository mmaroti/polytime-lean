import Polytime2.Arrays.PositionArithmetic

/-! # Polynomial array coordinates

The public bound is precisely membership in the requested finite interval.
Arithmetic widths are derived by the realization.
-/

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Read a polynomial mathematical size as an array coordinate. Working word
widths are derived internally; admissibility is precisely the coordinate bound. -/
noncomputable def positionPolynomial (value wires : MvPolynomial Parameter ℕ) : Computation Parameter Empty where
  inputDomains := Empty.elim
  outputDomain := arrayPosition wires
  precondition sizes _ := MvPolynomial.eval sizes value < MvPolynomial.eval sizes wires
  compute sizes arguments := ⟨MvPolynomial.eval sizes value, arguments.property⟩

theorem positionPolynomial_realizable (value wires : MvPolynomial Parameter ℕ) :
    (positionPolynomial value wires).Realizable := by
  have widened := (polynomialIntegerSize_realizable value).followedBy
    (integerWiden_realizable (value + 1) (wires + 1)) rfl (by intros; trivial)
  have allowed := widened.withPrecondition (positionPolynomial value wires).precondition (by intros; trivial)
  have narrowed := allowed.followedBy
    (integerNarrowAtWidths_realizable ((value + 1) + (wires + 1)) (wires + 1)
      (by intro sizes; simp only [map_add]; omega)) rfl (by
        intro sizes arguments allowed
        change (MvPolynomial.eval sizes value : ℤ).natAbs < 2 ^ MvPolynomial.eval sizes (wires + 1)
        simp only [Int.natAbs_natCast, map_add, map_one]
        exact allowed.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le))
  have magnitude := narrowed.followedBy (integerMagnitude_realizable (wires + 1)) rfl (by intros; trivial)
  exact magnitude.withEncodedOutput (arrayPosition wires) (positionPolynomial value wires).compute
    (by intros; rfl) (by
      intro sizes arguments
      apply congrArg CallingConvention.tape
      apply arrayPosition_binary_bits wires sizes
      rfl)

end Polytime2.Computation
