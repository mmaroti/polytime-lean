import Polytime2.Arithmetic.NaturalPolynomial

/-! # Polynomial array coordinates

The public bound is precisely membership in the requested finite interval.
Arithmetic widths are derived by the realization.
-/

namespace Polytime2.Computation

open EncodedDomain

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
  have ready := polynomialPosition_realizable (Empty.elim : Empty → MvPolynomial Parameter ℕ)
    (MvPolynomial.rename Sum.inl value) wires
  have prepared := ready.onArguments (positionPolynomial value wires).inputDomains
    (positionPolynomial value wires).precondition (fun empty => nomatch empty)
    (by intro empty; cases empty) (by
      intro sizes arguments
      simpa [polynomialPosition, positionPolynomial, MvPolynomial.eval_rename, Function.comp_def] using arguments.property)
  exact prepared.withSpecification (positionPolynomial value wires).precondition (positionPolynomial value wires).compute
    (by intros; assumption)
    (by intros; apply Fin.ext; simp [onResults, polynomialPosition, positionPolynomial, MvPolynomial.eval_rename, Function.comp_def])

end Polytime2.Computation
