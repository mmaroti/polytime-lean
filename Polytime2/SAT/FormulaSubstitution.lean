import Polytime2.SAT.TseitinEncoding
import Polytime2.Computation.Substitution

/-! # Reparameterizing canonical clause arrays without changing their bits

Only the finite bounds attached to clause coordinates change. Ordinary
variables, negation bits, clause order, and every canonical bit are preserved.
This connects a specialized verifier constructor to the shared input-fixing
constructor at its derived polynomial wire and clause counts.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

variable {Parameter SourceParameter : Type} [Fintype Parameter] [Fintype SourceParameter]

/-- Move polynomial substitution inside the canonical clause-array codec. -/
noncomputable def formulaSubstitution (wires count : MvPolynomial SourceParameter ℕ)
    (substitution : SourceParameter → MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (((clauseDomain wires).arrayOfLength count).substitute substitution)
    ((clauseDomain (SizeSubstitution.polynomial substitution wires)).arrayOfLength
      (SizeSubstitution.polynomial substitution count))
    (fun sizes clauses index position =>
      let literal := clauses (index.cast (SizeSubstitution.polynomial_eval substitution count sizes)) position
      (literal.1.cast (SizeSubstitution.polynomial_eval substitution wires sizes).symm, literal.2))

theorem formulaSubstitution_realizable (wires count : MvPolynomial SourceParameter ℕ)
    (substitution : SourceParameter → MvPolynomial Parameter ℕ) :
    (formulaSubstitution wires count substitution).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [width, clauseDomain, literalDomain, arrayPosition, boundedIndexOfWidth,
      SizeSubstitution.polynomial_eval]
  · intro sizes clauses
    rw [substitute_encode_bits]
    simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
    rw [List.ofFn_congr (SizeSubstitution.polynomial_eval substitution count sizes).symm]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext index
    simp only [clauseDomain, bits_record_encode]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext position
    simp only [literalDomain, bits_prod_encode]
    simp [arrayPosition, boundedIndexOfWidth, SizeSubstitution.polynomial_eval,
      ArrayEncoding.bits_append, booleans, fixed_encode_bits]
    apply List.ext_getElem
    · simp [ArrayEncoding.bits, SizeSubstitution.polynomial_eval]
    · intro position firstBound secondBound
      simp only [ArrayEncoding.bits, List.getElem_ofFn, BitVec.getLsbD_ofNatLT]

/-- Reparameterization preserves exactly the ordinary mathematical formula. -/
theorem formulaSubstitution_correct (wires count : MvPolynomial SourceParameter ℕ)
    (substitution : SourceParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (formulaSubstitution wires count substitution).Arguments sizes) :
    formulaValue ((formulaSubstitution wires count substitution).compute sizes ⟨arguments, trivial⟩) =
      formulaValue (arguments ()) := by
  change List.ofFn (fun index => clauseValue
    (arguments () (index.cast (SizeSubstitution.polynomial_eval substitution count sizes)))) =
      List.ofFn (fun index => clauseValue (arguments () index))
  exact (List.ofFn_congr (SizeSubstitution.polynomial_eval substitution count sizes).symm
    (fun index => clauseValue (arguments () index))).symm

end Polytime2.SAT
