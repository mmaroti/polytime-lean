import Polytime2.SAT.FixedInputs
import Polytime2.SAT.TseitinProgram

/-! # Certified clauses fixing a circuit's input prefix

Each supplied bit produces a repeated-literal unit clause on its coordinate.
Tabulation and concatenation reuse the canonical clause codec and the existing
array operations; no additional machine or representation is introduced.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation Circuit Complexity
open Polytime2.Computation.Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Emit the unit clauses fixing the first variables to the supplied bits. -/
noncomputable def inputAssertions (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    Computation Parameter Unit :=
  arrayTabulate (fun _ => booleans.arrayOfLength length) (clauseDomain wires) length
    (fun sizes arguments position _ =>
      (⟨position.val, position.isLt.trans_le (bounded sizes)⟩, !(arguments () position)))

theorem inputAssertions_realizable (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    (inputAssertions length wires bounded).Realizable := by
  apply arrayTabulate_realizable
  let context : Unit ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => booleans.arrayOfLength length) (fun _ => arrayPosition length)
  have lookup := (arrayLookupWithIndex_realizable booleans (arrayPosition length)
    (fun _ position => position.val) (arrayPosition_value length) length).onArguments
    context (fun _ _ => True) (fun name => if name then .inl () else .inr ())
    (by intro name; cases name <;> rfl) (by
      intro sizes arguments
      exact (arguments.val (.inr ())).isLt)
  have bit := lookup.withSpecification (fun _ _ => True)
    (fun _ arguments => arguments.val (.inl ()) (arguments.val (.inr ())))
    (by intros; trivial) (by intros; rfl)
  have negation := (booleanOperation_realizable (Parameter := Parameter)
    (fun arguments : Unit → Bool => !(arguments ()))).onResults context (fun _ _ => True)
      (fun _ _ arguments => arguments.val (.inl ()) (arguments.val (.inr ())))
      (by intros; trivial) (by intro singleton; cases singleton; exact bit)
  have wire := (wireOfPosition_realizable length wires bounded).onArguments context
    (fun _ _ => True) (fun _ => .inr ()) (by intros; rfl) (by intros; trivial)
  have literal := wire.prodMk negation
  exact Realizable.recordOutputs context 3 (fun _ => literalDomain wires)
    (fun _ _ => True) _ (fun _ => literal)

theorem inputAssertions_value (length wires : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires)
    (sizes : Parameter → ℕ) (bits : Fin (MvPolynomial.eval sizes length) → Bool) :
    formulaValue ((inputAssertions length wires bounded).compute sizes ⟨(fun _ => bits), trivial⟩) =
      List.ofFn (fun position => fun _ => (position.val, !(bits position))) := rfl

/-- Append exactly the clauses fixing the supplied prefix of a formula. -/
noncomputable def fixInputsProgram (length wires count : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    Computation Parameter Bool :=
  (arrayAppend (clauseDomain wires) count length).onResults
    (fun name => if name then booleans.arrayOfLength length else (clauseDomain wires).arrayOfLength count)
    (fun _ _ => True)
    (fun _ sizes arguments => (arguments.val false,
      (inputAssertions length wires bounded).compute sizes ⟨(fun _ => arguments.val true), trivial⟩))
    (by intros; trivial)

theorem fixInputsProgram_realizable (length wires count : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    (fixInputsProgram length wires count bounded).Realizable := by
  let context : Bool → EncodedDomain Parameter :=
    fun name => if name then booleans.arrayOfLength length else (clauseDomain wires).arrayOfLength count
  have assertions := (inputAssertions_realizable length wires bounded).onArguments context
    (fun _ _ => True) (fun _ => true) (by intros; rfl) (by intros; trivial)
  apply (arrayAppend_realizable (clauseDomain wires) count length).onResults
  intro singleton
  cases singleton
  exact (Realizable.argument context false (fun _ _ => True)).prodMk assertions

/-- The certified constructor produces the ordinary mathematical fixed-input
formula, including the empty prefix and empty original formula. -/
theorem fixInputsProgram_correct (length wires count : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires)
    (sizes : Parameter → ℕ) (arguments : (fixInputsProgram length wires count bounded).Arguments sizes) :
    formulaValue ((fixInputsProgram length wires count bounded).compute sizes ⟨arguments, trivial⟩) =
      fixInputs (List.ofFn (arguments true)) (formulaValue (arguments false)) := by
  simp only [formulaValue, fixInputsProgram, onResults]
  rw [List.ofFn_comp' _ clauseValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  simp [fixInputs, inputAssertions, arrayTabulate]
  rfl

/-- Input preparation, clause construction, and canonical serialized output
are included in the polynomial-time certificate. -/
theorem fixInputsProgram_polynomialTime (length wires count : MvPolynomial Parameter ℕ)
    (bounded : ∀ sizes, MvPolynomial.eval sizes length ≤ MvPolynomial.eval sizes wires) :
    PolynomialTime (fixInputsProgram length wires count bounded).inputWord
      (fixInputsProgram length wires count bounded).outputWord
      (fixInputsProgram length wires count bounded).result :=
  (fixInputsProgram_realizable length wires count bounded).polynomialTime

end Polytime2.SAT
