import Polytime2.SAT.TseitinBlocks
import Polytime2.Arrays.Append
import Polytime2.Computation.Specification
import Polytime2.Complexity.Realizable

/-! # Certified canonical Tseitin conversion

The input is a bounded gate array and its actual output reference. The output
is the mathematical Tseitin formula in the canonical clause-array codec.
Emission is total on this carrier; the satisfiability contract additionally
requires the ordinary acyclicity and output-validity hypotheses.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation Circuit Complexity

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def outputAssertion (wires : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (Computation.mk (fun _ => arrayPosition wires) (record 1 (fun _ => clauseDomain wires)) (fun _ _ => True)
    (fun _ arguments _ _ => (arguments.val (), false))).followedBy
    (recordToArray (clauseDomain wires) 1) rfl (by intros; trivial)

private theorem outputAssertion_realizable (wires : MvPolynomial Parameter ℕ) : (outputAssertion wires).Realizable := by
  let inputs : Unit → EncodedDomain Parameter := fun _ => arrayPosition wires
  have positive := (booleanOperation_realizable (Parameter := Parameter) (fun _ : Empty → Bool => false)).onResults
    inputs (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial) (fun empty => nomatch empty)
  have literal := (Realizable.argument inputs () (fun _ _ => True)).prodMk positive
  have clause := Realizable.recordOutputs inputs 3 (fun _ => literalDomain wires) (fun _ _ => True)
    (fun _ _ arguments => (arguments.val (), false)) (fun _ => literal)
  have wrapped := Realizable.recordOutputs inputs 1 (fun _ => clauseDomain wires) (fun _ _ => True)
    (fun _ _ arguments _ => (arguments.val (), false)) (fun _ => clause)
  exact wrapped.followedBy (recordToArray_realizable (clauseDomain wires) 1) rfl (by intros; trivial)

private theorem outputAssertion_value (wires : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (outputAssertion wires).Arguments sizes // True}) :
    List.ofFn (fun index => clauseValue ((outputAssertion wires).compute sizes arguments index)) =
      [fun _ => ((arguments.val ()).val, false)] := by
  simp [outputAssertion, followedBy, recordToArray, encodingMap, unaryMap, List.ofFn_succ]
  rfl

private noncomputable def tseitinImplementation (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (arrayAppend (clauseDomain (inputs + count)) (count * 3) 1).onResults
    (fun _ => networkDomain inputs count) (fun _ _ => True)
    (fun _ sizes arguments =>
      ((tseitinGateProgram inputs count).compute sizes ⟨(fun _ => (arguments.val ()).1), trivial⟩,
       (outputAssertion (inputs + count)).compute sizes ⟨(fun _ => (arguments.val ()).2), trivial⟩))
    (by intros; trivial)

private theorem tseitinImplementation_realizable (inputs count : MvPolynomial Parameter ℕ) :
    (tseitinImplementation inputs count).Realizable := by
  let context : Unit → EncodedDomain Parameter := fun _ => networkDomain inputs count
  have source := Realizable.argument context () (fun _ _ => True)
  have gates := (tseitinGateProgram_realizable inputs count).onResults context (fun _ _ => True)
    (fun _ _ arguments => (arguments.val ()).1) (by intros; trivial) (by intro singleton; cases singleton; exact source.fst)
  have assertion := (outputAssertion_realizable (inputs + count)).onResults context (fun _ _ => True)
    (fun _ _ arguments => (arguments.val ()).2) (by intros; trivial) (by intro singleton; cases singleton; exact source.snd)
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact gates.prodMk assertion

private theorem tseitinImplementation_correct (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : (tseitinImplementation inputs count).Arguments sizes // True}) :
    formulaValue ((tseitinImplementation inputs count).compute sizes arguments) =
      tseitin (MvPolynomial.eval sizes inputs) (programValue (arguments.val ())) := by
  simp only [formulaValue, tseitinImplementation, onResults]
  rw [List.ofFn_comp' _ clauseValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  erw [tseitinGateProgram_value]
  erw [outputAssertion_value]
  rfl

private theorem tseitin_fits (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : {arguments : ∀ _ : Unit, (networkDomain inputs count).Carrier sizes // True}) :
    ∃ result : ((clauseDomain (inputs + count)).arrayOfLength (count * 3 + 1)).Carrier sizes,
      formulaValue result = tseitin (MvPolynomial.eval sizes inputs) (programValue (arguments.val ())) :=
  ⟨(tseitinImplementation inputs count).compute sizes arguments,
    tseitinImplementation_correct inputs count sizes arguments⟩

/-- Construct exactly the mathematical Tseitin formula, including its output
assertion. Reference bounds and canonical serialization remain internal. -/
noncomputable def tseitinProgram (inputs count : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  specificationBy (fun _ => networkDomain inputs count)
    ((clauseDomain (inputs + count)).arrayOfLength (count * 3 + 1)) (fun _ _ => True)
    (fun _ => formulaValue)
    (fun sizes arguments => tseitin (MvPolynomial.eval sizes inputs) (programValue (arguments.val ())))
    (tseitin_fits inputs count)

theorem tseitinProgram_realizable (inputs count : MvPolynomial Parameter ℕ) : (tseitinProgram inputs count).Realizable := by
  apply (tseitinImplementation_realizable inputs count).specificationBy
    (fun _ => formulaValue)
    (fun sizes arguments => tseitin (MvPolynomial.eval sizes inputs) (programValue (arguments.val ())))
    (tseitin_fits inputs count) (fun _ => formulaValue_injective)
  intro sizes arguments accepted
  exact tseitinImplementation_correct inputs count sizes ⟨arguments, accepted⟩

theorem tseitinProgram_correct (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (tseitinProgram inputs count).Arguments sizes) :
    formulaValue ((tseitinProgram inputs count).compute sizes ⟨arguments, trivial⟩) =
      tseitin (MvPolynomial.eval sizes inputs) (programValue (arguments ())) := by
  simp only [tseitinProgram, specificationBy_correct]

/-- A valid circuit and its certified output formula have exactly the same
satisfiability status, with the mathematical witness conversions above. -/
theorem tseitinProgram_satisfiable (inputs count : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (tseitinProgram inputs count).Arguments sizes)
    (valid : Circuit.Valid (MvPolynomial.eval sizes inputs) (programValue (arguments ()))) :
    Formula.Satisfiable (formulaValue ((tseitinProgram inputs count).compute sizes ⟨arguments, trivial⟩)) ↔
      Circuit.Satisfiable (MvPolynomial.eval sizes inputs) (programValue (arguments ())) := by
  rw [tseitinProgram_correct]
  exact tseitin_correct _ _ valid

/-- Canonical circuit-input preparation, execution, and serialized clause
output are all included in the word-level polynomial-time certificate. -/
theorem tseitinProgram_polynomialTime (inputs count : MvPolynomial Parameter ℕ) :
    PolynomialTime (tseitinProgram inputs count).inputWord (tseitinProgram inputs count).outputWord
      (tseitinProgram inputs count).result :=
  (tseitinProgram_realizable inputs count).polynomialTime

end Polytime2.SAT
