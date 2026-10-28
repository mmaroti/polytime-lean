import Polytime2.Complexity.CookLevin.CheckedWordProgram
import Polytime2.SAT.TseitinProgram

/-! # Certified checked-verifier circuits followed by Tseitin conversion

Both constructor stages use the same canonical gate codec. The intermediate
wire-bound identity is mathematical; composition changes no encoded bits.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing Circuit EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

/-- Construct all clauses of a bounded checked verifier circuit. -/
noncomputable def verifierFormulaProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : Computation Bool Empty :=
  (checkedWordProgram machine entry letters).followedBy
    (SAT.tseitinProgram verifierInputBits (checkedWordGateCount Symbol State)) checkedWordCircuitDomain_equal (by intros; trivial)

theorem verifierFormulaProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) : (verifierFormulaProgram machine entry letters).Realizable :=
  (checkedWordProgram_realizable machine entry letters).followedBy
    (SAT.tseitinProgram_realizable verifierInputBits (checkedWordGateCount Symbol State)) checkedWordCircuitDomain_equal (by intros; trivial)

/-- The result is exactly Tseitin applied to the original mathematical checked
word circuit; no intermediate representation changes its gate or wire values. -/
theorem verifierFormulaProgram_correct (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ)
    (arguments : (verifierFormulaProgram machine entry letters).Arguments sizes) :
    SAT.formulaValue ((verifierFormulaProgram machine entry letters).compute sizes ⟨arguments, trivial⟩) =
      SAT.tseitin (sizes true * Fintype.card Letter)
        (checkedWordCircuit machine entry letters (sizes false) (sizes true)) := by
  let program : (checkedWordCircuitDomain Symbol State).Carrier sizes :=
    (checkedWordProgram machine entry letters).compute sizes ⟨arguments, trivial⟩
  let converted : (Circuit.networkDomain verifierInputBits (checkedWordGateCount Symbol State)).Carrier sizes :=
    (checkedWordCircuitDomain_equal (Symbol := Symbol) (State := State)).symm ▸ program
  change SAT.formulaValue ((SAT.tseitinProgram verifierInputBits (checkedWordGateCount Symbol State)).compute sizes
    ⟨(fun _ => converted), trivial⟩) = _
  rw [SAT.tseitinProgram_correct]
  have castValue : programValue converted =
      programValue program := programValue_transport sizes _ _ _ (checkedWord_wireCount (Symbol := Symbol) (State := State)).symm program
  rw [castValue]
  have correct := checkedWordProgram_correct machine entry letters sizes arguments
  change programValue program = _ at correct
  rw [correct]
  simp only [verifierInputBits, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- Satisfiability of the certified output means that some actual word of the
given length is accepted. Noncanonical Boolean letter codes introduce no witnesses. -/
theorem verifierFormulaProgram_satisfiable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (sizes : Bool → ℕ) (verify : Word → Bool)
    (runs : ∀ word : Fin (sizes true) → Letter,
      Internal.Runs machine entry letters (List.ofFn word) [Sum.inl (verify (List.ofFn word))] (sizes false))
    (arguments : (verifierFormulaProgram machine entry letters).Arguments sizes) :
    SAT.Formula.Satisfiable (SAT.formulaValue
      ((verifierFormulaProgram machine entry letters).compute sizes ⟨arguments, trivial⟩)) ↔
      ∃ word : Fin (sizes true) → Letter, verify (List.ofFn word) = true := by
  rw [verifierFormulaProgram_correct, SAT.tseitin_correct _ _ (checkedWordCircuit_valid machine entry letters _ _)]
  constructor
  · rintro ⟨assignment, accepted⟩
    obtain ⟨word, _encoded, answer⟩ := (checkedWordCircuit_correct machine entry letters _ _ verify runs assignment).mp accepted
    exact ⟨word, answer⟩
  · rintro ⟨word, accepted⟩
    refine ⟨encodeWordBits word, ?_⟩
    exact (checkedWordCircuit_correct machine entry letters _ _ verify runs _).mpr ⟨word, rfl, accepted⟩

/-- Includes canonical size preparation, circuit construction, Tseitin
emission, and serialized clause-array extraction in one polynomial bound. -/
theorem verifierFormulaProgram_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) :
    PolynomialTime (verifierFormulaProgram machine entry letters).inputWord
      (verifierFormulaProgram machine entry letters).outputWord (verifierFormulaProgram machine entry letters).result :=
  (verifierFormulaProgram_realizable machine entry letters).polynomialTime

end Polytime2.Complexity.CookLevin
