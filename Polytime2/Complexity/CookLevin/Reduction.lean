import Polytime2.Complexity.CookLevin.FixedInstanceProgram
import Polytime2.CSP.WordOutput
import Polytime2.CSP.VerifierRealizable

/-! # Cook-Levin reduction to the existing relational three-SAT language

The total translation accepts every external word as the source instance,
constructs the prefix-fixed verifier formula and its dense Boolean structure,
and emits the existing unary-header instance word. The target is the language
already certified to belong to NP, with its original strict decoder.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Turing EncodedDomain Polytime2.Computation

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def rawInstanceProgram (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) : Computation Unit Unit :=
  (fixedInstanceProgram machine entry letters timeBound witnessLength).reinterpretInputs
    (fun _ => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (fun _ _ => True) (by intros; trivial)

private theorem rawInstanceProgram_realizable (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (rawInstanceProgram machine entry letters timeBound witnessLength).Realizable :=
  (fixedInstanceProgram_realizable machine entry letters timeBound witnessLength).reinterpretInputs
    (fun _ => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (by intros; rfl) (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
    (fun _ _ => True) (by intros; trivial)

/-- Total word translation with the target CSP's native unary header. -/
noncomputable def fixedInstanceWord (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (word : Word) : Word :=
  CSP.instanceWord CSP.ThreeSAT.language
    ⟨MvPolynomial.eval (fun _ => word.length) (fixedFormulaWireCount Symbol State timeBound witnessLength),
      (rawInstanceProgram machine entry letters timeBound witnessLength).compute (fun _ => word.length)
        ⟨fun _ index => word[index], trivial⟩⟩

/-- Includes raw-input preparation, formula and table construction, and native
output framing, on every word, including the empty word. -/
theorem fixedInstanceWord_polynomialTime (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    PolynomialTime id id (fixedInstanceWord machine entry letters timeBound witnessLength) := by
  let operation (size : ℕ) (input : Fin size → Letter) :=
    (rawInstanceProgram machine entry letters timeBound witnessLength).compute (fun _ => size)
      ⟨fun _ => input, trivial⟩
  have ready := (rawInstanceProgram_realizable machine entry letters timeBound witnessLength).withSpecification
    (fun _ _ => True) (fun sizes arguments => operation (sizes ()) (arguments.val ()))
    (by intros; trivial) (by
      intro sizes arguments valid
      obtain ⟨size, rfl⟩ : ∃ size, sizes = fun _ : Unit => size :=
        ⟨sizes (), by funext name; cases name; rfl⟩
      rfl)
  exact CSP.instanceWord_polynomialTime CSP.ThreeSAT.language
    (fixedFormulaWireCount Symbol State timeBound witnessLength) operation ready

/-- The strict target decoder accepts the constructed word and recovers
exactly the satisfiability of the constructor's formula. -/
theorem fixedInstanceWord_mem (machine : TM0.Machine Symbol State) (entry : State)
    (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) (word : Word) :
    fixedInstanceWord machine entry letters timeBound witnessLength word ∈
      CSP.language CSP.ThreeSAT.language Bool ↔
    SAT.Formula.Satisfiable (SAT.formulaValue
      ((fixedFormulaProgram machine entry letters timeBound witnessLength).compute (fun _ => word.length)
        ⟨fun _ => arrayParameterEquiv letterDomain () (fun _ => word.length)
          (fun index => word[index]), trivial⟩)) := by
  change (∃ input, CSP.decodeInstanceWord CSP.ThreeSAT.language
    (CSP.instanceWord CSP.ThreeSAT.language _) = some input ∧
      CSP.Instance.Satisfiable CSP.ThreeSAT.language input.2 Bool) ↔ _
  rw [CSP.decodeInstanceWord_instanceWord]
  simp only [Option.some.injEq, exists_eq_left']
  exact fixedInstanceProgram_satisfiable machine entry letters timeBound witnessLength _ _

/-- Every NP language has a total polynomial many-one reduction to the
existing eight-relation Boolean CSP word language. No hardness assumption is
used: the verifier, circuit constructor, and every output stage are certified. -/
theorem np_reduces_threeSAT (source : Language Letter) (membership : InNP source) :
    ManyOneReducible source (CSP.language CSP.ThreeSAT.language Bool) := by
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, witnessLength, _ready, correct⟩ := np_formulas_uniform source membership
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  refine ⟨fixedInstanceWord machine entry letters timeBound witnessLength,
    fixedInstanceWord_polynomialTime machine entry letters timeBound witnessLength, ?_⟩
  intro word
  rw [fixedInstanceWord_mem]
  have result := correct (fun _ => word.length)
    (fun _ => arrayParameterEquiv letterDomain () (fun _ => word.length) (fun index => word[index]))
  have sameLetters : List.ofFn (arrayParameterEquiv letterDomain () (fun _ => word.length)
      (fun index => word[index])) = word := by
    have transported := (List.ofFn_congr (MvPolynomial.eval_X (f := fun _ : Unit => word.length) ()).symm
      (fun index : Fin word.length => word[index])).symm
    have original : List.ofFn (fun index : Fin word.length => word[index]) = word := by simp
    exact transported.trans original
  rw [sameLetters] at result
  exact result

end Polytime2.Complexity.CookLevin

namespace Polytime2.CSP.ThreeSAT

/-- Cook-Levin hardness for the original dense relational three-SAT language. -/
theorem language_npHard : Complexity.NPHard (CSP.language language Bool) :=
  Complexity.CookLevin.np_reduces_threeSAT

/-- Three-SAT is NP-complete with the existing strict instance-word decoder
and actual finite-machine polynomial-time reductions. -/
theorem language_npComplete : Complexity.NPComplete (CSP.language language Bool) :=
  ⟨language_inNP language Bool, language_npHard⟩

end Polytime2.CSP.ThreeSAT
