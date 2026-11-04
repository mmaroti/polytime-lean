import Polytime2.CSP.GadgetReduction
import Polytime2.CSP.VerifierRealizable
import Polytime2.Complexity.CookLevin.FixedFormulaProgram

/-! # NP-completeness for finite rigid cores without Taylor polymorphisms

The mathematical algebraic theorem supplies fixed Boolean pp gadgets. Compose
the certified Cook-Levin constructor with their certified compiler to obtain a
total polynomial many-one reduction from every NP language. Membership in NP
uses the existing verifier with strict rejection of malformed instance words.

The hypothesis is rigidity, not reflexivity. The template, its signature, and
all gadget choices are fixed independently of each reduction's input word.

Mathematical provenance: Brady, *Notes on CSPs and Polymorphisms*, sections
1.3 and 1.5, especially Corollary 1.5.7; see the author's
[TeX source](https://github.com/notzeb/all/blob/master/csp.tex).
-/

namespace Polytime2.CSP

open Complexity Complexity.CookLevin EncodedDomain Polytime2.Computation GadgetExpansion

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]

section Verifier

variable {Symbol State : Type} [Inhabited Symbol] [Inhabited State]
variable [Fintype Symbol] [Fintype State]

private noncomputable def wordFormula (machine : Turing.TM0.Machine Symbol State)
    (entry : State) (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :=
  (fixedFormulaProgram machine entry letters timeBound witnessLength).reinterpretInputs
    (fun _ => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (fun _ _ => True) (by intros; trivial)

private theorem wordFormula_realizable (machine : Turing.TM0.Machine Symbol State)
    (entry : State) (letters : Letter ↪ Symbol) (timeBound witnessLength : Polynomial ℕ) :
    (wordFormula machine entry letters timeBound witnessLength).Realizable :=
  (fixedFormulaProgram_realizable machine entry letters timeBound witnessLength).reinterpretInputs
    (fun _ => letterDomain.array ()) (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (by intros; rfl) (fun _ sizes value => array_X_encode_bits letterDomain () sizes value)
    (fun _ _ => True) (by intros; trivial)

end Verifier

/-- Every NP language reduces, on all raw words, to the fixed-template CSP of
any nonempty finite rigid core without a Taylor polymorphism. No complexity
assumption or external hardness axiom is used. -/
theorem language_npHard_of_noTaylorPolymorphism
    (rigid : IsRigidCore L Carrier) (noTaylor : ¬ HasTaylorPolymorphism L Carrier) :
    NPHard (CSP.language L Carrier) := by
  classical
  obtain ⟨choices, witness⟩ := exists_boolean_gadgets_of_noTaylorPolymorphism rigid noTaylor
  let _ : (polymorphismLanguage L Carrier).Structure Bool := projectionStructure choices Bool
  dsimp only at witness
  obtain ⟨subalgebra, quotient, _surjective, representatives, sectionLaw,
    domainFormula, equalityFormula, clauseFormulas, family⟩ := witness
  let _ : Fintype (Pool (Carrier := Carrier) domainFormula clauseFormulas) := Fintype.ofFinite _
  let enumeration := Fintype.equivFin (Pool (Carrier := Carrier) domainFormula clauseFormulas)
  intro source membership
  obtain ⟨Symbol, finiteSymbols, inhabitedSymbols, State, finiteStates, inhabitedStates,
    letters, machine, entry, timeBound, witnessLength, _ready, correct⟩ := np_formulas_uniform source membership
  let _ : Fintype Symbol := finiteSymbols
  let _ : Inhabited Symbol := inhabitedSymbols
  let _ : Fintype State := finiteStates
  let _ : Inhabited State := inhabitedStates
  let wires := fixedFormulaWireCount Symbol State timeBound witnessLength
  let clauses := fixedFormulaClauseCount Symbol State timeBound witnessLength
  let construct := (wordFormula machine entry letters timeBound witnessLength).compute
  refine ⟨formulaGadgetWord domainFormula clauseFormulas enumeration wires clauses construct,
    formulaGadgetWord_polynomialTime domainFormula clauseFormulas enumeration wires clauses construct
      (wordFormula_realizable machine entry letters timeBound witnessLength), ?_⟩
  intro word
  rw [formulaGadgetWord_mem domainFormula clauseFormulas enumeration wires clauses construct
    family representatives sectionLaw]
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

/-- The strict dense relational CSP word language of a nonempty finite rigid
core without a Taylor polymorphism is NP-complete under polynomial-time
many-one reductions certified by finite Mathlib TM0 machines. -/
theorem language_npComplete_of_noTaylorPolymorphism
    (rigid : IsRigidCore L Carrier) (noTaylor : ¬ HasTaylorPolymorphism L Carrier) :
    NPComplete (CSP.language L Carrier) := by
  let _ : Fintype Carrier := Fintype.ofFinite Carrier
  exact ⟨language_inNP L Carrier, language_npHard_of_noTaylorPolymorphism L Carrier rigid noTaylor⟩

end Polytime2.CSP
