import Polytime2.Complexity.CookLevin.WordGuardPrefixes
import Polytime2.Complexity.CookLevin.WordGuardSuffixes
import Polytime2.Arrays.Append

/-! # Complete canonical gate array for the letter-code predicate -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

/-- Exact number of gates in the compiled word-code predicate. -/
noncomputable def wordGuardGateCount : MvPolynomial Bool ℕ :=
  MvPolynomial.X true * MvPolynomial.C letterExpression.gateCount + 1 +
    MvPolynomial.X true * MvPolynomial.C letterGuardSuffix.gateCount

theorem wordGuardWires_eq (base : MvPolynomial Bool ℕ) :
    wordGuardWires base = base + wordGuardGateCount := by
  simp only [wordGuardWires, wordGuardGateCount, letterGuardSuffix_gateCount]
  ring

theorem wordGuardGateCount_eval (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes wordGuardGateCount = (wordGuardExpression (sizes true)).gateCount := by
  rw [wordGuardExpression_gateCount]
  simp only [wordGuardGateCount, letterGuardSuffix_gateCount, map_add, map_mul, map_one,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  ring

theorem wordGuardGateCount_positive (sizes : Bool → ℕ) : 0 < MvPolynomial.eval sizes wordGuardGateCount := by
  simp only [wordGuardGateCount, map_add, map_mul, map_one, MvPolynomial.eval_X, MvPolynomial.eval_C]
  omega

private noncomputable def terminalTrue (wires : MvPolynomial Bool ℕ) : Computation Bool Empty :=
  arrayTabulate Empty.elim (gateDomain wires) 1 (fun _ _ _ => Sum.inl true)

private theorem terminalTrue_realizable (wires : MvPolynomial Bool ℕ) : (terminalTrue wires).Realizable := by
  apply arrayTabulate_realizable
  let inputs : Empty ⊕ Unit → EncodedDomain Bool := Sum.elim Empty.elim (fun _ => arrayPosition 1)
  have constant := (instantiateGate_realizable wires (arity := 0) (.inl true)).onResults inputs (fun _ _ => True)
    (fun port => Fin.elim0 port) (by intros; trivial) (fun port => Fin.elim0 port)
  exact constant.withSpecification (fun _ _ => True) _ (by intros; trivial) (by intros; rfl)

private theorem terminalTrue_value (wires : MvPolynomial Bool ℕ) (sizes : Bool → ℕ)
    (arguments : {arguments : (terminalTrue wires).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((terminalTrue wires).compute sizes arguments index)) = [.inl true] := by
  simp [terminalTrue, arrayTabulate, gateValue, List.ofFn_succ]

private noncomputable def prefixesAndTrue (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (wordGuardWires base))
    (MvPolynomial.X true * MvPolynomial.C letterExpression.gateCount) 1).onResults
    Empty.elim (fun _ _ => True) (fun _ sizes arguments =>
      ((wordGuardPrefixes base available).compute sizes arguments,
       (terminalTrue (wordGuardWires base)).compute sizes arguments)) (by intros; trivial)

private theorem prefixesAndTrue_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (prefixesAndTrue base available).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (wordGuardPrefixes_realizable base available).prodMk (terminalTrue_realizable _)

private theorem prefixesAndTrue_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ) (arguments : {arguments : (prefixesAndTrue base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((prefixesAndTrue base available).compute sizes arguments index)) =
      List.ofFn (fun index => gateValue ((wordGuardPrefixes base available).compute sizes arguments index)) ++ [.inl true] := by
  simp only [prefixesAndTrue, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  rw [terminalTrue_value]

/-- Emit every gate of the original mathematical word-code predicate. -/
noncomputable def wordGuardProgram (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (wordGuardWires base))
    (MvPolynomial.X true * MvPolynomial.C letterExpression.gateCount + 1)
    (MvPolynomial.X true * MvPolynomial.C letterGuardSuffix.gateCount)).onResults
    Empty.elim (fun _ _ => True) (fun _ sizes arguments =>
      ((prefixesAndTrue base available).compute sizes arguments,
       (wordGuardSuffixes base available).compute sizes arguments)) (by intros; trivial)

theorem wordGuardProgram_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (wordGuardProgram base available).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (prefixesAndTrue_realizable base available).prodMk (wordGuardSuffixes_realizable base available)

/-- Exact agreement with the complete predicate compiler, including the
empty word's single true gate. -/
theorem wordGuardProgram_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ) (arguments : {arguments : (wordGuardProgram base available).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((wordGuardProgram base available).compute sizes arguments index)) =
      ((wordGuardExpression (sizes true)).compile (MvPolynomial.eval sizes base)).1 := by
  have letterCast {first second : ℕ} (equal : first = second) (position : Fin first) :
      wordLetterExpression second (position.cast equal) = wordLetterExpression first position := by
    cases equal
    rfl
  simp only [wordGuardProgram, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  rw [prefixesAndTrue_value, wordGuardPrefixes_value, wordGuardSuffixes_value]
  rw [wordGuardExpression_compile_blocks]
  simp only [MvPolynomial.eval_X, List.append_assoc]
  simp only [← Fin.cast_rev, Fin.val_cast, letterCast]

end Polytime2.Complexity.CookLevin
