import Polytime2.Complexity.CookLevin.CheckedGuardCopy
import Polytime2.Circuit.GuardLayout

/-! # Complete canonical program appended by the checked-word guard -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

private noncomputable def firstCopyAndJoin (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (checkedGuardWires base)) wordGuardGateCount 1).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes arguments => ((checkedGuardCopy base available 0).compute sizes arguments,
      (checkedGuardJoining base output outputBound false).compute sizes arguments)) (by intros; trivial)

private theorem firstCopyAndJoin_realizable (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) :
    (firstCopyAndJoin base output available outputBound).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (checkedGuardCopy_realizable base available 0).prodMk (checkedGuardJoining_realizable base output outputBound false)

private noncomputable def remainingCopies (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (checkedGuardWires base)) wordGuardGateCount wordGuardGateCount).onResults
    Empty.elim (fun _ _ => True) (fun _ sizes arguments =>
      ((checkedGuardCopy base available 1).compute sizes arguments,
       (checkedGuardCopy base available 2).compute sizes arguments)) (by intros; trivial)

private theorem remainingCopies_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base) :
    (remainingCopies base available).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (checkedGuardCopy_realizable base available 1).prodMk (checkedGuardCopy_realizable base available 2)

private noncomputable def allCopies (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (checkedGuardWires base)) (wordGuardGateCount + 1)
    (wordGuardGateCount + wordGuardGateCount)).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes arguments => ((firstCopyAndJoin base output available outputBound).compute sizes arguments,
      (remainingCopies base available).compute sizes arguments)) (by intros; trivial)

private theorem allCopies_realizable (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) :
    (allCopies base output available outputBound).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (firstCopyAndJoin_realizable base output available outputBound).prodMk (remainingCopies_realizable base available)

/-- Emit all predicate copies and joining gates of the original selector. -/
noncomputable def checkedGuardProgram (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) : Computation Bool Empty :=
  (arrayAppend (gateDomain (checkedGuardWires base))
    ((wordGuardGateCount + 1) + (wordGuardGateCount + wordGuardGateCount)) 4).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes arguments => ((allCopies base output available outputBound).compute sizes arguments,
      (checkedGuardJoining base output outputBound true).compute sizes arguments)) (by intros; trivial)

theorem checkedGuardProgram_realizable (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base) :
    (checkedGuardProgram base output available outputBound).Realizable := by
  apply (arrayAppend_realizable _ _ _).onResults
  intro singleton
  cases singleton
  exact (allCopies_realizable base output available outputBound).prodMk (checkedGuardJoining_realizable base output outputBound true)

/-- The constructed array is exactly the compiler's guard expression, with
all three copies at the original compiler's offsets. -/
theorem checkedGuardProgram_value (base output : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedGuardProgram base output available outputBound).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedGuardProgram base output available outputBound).compute sizes arguments index)) =
      ((Expression.select (wordGuardExpression (sizes true)) (.wire (MvPolynomial.eval sizes output))
        (.constant false)).compile (MvPolynomial.eval sizes base)).1 := by
  rcases arguments with ⟨arguments, accepted⟩
  have unique : arguments = (fun empty => nomatch empty) := by funext empty; cases empty
  subst arguments
  simp only [checkedGuardProgram, allCopies, remainingCopies, firstCopyAndJoin, onResults]
  rw [List.ofFn_comp' _ gateValue, arrayAppend_list]
  simp only [arrayAppend_list]
  simp only [List.map_append, List.map_ofFn, Function.comp_def]
  rw [checkedGuardCopy_value]
  erw [checkedGuardJoining_first base output outputBound sizes ⟨(fun empty => nomatch empty), trivial⟩]
  rw [checkedGuardCopy_value, checkedGuardCopy_value]
  erw [checkedGuardJoining_last base output outputBound sizes ⟨(fun empty => nomatch empty), trivial⟩]
  have positive : 0 < (wordGuardExpression (sizes true)).gateCount := by
    rw [← wordGuardGateCount_eval]
    exact wordGuardGateCount_positive sizes
  rw [Expression.selectWire_compile_blocks _ positive]
  have count := congrArg (MvPolynomial.eval sizes) wordGuardGateCount_eq
  simp only [map_add, map_one, wordGuardGateCount_eval] at count
  have firstReference : MvPolynomial.eval sizes (base + wordGuardOutputOffset) =
      MvPolynomial.eval sizes base + (wordGuardExpression (sizes true)).gateCount - 1 := by
    simp only [map_add]
    omega
  rw [firstReference]
  simp [checkedGuardCopyBase, map_add, map_mul, map_ofNat, map_one, wordGuardGateCount_eval,
    List.append_assoc]

end Polytime2.Complexity.CookLevin
