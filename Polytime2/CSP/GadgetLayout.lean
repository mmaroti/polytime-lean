import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Numbering uniformly allocated gadget variables

Each source variable owns its shared block followed by its domain pool.
Clause pools follow those groups. The equivalence and its address formulas
are purely mathematical, with no encoding or machine interfaces.
-/

namespace Polytime2.CSP.GadgetAllocation

universe poolLevel

variable {Pool : Type poolLevel} {poolSize : ℕ}

/-- Dense numbering of the ordinary shared and fresh variable sets. -/
def layoutEquiv (enumeration : Pool ≃ Fin poolSize) (variableCount clauses dimension : ℕ) :
    ((Fin variableCount × Fin dimension) ⊕ ((Fin variableCount ⊕ Fin clauses) × Pool)) ≃
      Fin (variableCount * (dimension + poolSize) + clauses * poolSize) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) enumeration)).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumProdDistrib (Fin variableCount) (Fin clauses) (Fin poolSize))).trans
      ((Equiv.sumAssoc (Fin variableCount × Fin dimension) (Fin variableCount × Fin poolSize)
        (Fin clauses × Fin poolSize)).symm.trans
        ((Equiv.sumCongr (Equiv.prodSumDistrib (Fin variableCount) (Fin dimension) (Fin poolSize)).symm
          (Equiv.refl _)).trans
          ((Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv) (Equiv.refl _)).trans
            ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)))))

theorem layout_shared_val (enumeration : Pool ≃ Fin poolSize) (variableCount clauses dimension : ℕ)
    (source : Fin variableCount) (coordinate : Fin dimension) :
    (layoutEquiv enumeration variableCount clauses dimension (.inl (source, coordinate))).val =
      source.val * (dimension + poolSize) + coordinate.val := by
  simp [layoutEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem layout_domain_val (enumeration : Pool ≃ Fin poolSize) (variableCount clauses dimension : ℕ)
    (source : Fin variableCount) (value : Pool) :
    (layoutEquiv enumeration variableCount clauses dimension (.inr (.inl source, value))).val =
      source.val * (dimension + poolSize) + dimension + (enumeration value).val := by
  simp [layoutEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem layout_clause_val (enumeration : Pool ≃ Fin poolSize) (variableCount clauses dimension : ℕ)
    (clause : Fin clauses) (value : Pool) :
    (layoutEquiv enumeration variableCount clauses dimension (.inr (.inr clause, value))).val =
      variableCount * (dimension + poolSize) + clause.val * poolSize + (enumeration value).val := by
  simp [layoutEquiv, finProdFinEquiv, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Polytime2.CSP.GadgetAllocation
