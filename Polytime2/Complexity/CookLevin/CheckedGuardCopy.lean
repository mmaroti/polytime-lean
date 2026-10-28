import Polytime2.Complexity.CookLevin.CheckedGuardJoining
import Polytime2.Circuit.GateWiden

/-! # The three predicate copies required by the mathematical guard compiler -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

/-- Start wires of the three predicate copies, with the first joining gate
between the first and second copies. -/
noncomputable def checkedGuardCopyBase (base : MvPolynomial Bool ℕ) : Fin 3 → MvPolynomial Bool ℕ :=
  ![base, base + wordGuardGateCount + 1, base + 2 * wordGuardGateCount + 1]

private theorem copyAvailable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (copy : Fin 3) (sizes : Bool → ℕ) :
    sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes (checkedGuardCopyBase base copy) := by
  have bounded := available sizes
  fin_cases copy <;> simp [checkedGuardCopyBase, map_add, map_mul, map_ofNat, map_one] at bounded ⊢ <;> omega

private theorem copyWires_bounded (base : MvPolynomial Bool ℕ) (copy : Fin 3) (sizes : Bool → ℕ) :
    MvPolynomial.eval sizes (wordGuardWires (checkedGuardCopyBase base copy)) ≤
      MvPolynomial.eval sizes (checkedGuardWires base) := by
  rw [wordGuardWires_eq]
  fin_cases copy <;>
    simp [checkedGuardCopyBase, checkedGuardWires, map_add, map_mul, map_ofNat, map_one] <;> omega

/-- Emit one copy directly in the final checked circuit's reference codec. -/
noncomputable def checkedGuardCopy (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (copy : Fin 3) : Computation Bool Empty :=
  ((wordGuardProgram (checkedGuardCopyBase base copy) (copyAvailable base available copy)).followedBy
    (mapArray (gateDomain (wordGuardWires (checkedGuardCopyBase base copy))) (gateDomain (checkedGuardWires base))
      wordGuardGateCount (fun sizes gate =>
        (gateWiden (wordGuardWires (checkedGuardCopyBase base copy)) (checkedGuardWires base)
          (copyWires_bounded base copy)).compute sizes ⟨(fun _ => gate), trivial⟩)) rfl (by intros; trivial)).onResults
    Empty.elim (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)

theorem checkedGuardCopy_realizable (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (copy : Fin 3) : (checkedGuardCopy base available copy).Realizable := by
  have copied := (wordGuardProgram_realizable (checkedGuardCopyBase base copy) (copyAvailable base available copy)).followedBy
    (mapArray_realizable _ _ _ _ (gateWiden_realizable _ _ (copyWires_bounded base copy))) rfl (by intros; trivial)
  exact copied.onResults Empty.elim (fun _ _ => True) (fun empty => nomatch empty)
    (by intros; trivial) (fun empty => nomatch empty)

/-- Copy conversion changes neither gate order nor mathematical wire numbers. -/
theorem checkedGuardCopy_value (base : MvPolynomial Bool ℕ)
    (available : ∀ sizes, sizes true * Fintype.card Letter ≤ MvPolynomial.eval sizes base)
    (copy : Fin 3) (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedGuardCopy base available copy).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedGuardCopy base available copy).compute sizes arguments index)) =
      ((wordGuardExpression (sizes true)).compile (MvPolynomial.eval sizes (checkedGuardCopyBase base copy))).1 := by
  simp only [checkedGuardCopy, onResults, followedBy, mapArray, gateWiden_value]
  exact wordGuardProgram_value (checkedGuardCopyBase base copy) (copyAvailable base available copy) sizes
    ⟨(fun empty => nomatch empty), trivial⟩

end Polytime2.Complexity.CookLevin
