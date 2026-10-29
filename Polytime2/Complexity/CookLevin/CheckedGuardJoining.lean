import Polytime2.Complexity.CookLevin.WordGuardProgram
import Polytime2.Circuit.WireArithmetic

/-! # Fixed joining templates for the checked-word circuit

Three predicate copies are joined to the existing answer by one gate and a
four-gate tail. Every reference is a polynomial in the mathematical sizes.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

/-- Last output offset within one predicate copy. -/
noncomputable def wordGuardOutputOffset : MvPolynomial Bool ℕ :=
  MvPolynomial.X true * MvPolynomial.C letterExpression.gateCount +
    MvPolynomial.X true * MvPolynomial.C letterGuardSuffix.gateCount

theorem wordGuardGateCount_eq : wordGuardGateCount = wordGuardOutputOffset + 1 := by
  simp only [wordGuardGateCount, wordGuardOutputOffset]
  ring

/-- Wire count after compiling the entire selecting guard expression. -/
noncomputable def checkedGuardWires (base : MvPolynomial Bool ℕ) : MvPolynomial Bool ℕ :=
  base + 3 * wordGuardGateCount + 5

private noncomputable def joiningCoordinates (base output : MvPolynomial Bool ℕ) : Fin 8 → MvPolynomial Bool ℕ :=
  ![base + wordGuardOutputOffset, output, base + 2 * wordGuardGateCount, base + 3 * wordGuardGateCount,
    base + 3 * wordGuardGateCount + 1, base + 3 * wordGuardGateCount + 2,
    base + 3 * wordGuardGateCount + 3, base + wordGuardGateCount]

private theorem joiningCoordinate_fits (base output : MvPolynomial Bool ℕ)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ) (port : Fin 8) :
    MvPolynomial.eval sizes (joiningCoordinates base output port) < MvPolynomial.eval sizes (checkedGuardWires base) := by
  have bounded := outputBound sizes
  have count := congrArg (MvPolynomial.eval sizes) wordGuardGateCount_eq
  simp only [map_add, map_one] at count
  fin_cases port <;>
    simp [joiningCoordinates, checkedGuardWires, map_add, map_mul, map_ofNat, map_one] <;> omega

private def joiningTemplates (isTail : Bool) : Fin (if isTail then 4 else 1) → Bool ⊕ (Fin 8 × Fin 8) := by
  cases isTail
  · exact fun _ => .inr (0, 1)
  · exact ![.inr (2, 3), .inl false, .inr (4, 5), .inr (7, 6)]

/-- Emit either the first joining gate or the four-gate final joining block. -/
noncomputable def checkedGuardJoining (base output : MvPolynomial Bool ℕ)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (isTail : Bool) : Computation Bool Empty :=
  (((instantiateProgram (checkedGuardWires base) (joiningTemplates isTail)).onResults
    Empty.elim (fun _ _ => True)
    (fun port sizes _ => ⟨MvPolynomial.eval sizes (joiningCoordinates base output port),
      joiningCoordinate_fits base output outputBound sizes port⟩) (by intros; trivial)).followedBy
    (recordToArray (gateDomain (checkedGuardWires base)) (if isTail then 4 else 1)) rfl (by intros; trivial)).onResults
    Empty.elim (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)

theorem checkedGuardJoining_realizable (base output : MvPolynomial Bool ℕ)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (isTail : Bool) : (checkedGuardJoining base output outputBound isTail).Realizable := by
  have fixed := (instantiateProgram_realizable (checkedGuardWires base) (joiningTemplates isTail)).onResults
    (Empty.elim : Empty → EncodedDomain Bool) (fun _ _ => True)
    (fun port sizes _ => ⟨MvPolynomial.eval sizes (joiningCoordinates base output port),
      joiningCoordinate_fits base output outputBound sizes port⟩) (by intros; trivial) (by
        intro port
        have coordinate := (positionPolynomial_realizable (joiningCoordinates base output port) (checkedGuardWires base)).onResults
          (Empty.elim : Empty → EncodedDomain Bool) (fun _ _ => True) (fun empty => nomatch empty)
          (by intro sizes arguments; exact joiningCoordinate_fits base output outputBound sizes port)
          (fun empty => nomatch empty)
        exact coordinate)
  have converted := fixed.followedBy (recordToArray_realizable _ _) rfl (by intros; trivial)
  exact converted.onResults Empty.elim (fun _ _ => True) (fun empty => nomatch empty)
    (by intros; trivial) (fun empty => nomatch empty)

theorem checkedGuardJoining_first (base output : MvPolynomial Bool ℕ)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedGuardJoining base output outputBound false).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedGuardJoining base output outputBound false).compute sizes arguments index)) =
      [.inr (MvPolynomial.eval sizes (base + wordGuardOutputOffset), MvPolynomial.eval sizes output)] := by
  simp [checkedGuardJoining, followedBy, recordToArray, encodingMap, unaryMap, onResults,
    instantiateProgram, joiningTemplates, joiningCoordinates, gateValue, List.ofFn_succ]

theorem checkedGuardJoining_last (base output : MvPolynomial Bool ℕ)
    (outputBound : ∀ sizes, MvPolynomial.eval sizes output < MvPolynomial.eval sizes base)
    (sizes : Bool → ℕ)
    (arguments : {arguments : (checkedGuardJoining base output outputBound true).Arguments sizes // True}) :
    List.ofFn (fun index => gateValue ((checkedGuardJoining base output outputBound true).compute sizes arguments index)) =
      [.inr (MvPolynomial.eval sizes (base + 2 * wordGuardGateCount), MvPolynomial.eval sizes (base + 3 * wordGuardGateCount)),
       .inl false,
       .inr (MvPolynomial.eval sizes (base + 3 * wordGuardGateCount + 1), MvPolynomial.eval sizes (base + 3 * wordGuardGateCount + 2)),
       .inr (MvPolynomial.eval sizes (base + wordGuardGateCount), MvPolynomial.eval sizes (base + 3 * wordGuardGateCount + 3))] := by
  simp [checkedGuardJoining, followedBy, recordToArray, encodingMap, unaryMap, onResults,
    instantiateProgram, joiningTemplates, joiningCoordinates, gateValue, List.ofFn_succ]

end Polytime2.Complexity.CookLevin
