import Polytime2.Complexity.CookLevin.WordInput
import Polytime2.Circuit.WireArithmetic

/-! # Certified references to external word bits

The mathematical sizes are the time allowance (false) and word length (true).
A window cell inside the initial word refers to its letter's one-hot bit.
Working capacities are derived internally, including for zero time.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation

noncomputable def wordPositions : MvPolynomial Bool ℕ := 4 * MvPolynomial.X false + 1

/-- External letter bits followed by the two Boolean constant gates. -/
noncomputable def wordPreparedWires : MvPolynomial Bool ℕ :=
  MvPolynomial.X true * MvPolynomial.C (Fintype.card Letter) + 2

private theorem wordLetterWire_fits (letter : Fin (Fintype.card Letter)) (sizes : Bool → ℕ)
    (cell : Fin (MvPolynomial.eval sizes wordPositions))
    (inside : 2 * sizes false ≤ cell.val ∧ cell.val < 2 * sizes false + sizes true) :
    (cell.val - 2 * sizes false) * Fintype.card Letter + letter.val <
      MvPolynomial.eval sizes wordPreparedWires := by
  have bounded := (finProdFinEquiv ((⟨cell.val - 2 * sizes false, by omega⟩ : Fin (sizes true)), letter)).isLt
  have referenceBound : (cell.val - 2 * sizes false) * Fintype.card Letter + letter.val <
      sizes true * Fintype.card Letter := by
    simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm, Nat.add_comm] using bounded
  simp only [wordPreparedWires, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_ofNat]
  omega

/-- Reference to a fixed letter bit at a window cell lying inside the word.
The precondition states precisely that the cell is an actual word position. -/
noncomputable def wordLetterWire (letter : Fin (Fintype.card Letter)) : Computation Bool Unit :=
  specification (fun _ => arrayPosition wordPositions) (arrayPosition wordPreparedWires)
    (fun sizes arguments => 2 * sizes false ≤ (arguments ()).val ∧
      (arguments ()).val < 2 * sizes false + sizes true)
    (fun sizes arguments => ⟨((arguments.val ()).val - 2 * sizes false) * Fintype.card Letter + letter.val,
      wordLetterWire_fits letter sizes (arguments.val ()) arguments.property⟩)

theorem wordLetterWire_value (letter : Fin (Fintype.card Letter)) (sizes : Bool → ℕ)
    (arguments : {arguments : (wordLetterWire letter).Arguments sizes //
      (wordLetterWire letter).precondition sizes arguments}) :
    ((wordLetterWire letter).compute sizes arguments).val =
      ((arguments.val ()).val - 2 * sizes false) * Fintype.card Letter + letter.val := by
  simp only [wordLetterWire, specification_compute]

theorem wordLetterWire_realizable (letter : Fin (Fintype.card Letter)) :
    (wordLetterWire letter).Realizable := by
  let inputs := (wordLetterWire letter).inputDomains
  let allowed := (wordLetterWire letter).precondition
  let origin : MvPolynomial Bool ℕ := 2 * MvPolynomial.X false
  let capacity := wordPositions + wordPreparedWires
  let reference := (wireOfPosition wordPositions capacity
    (by intro sizes; simp only [capacity, map_add]; omega)).withPrecondition allowed (by intros; trivial)
  have referenceReady : reference.Realizable :=
    (wireOfPosition_realizable wordPositions capacity
      (by intro sizes; simp only [capacity, map_add]; omega)).withPrecondition allowed (by intros; trivial)
  let start := (wirePolynomial origin capacity).onResults inputs allowed (fun empty => nomatch empty) (by
    intro sizes arguments
    change MvPolynomial.eval sizes origin < MvPolynomial.eval sizes capacity
    simp only [origin, capacity, wordPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
    omega)
  have startReady : start.Realizable := by
    apply (wirePolynomial_realizable origin capacity).onResults
    intro empty
    exact nomatch empty
  let difference := (wireSubtract capacity).onResults inputs allowed
    (fun choice sizes arguments => if choice then start.compute sizes arguments else reference.compute sizes arguments) (by
      intro sizes arguments
      change MvPolynomial.eval sizes origin ≤ (arguments.val ()).val
      simpa only [origin, map_mul, map_ofNat, MvPolynomial.eval_X] using arguments.property.1)
  have differenceReady : difference.Realizable := by
    apply (wireSubtract_realizable capacity).onResults
    intro choice
    cases choice
    · exact referenceReady
    · exact startReady
  have smallDifference (sizes : Bool → ℕ) (arguments : ∀ name, (inputs name).Carrier sizes)
      (inside : allowed sizes arguments) :
      (arguments ()).val - 2 * sizes false < MvPolynomial.eval sizes wordPreparedWires := by
    have bounded : (arguments ()).val - 2 * sizes false < sizes true := by
      change 2 * sizes false ≤ (arguments ()).val ∧ (arguments ()).val < 2 * sizes false + sizes true at inside
      omega
    have positive : 0 < Fintype.card Letter := Fintype.card_pos
    have scaled := Nat.mul_le_mul_left (sizes true) (Nat.succ_le_of_lt positive)
    simp only [Nat.mul_one] at scaled
    simp only [wordPreparedWires, map_add, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
    omega
  have narrowed := differenceReady.followedBy (wireCast_realizable capacity wordPreparedWires) rfl (by
    intro sizes arguments inside
    change (arguments ()).val - MvPolynomial.eval sizes origin < MvPolynomial.eval sizes wordPreparedWires
    simpa only [origin, map_mul, map_ofNat, MvPolynomial.eval_X] using smallDifference sizes arguments inside)
  have complete := narrowed.followedBy
    (wireAffine_realizable wordPreparedWires (MvPolynomial.C letter.val) (Fintype.card Letter)) rfl (by
      intro sizes arguments inside
      change MvPolynomial.eval sizes (MvPolynomial.C letter.val) + Fintype.card Letter *
        ((arguments ()).val - MvPolynomial.eval sizes origin) < MvPolynomial.eval sizes wordPreparedWires
      simpa only [origin, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C, Nat.mul_comm, Nat.add_comm] using
        wordLetterWire_fits letter sizes (arguments ()) inside)
  apply complete.withSpecification (wordLetterWire letter).precondition (wordLetterWire letter).compute
    (by intros; assumption)
  intro sizes arguments inside
  apply Fin.ext
  rw [wordLetterWire_value]
  change MvPolynomial.eval sizes (MvPolynomial.C letter.val) + Fintype.card Letter *
    ((arguments ()).val - MvPolynomial.eval sizes origin) = _
  simp only [origin, map_mul, map_ofNat, MvPolynomial.eval_X, MvPolynomial.eval_C]
  ring

end Polytime2.Complexity.CookLevin
