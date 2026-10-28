import Polytime2.Complexity.CookLevin.WordLetterWire

/-! # Certified initial-word membership and head-position tests

These tests classify a mathematical window coordinate. Their bounds depend
only on the word length and time allowance, including empty words.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

private noncomputable def wordCellInterval (upper : MvPolynomial Bool ℕ) : Computation Bool Unit :=
  unaryMap (arrayPosition wordPositions) booleans (fun _ _ => True)
    (fun sizes coordinate => decide (2 * sizes false ≤ coordinate.val.val ∧
      coordinate.val.val < MvPolynomial.eval sizes upper))

private theorem wordCellInterval_realizable (upper : MvPolynomial Bool ℕ) :
    (wordCellInterval upper).Realizable := by
  let inputs : Unit → EncodedDomain Bool := fun _ => arrayPosition wordPositions
  have tested := (booleanOperation_realizable (Parameter := Bool)
    (fun flags : Bool → Bool => !(flags false) && flags true)).onResults inputs (fun _ _ => True)
      (fun choice sizes arguments => if choice then
        (positionWithin wordPositions upper).compute sizes arguments
        else (positionWithin wordPositions (2 * MvPolynomial.X false)).compute sizes arguments)
      (by intros; trivial) (by
        intro choice
        cases choice
        · exact positionWithin_realizable wordPositions (2 * MvPolynomial.X false)
        · exact positionWithin_realizable wordPositions upper)
  apply tested.withSpecification (fun _ _ => True) (wordCellInterval upper).compute (by intros; trivial)
  intro sizes arguments accepted
  simp [wordCellInterval, unaryMap, onResults, booleanOperation, positionWithin, ← decide_not, Nat.not_lt]

/-- The first flag says that the cell lies inside the word; the second says
that it is the unique initial head position. -/
noncomputable def wordCellFlags : Computation Bool Unit :=
  unaryMap (arrayPosition wordPositions) (booleans.prod booleans) (fun _ _ => True)
    (fun sizes coordinate =>
      (decide (2 * sizes false ≤ coordinate.val.val ∧ coordinate.val.val < 2 * sizes false + sizes true),
       decide (coordinate.val.val = 2 * sizes false)))

/-- The flags describe membership and the origin in signed tape coordinates. -/
theorem wordCellFlags_correct (sizes : Bool → ℕ)
    (arguments : wordCellFlags.Arguments sizes) :
    (((wordCellFlags.compute sizes ⟨arguments, trivial⟩).1 = true ↔
      0 ≤ ((arguments ()).val : ℤ) - 2 * sizes false ∧
        ((arguments ()).val : ℤ) - 2 * sizes false < sizes true) ∧
     ((wordCellFlags.compute sizes ⟨arguments, trivial⟩).2 = true ↔
      ((arguments ()).val : ℤ) - 2 * sizes false = 0)) := by
  change ((decide (2 * sizes false ≤ (arguments ()).val ∧
      (arguments ()).val < 2 * sizes false + sizes true) = true ↔ _) ∧
    (decide ((arguments ()).val = 2 * sizes false) = true ↔ _))
  simp only [decide_eq_true_eq]
  constructor <;> omega

theorem wordCellFlags_realizable : wordCellFlags.Realizable := by
  have inside := wordCellInterval_realizable (2 * MvPolynomial.X false + MvPolynomial.X true)
  have head := wordCellInterval_realizable (2 * MvPolynomial.X false + 1)
  apply (inside.prodMk head).withSpecification (fun _ _ => True) wordCellFlags.compute (by intros; trivial)
  intro sizes arguments accepted
  simp only [wordCellFlags, unaryMap, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
  congr 1
  have same : (2 * sizes false ≤ (arguments ()).val ∧ (arguments ()).val < 2 * sizes false + 1) ↔
      (arguments ()).val = 2 * sizes false := by omega
  simp only [same]

end Polytime2.Complexity.CookLevin
