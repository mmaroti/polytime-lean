import Polytime2.Complexity.CookLevin.MachineLayout
import Polytime2.Computation.Conditional

/-! # Certified neighboring cell coordinates

Neighbor coordinates are clamped at the ends of the mathematical window.
Boundary cases use the existing coordinate unchanged. Interior cases reuse
certified subtraction or successor; they require no caller-supplied padding.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

/-- Select left, center, or right in the finite window of radius twice the
time allowance. The selected direction is specialization-fixed. -/
noncomputable def neighborCoordinate (direction : Fin 3) : Computation Unit Unit :=
  unaryMap (arrayPosition layoutPositions) (arrayPosition layoutPositions) (fun _ _ => True)
    (fun sizes coordinate =>
      if direction.val = 0 then ⟨coordinate.val.val - 1, (Nat.sub_le _ _).trans_lt coordinate.val.isLt⟩
      else if direction.val = 1 then coordinate.val
      else ⟨min (coordinate.val.val + 1) (4 * sizes ()), by
        have bounded := Nat.min_le_right (coordinate.val.val + 1) (4 * sizes ())
        simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
        omega⟩)

/-- The certified coordinate agrees with the neighbor map used by the
mathematical machine simulation. -/
theorem neighborCoordinate_correct (direction : Fin 3) (sizes : Unit → ℕ)
    (arguments : (neighborCoordinate direction).Arguments sizes) :
    ((neighborCoordinate direction).compute sizes ⟨arguments, trivial⟩).val =
      (windowNeighbors (2 * sizes ())
        ⟨(arguments ()).val, by
          have bounded : (arguments ()).val < MvPolynomial.eval sizes layoutPositions :=
            (arguments ()).isLt
          simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one,
            MvPolynomial.eval_X] at bounded
          omega⟩ direction).val := by
  have radius : 2 * (2 * sizes ()) = 4 * sizes () := by omega
  fin_cases direction <;> simp [neighborCoordinate, unaryMap, windowNeighbors, radius]

theorem neighborCoordinate_realizable (direction : Fin 3) : (neighborCoordinate direction).Realizable := by
  fin_cases direction
  · let computation := neighborCoordinate 0
    let condition := fun sizes (arguments : computation.Arguments sizes) => decide ((arguments ()).val < 1)
    apply Realizable.ofCases condition
    · exact (positionWithin_realizable layoutPositions 1).withSpecification computation.precondition
        (fun sizes arguments => condition sizes arguments.val) (by intros; trivial) (by
          intro sizes arguments allowed
          simp [condition, positionWithin])
    · have copied := (copy_realizable (arrayPosition layoutPositions)).withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true)
        (by intros; trivial)
      apply copied.withSpecification _ _ (by intros; assumption)
      intro sizes arguments allowed
      apply Fin.ext
      have zero : (arguments ()).val = 0 := by simpa [condition] using allowed.2
      simp [computation, neighborCoordinate, unaryMap, withPrecondition, copy, zero]
    · let inputs : Unit → EncodedDomain Unit := fun _ => arrayPosition layoutPositions
      let allowed := fun sizes (arguments : ∀ name, (inputs name).Carrier sizes) =>
        computation.precondition sizes arguments ∧ condition sizes arguments = false
      let one := (wirePolynomial 1 layoutPositions).onResults inputs allowed (fun empty => nomatch empty) (by
        intro sizes arguments
        have nonzero : ¬ (arguments.val ()).val < 1 := by simpa [condition] using arguments.property.2
        have bounded : (arguments.val ()).val < MvPolynomial.eval sizes layoutPositions := (arguments.val ()).isLt
        change MvPolynomial.eval sizes (1 : MvPolynomial Unit ℕ) < MvPolynomial.eval sizes layoutPositions
        simp only [map_one]
        omega)
      have oneReady : one.Realizable := by
        apply (wirePolynomial_realizable 1 layoutPositions).onResults
        intro empty
        exact nomatch empty
      have subtracted := (wireSubtract_realizable layoutPositions).onResults inputs allowed
        (fun choice sizes arguments => if choice then one.compute sizes arguments else arguments.val ()) (by
          intro sizes arguments
          change MvPolynomial.eval sizes 1 ≤ (arguments.val ()).val
          have nonzero : ¬ (arguments.val ()).val < 1 := by simpa [condition] using arguments.property.2
          simp only [map_one]
          omega) (by
          intro choice
          cases choice
          · exact Realizable.argument inputs () allowed
          · exact oneReady)
      apply subtracted.withSpecification _ _ (by intros; assumption)
      intro sizes arguments accepted
      apply Fin.ext
      simp [computation, neighborCoordinate, unaryMap, onResults,
        wireSubtract, one, wirePolynomial]
  · exact (copy_realizable (arrayPosition layoutPositions)).withSpecification
      (neighborCoordinate 1).precondition (neighborCoordinate 1).compute (by intros; trivial) (by intros; rfl)
  · let computation := neighborCoordinate 2
    let condition := fun sizes (arguments : computation.Arguments sizes) => decide ((arguments ()).val < 4 * sizes ())
    apply Realizable.ofCases condition
    · exact (positionWithin_realizable layoutPositions (4 * MvPolynomial.X ())).withSpecification
        computation.precondition (fun sizes arguments => condition sizes arguments.val)
        (by intros; trivial) (by intro sizes arguments allowed; simp [condition, positionWithin])
    · have advanced := (wireSuccessor_realizable layoutPositions).withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = true) (by
          intro sizes arguments allowed
          have inside : (arguments ()).val < 4 * sizes () := by simpa [condition] using allowed.2
          change (arguments ()).val + 1 < MvPolynomial.eval sizes layoutPositions
          simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X]
          omega)
      apply advanced.withSpecification _ _ (by intros; assumption)
      intro sizes arguments allowed
      apply Fin.ext
      have inside : (arguments ()).val < 4 * sizes () := by simpa [condition] using allowed.2
      simp [computation, neighborCoordinate, unaryMap, withPrecondition, wireSuccessor,
        Nat.min_eq_left (show (arguments ()).val + 1 ≤ 4 * sizes () by omega)]
    · have copied := (copy_realizable (arrayPosition layoutPositions)).withPrecondition
        (fun sizes arguments => computation.precondition sizes arguments ∧ condition sizes arguments = false)
        (by intros; trivial)
      apply copied.withSpecification _ _ (by intros; assumption)
      intro sizes arguments allowed
      apply Fin.ext
      have outside : ¬ (arguments ()).val < 4 * sizes () := by simpa [condition] using allowed.2
      have bounded := (arguments ()).isLt
      change (arguments ()).val < MvPolynomial.eval sizes layoutPositions at bounded
      simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X] at bounded
      have equal : (arguments ()).val = 4 * sizes () := by omega
      simp [computation, neighborCoordinate, unaryMap, withPrecondition, copy, equal]

end Polytime2.Complexity.CookLevin
