import Polytime2.Complexity.CookLevin.MachineLayout
import Polytime2.Primitives.FiniteOperations
import Polytime2.Computation.Constant

/-! # Certified selection of a local machine template

The classifier reads a mathematical window coordinate and produces the finite
tag for its boundary flags and selected output bit. Both comparisons reuse
the position rules; the remaining table is fixed with the machine alphabet.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity.CookLevin

open Circuit EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

variable {Symbol State : Type} [Fintype Symbol] [Fintype State]

private noncomputable def tagFromFlags (bit : Fin (cellWidth Symbol State)) : Computation Unit Bool where
  inputDomains _ := booleans
  outputDomain := templateTagDomain (Fintype.card (CellTemplateTag Symbol State))
  precondition _ _ := True
  compute _ arguments := (Fintype.equivFin (CellTemplateTag Symbol State))
    ((arguments.val false, !(arguments.val true)), bit)

private theorem tagFromFlags_realizable (bit : Fin (cellWidth Symbol State)) : (tagFromFlags bit).Realizable := by
  let tag : EncodedDomain Empty := fixed (Equiv.refl (Fin (Fintype.card (CellTemplateTag Symbol State))))
  have raw := (finiteOperation_realizable (fun _ : Bool => (booleans : EncodedDomain Empty)) tag
    (fun arguments => (Fintype.equivFin (CellTemplateTag Symbol State))
      ((arguments false, !(arguments true)), bit))).withConstantSizes (Parameter := Unit)
  have normalized := raw.reinterpretInputs (fun _ : Bool => (booleans : EncodedDomain Unit)) (fun _ _ value => value)
    (by intros; simp [withConstantSizes, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finiteOperation, constant_encode_bits,
      booleans, fixed_encode_bits])
    (fun _ _ => True) (by intros; trivial)
  exact normalized.withSpecification (tagFromFlags bit).precondition (tagFromFlags bit).compute
    (by intros; trivial) (by intros; rfl)

/-- Choose the fixed local table for a window cell and an output bit. -/
noncomputable def boundaryTag (bit : Fin (cellWidth Symbol State)) : Computation Unit Unit :=
  unaryMap (arrayPosition layoutPositions)
    (templateTagDomain (Fintype.card (CellTemplateTag Symbol State))) (fun _ _ => True)
    (fun sizes coordinate => by
      classical
      exact (Fintype.equivFin (CellTemplateTag Symbol State))
        ((decide (coordinate.val.val = 0), decide (coordinate.val.val = 4 * sizes ())), bit))

theorem boundaryTag_realizable (bit : Fin (cellWidth Symbol State)) : (boundaryTag bit).Realizable := by
  let inputs : Unit → EncodedDomain Unit := fun _ => arrayPosition layoutPositions
  have prepared := (tagFromFlags_realizable bit).onResults inputs (fun _ _ => True)
    (fun choice sizes arguments => if choice then
      (positionWithin layoutPositions (4 * MvPolynomial.X ())).compute sizes arguments
      else (positionWithin layoutPositions 1).compute sizes arguments)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact positionWithin_realizable layoutPositions 1
      · exact positionWithin_realizable layoutPositions (4 * MvPolynomial.X ()))
  apply prepared.withSpecification (boundaryTag bit).precondition (boundaryTag bit).compute (by intros; trivial)
  intro sizes arguments allowed
  have bounded : (arguments ()).val < MvPolynomial.eval sizes layoutPositions := (arguments ()).isLt
  simp only [layoutPositions, map_add, map_mul, map_ofNat, map_one, MvPolynomial.eval_X] at bounded
  have last : ¬ (arguments ()).val < 4 * sizes () ↔ (arguments ()).val = 4 * sizes () := by omega
  simp [tagFromFlags, boundaryTag, unaryMap, onResults, positionWithin]
  by_cases inside : (arguments ()).val < 4 * sizes ()
  · have different : (arguments ()).val ≠ 4 * sizes () := by omega
    simp [inside, different]
  · simp [last.mp inside]

end Polytime2.Complexity.CookLevin
