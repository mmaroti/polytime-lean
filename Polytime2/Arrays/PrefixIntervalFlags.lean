import Polytime2.Arrays.PackingIntervals
import Polytime2.Arrays.PackingResult
import Polytime2.Arrays.PositionArithmetic
import Polytime2.Arrays.Tabulate

/-! # Certified selection flags for a prefix and a later interval

Three ordinary endpoint coordinates select the prefix and a half-open
interval. Endpoints at the array's end and empty retained intervals are
supported. Storage and comparison widths remain internal.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Realizable.Internal

variable {Parameter : Type} [Fintype Parameter]

/-- Endpoints are the prefix end, interval start, and interval end, in order. -/
noncomputable def arrayPrefixIntervalFlags (length : MvPolynomial Parameter ℕ) : Computation Parameter (Fin 3) :=
  arrayTabulate (fun _ => arrayPosition (length + 1)) booleans length
    (fun _ endpoints position => decide (position.val < (endpoints 0).val ∨
      (endpoints 1).val ≤ position.val ∧ position.val < (endpoints 2).val))

theorem arrayPrefixIntervalFlags_realizable (length : MvPolynomial Parameter ℕ) :
    (arrayPrefixIntervalFlags length).Realizable := by
  apply arrayTabulate_realizable
  let context : Fin 3 ⊕ Unit → EncodedDomain Parameter :=
    Sum.elim (fun _ => arrayPosition (length + 1)) (fun _ => arrayPosition length)
  have compared (endpoint : Fin 3) := (positionsLess_realizable length (length + 1)).onArguments context
    (fun _ _ => True) (fun choice => if choice then .inl endpoint else .inr ())
    (by intro choice; cases choice <;> rfl) (by intros; trivial)
  have combined := (booleanOperation_realizable (Parameter := Parameter)
    (fun flags : Fin 3 → Bool => flags 0 || (!flags 1 && flags 2))).onResults context (fun _ _ => True)
    (fun endpoint _ arguments => decide ((arguments.val (.inr ())).val < (arguments.val (.inl endpoint)).val))
    (by intros; trivial) compared
  apply combined.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments accepted
  apply Bool.eq_iff_iff.mpr
  simp [onResults, booleanOperation]

/-- The concrete flags agree with the mathematical two-interval selection. -/
theorem arrayPrefixIntervalFlags_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (endpoints : (arrayPrefixIntervalFlags length).Arguments sizes)
    (position : Fin (MvPolynomial.eval sizes length)) :
    (arrayPrefixIntervalFlags length).compute sizes ⟨endpoints, trivial⟩ position =
      decide (position.val < (endpoints 0).val ∨
        (endpoints 1).val ≤ position.val ∧ position.val < (endpoints 2).val) := rfl

end Polytime2.Computation
