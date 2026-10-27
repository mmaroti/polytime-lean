import Polytime2.Complexity.UnarySize
import Polytime2.Complexity.PairFields
import Polytime2.Computation.ComputedHost

/-! # Preparing the variable count while retaining both word fields

The field pair contains the instance word and witness word. Read the leading
instance count into the computed-size frame while retaining the exact pair.
A valid header yields its parsed variable count; validation remains separate.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

private noncomputable def fieldDomain : EncodedDomain Unit :=
  boundedArray letterDomain (MvPolynomial.X ())

private noncomputable def countReader : Computation Unit Unit :=
  (pairProjection fieldDomain fieldDomain false).followedBy fieldVariableCount rfl (by intros; trivial)

private theorem countReader_realizable : countReader.Realizable :=
  (pairProjection_realizable fieldDomain fieldDomain false).followedBy fieldVariableCount_realizable
    rfl (by intros; trivial)

/-- Retain the instance/witness word pair while preparing its variable count
as a bounded unary size. The original host size remains in the frame. -/
noncomputable def prepareFieldCount : Computation Unit Unit :=
  computedHostFrame (fun _ : Unit => MvPolynomial.X ()) (fieldDomain.prod fieldDomain)
    (fun sizes pair _ => countReader.compute sizes ⟨(fun _ => pair), trivial⟩)

theorem prepareFieldCount_realizable : prepareFieldCount.Realizable := by
  apply computedHostFrame_realizable
  intro name
  exact countReader_realizable

/-- When the instance header parses, the prepared size is its exact count. -/
theorem prepareFieldCount_parsed (sizes : Unit → ℕ)
    (pair : (fieldDomain.prod fieldDomain).Carrier sizes) (count : ℕ) (payload : Word)
    (parsed : readPairHeader (List.ofFn pair.1.2) = some (count, payload)) :
    ((prepareFieldCount.compute sizes ⟨(fun _ => pair), trivial⟩).1 (.inr ())).val = count :=
  fieldVariableCount_parsed sizes pair.1 count payload parsed

end Polytime2.CSP
