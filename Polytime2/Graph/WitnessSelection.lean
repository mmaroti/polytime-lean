import Polytime2.Graph.ThreeSATClique
import Polytime2.Primitives.FiniteOperations

/-! # Certified three-way literal selection

The selector receives the truth values of one clause's three literals. Its
certificate is a fixed finite table, independent of all formula dimensions.
-/

namespace Polytime2.SAT

open EncodedDomain Polytime2.Computation

/-- Choose a true literal position, defaulting to the last position only when
needed. Correctness under a satisfied clause is `truePosition_true`. -/
noncomputable def selectTrueLiteral : Computation Empty (Fin 3) :=
  finiteOperation (fun _ => booleans) (fixed (Equiv.refl (Fin 3))) truePosition

theorem selectTrueLiteral_realizable : selectTrueLiteral.Realizable :=
  finiteOperation_realizable _ _ _

end Polytime2.SAT
