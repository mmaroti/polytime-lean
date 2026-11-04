import Polytime2.CSP.QuotientCompiler
import Polytime2.Complexity.Realizable

/-! # Standalone export of equation-class compilation

The shared export includes unary size headers, argument preparation, and
canonical result framing. This exports the quotient component's dependent
result codec. `GadgetExport` supplies the separate native instance-word export.
-/

namespace Polytime2.CSP

open Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

theorem quotientCompiler_tm0 (equations : MvPolynomial Unit ℕ) :
    (quotientCompiler L equations).TM0Realizable :=
  (quotientCompiler_realizable L equations).tm0

/-- Both execution and output length are polynomial in the entire serialized
input, including its unary vertex-count header. -/
theorem quotientCompiler_polynomialTime (equations : MvPolynomial Unit ℕ) :
    Complexity.PolynomialTime (quotientCompiler L equations).inputWord
      (quotientCompiler L equations).outputWord (quotientCompiler L equations).result :=
  (quotientCompiler_realizable L equations).polynomialTime

end Polytime2.CSP
