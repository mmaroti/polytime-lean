import Polytime2.CSP.GadgetWordBounds
import Polytime2.CSP.GadgetWordCompiler

/-! # Standalone native-word gadget compilation

The certificate supplies a finite Mathlib TM0 machine, exact native output on
an otherwise blank tape, and a polynomial transition and output-length bound
in the complete serialized source. The output is the ordinary sized instance
from `gadgetCompilerInstance`, with no dependent frame or capacity padding.
-/

namespace Polytime2.CSP.GadgetExpansion

open EncodedDomain Polytime2.Computation

variable {L : FirstOrder.Language.{0, 0}} [L.IsRelational] [Fintype (RelationSymbol L)]
variable {Carrier : Type} [L.Structure Carrier] [Finite Carrier] [Nonempty Carrier]
variable {dimension poolSize : ℕ}
variable (domainFormula : L.Formula (Fin dimension))
variable (clauseFormulas : (Fin 3 → Bool) → L.Formula (Fin 3 × Fin dimension))
variable (enumeration : Pool (Carrier := Carrier) domainFormula clauseFormulas ≃ Fin poolSize)
variable {Parameter : Type} [Fintype Parameter]

/-- Compile to the exact native instance word. Its variables and solutions are
specified by `gadgetCompilerInstance_count` and
`gadgetCompilerInstance_satisfiable_iff`. All source size headers contribute
to the standalone machine's polynomial bound. -/
theorem gadgetCompilerInstance_polynomialTime (wires clauses : MvPolynomial Parameter ℕ) :
    Complexity.PolynomialTime
      (gadgetCompiler domainFormula clauseFormulas enumeration wires clauses).inputWord id
      (fun input => instanceWord L
        (gadgetCompilerInstance domainFormula clauseFormulas enumeration wires clauses
          input.1 (input.2.val ()))) :=
  gadgetWordCompiler_polynomialTime domainFormula clauseFormulas enumeration wires clauses

end Polytime2.CSP.GadgetExpansion
