import Polytime2.CSP.WordVerifier
import Polytime2.Complexity.FramedOutput

/-! # Native instance-word output

Certified construction of a dense instance at a polynomial variable count
exports to the existing unary-header word format on every raw input word.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Complexity Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

/-- Emit the existing instance word, including its unary variable count. -/
theorem instanceWord_polynomialTime (variableCount : MvPolynomial Unit ℕ)
    (operation : (size : ℕ) → (Fin size → Letter) →
      Instance L (MvPolynomial.eval (fun _ => size) variableCount))
    (ready : (Computation.mk (fun _ : Unit => letterDomain.array ())
      ((instanceDomain L).substitute (fun _ => variableCount)) (fun _ _ => True)
      (fun sizes arguments => operation (sizes ()) (arguments.val ()))).Realizable) :
    PolynomialTime id id (fun word => instanceWord L
      ⟨MvPolynomial.eval (fun _ => word.length) variableCount, operation word.length (fun index => word[index])⟩) := by
  have framed := ready.onWordOutputWithHeader variableCount
    ((instanceDomain L).substitute (fun _ => variableCount)) operation
  convert framed using 1
  funext word
  simp only [instanceWord, EncodedDomain.word]
  exact congrArg (fun bits =>
    List.replicate (MvPolynomial.eval (fun _ => word.length) variableCount) (.inr (1 : Fin 3)) ++
      .inr 0 :: bits.map Sum.inl)
    (substitute_encode_bits (instanceDomain L) (fun _ => variableCount)
      (fun _ => word.length) (operation word.length (fun index => word[index]))).symm

end Polytime2.CSP
