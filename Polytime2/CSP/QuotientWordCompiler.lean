import Polytime2.CSP.QuotientCompiler
import Polytime2.CSP.WordVerifier
import Polytime2.Complexity.ComputedNativeStream

/-! # Exact native word export of equation-class compilation

The quotient's actual variable count controls its header and dense table
payload. The standalone output contains neither the computed-size frame nor
capacity padding.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Complexity Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

/-- Construct the sentinel-terminated stream for the computed quotient. -/
noncomputable def quotientWordCompiler (equations : MvPolynomial Unit ℕ) : Computation Unit Bool :=
  (quotientCompiler L equations).followedBy
    (computedNativeStream (MvPolynomial.X ()) (instanceDomain L) (fun _ => MvPolynomial.X ()))
    rfl (by intros; trivial)

theorem quotientWordCompiler_realizable (equations : MvPolynomial Unit ℕ) :
    (quotientWordCompiler L equations).Realizable :=
  (quotientCompiler_realizable L equations).followedBy
    (computedNativeStream_realizable (MvPolynomial.X ()) (instanceDomain L) (fun _ => MvPolynomial.X ()))
    rfl (by intros; trivial)

/-- The live output is exactly the native word of the mathematical quotient. -/
theorem quotientWordCompiler_list (equations : MvPolynomial Unit ℕ) (sizes : Unit → ℕ)
    (arguments : (quotientWordCompiler L equations).Arguments sizes) :
    ∃ padding : List (Option Letter),
      List.ofFn ((quotientWordCompiler L equations).compute sizes ⟨arguments, trivial⟩) =
        (instanceWord L
          ⟨(((quotientCompiler L equations).compute sizes ⟨arguments, trivial⟩).1 ()).val,
            ((quotientCompiler L equations).compute sizes ⟨arguments, trivial⟩).2⟩).map some ++
        none :: padding := by
  have exactStream := computedNativeStream_list (MvPolynomial.X ()) (instanceDomain L)
    (fun _ : Unit => MvPolynomial.X ()) sizes
    (fun _ => (quotientCompiler L equations).compute sizes ⟨arguments, trivial⟩)
  let output := (quotientCompiler L equations).compute sizes ⟨arguments, trivial⟩
  have assignmentEqual : computedSizeAssignment (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ))
      sizes output.1 = (fun _ => (output.1 ()).val) := by
    funext name
    cases name
    rfl
  have payloadWords : (instanceDomain L).word
      (computedSizeAssignment (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ)) sizes output.1)
      output.2 = (instanceDomain L).word (fun _ => (output.1 ()).val) output.2 :=
    congrArg (List.map Sum.inl) (encode_bits_cast_sizes (instanceDomain L) assignmentEqual output.2)
  simp only [MvPolynomial.eval_X] at exactStream
  rw [payloadWords] at exactStream
  exact exactStream

end Polytime2.CSP
