import Polytime2.Complexity.NativeStream
import Polytime2.Arrays.ComputedPadding
import Polytime2.Computation.ComputedCall

/-! # Native streams at stored mathematical sizes

Construct the exact word at the stored sizes. The computed frame's zero
padding is then retained as absent native letters at host capacity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

variable {Parameter NewParameter : Type} [Fintype Parameter] [Fintype NewParameter]

/-- Live word length plus the absent sentinel. -/
noncomputable def nativeStreamLength (count : MvPolynomial NewParameter ℕ)
    (domain : EncodedDomain NewParameter) : MvPolynomial NewParameter ℕ :=
  ((count + 1) + domain.widthPolynomial) + 1

private noncomputable def fixedLetterBlock : EncodedDomain Empty :=
  optional (fixed (Fintype.equivFin Letter))

/-- Emit a native coded stream from a payload at its stored size assignment. -/
noncomputable def computedNativeStream (count : MvPolynomial NewParameter ℕ)
    (domain : EncodedDomain NewParameter)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  ((nativeWordStream count domain).atComputedUnarySizes bounds).followedBy
    (padComputedArray fixedLetterBlock (nativeStreamLength count domain) bounds none)
    rfl (by intros; trivial)

theorem computedNativeStream_realizable (count : MvPolynomial NewParameter ℕ)
    (domain : EncodedDomain NewParameter)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) :
    (computedNativeStream count domain bounds).Realizable :=
  ((nativeWordStream_realizable count domain).atComputedUnarySizes bounds).followedBy
    (padComputedArray_realizable fixedLetterBlock (nativeStreamLength count domain) bounds none
      (optional_none_bits _ _)) rfl (by intros; trivial)

/-- The exact word is followed immediately by a sentinel; host padding only
adds absent entries after that sentinel. -/
theorem computedNativeStream_list (count : MvPolynomial NewParameter ℕ)
    (domain : EncodedDomain NewParameter)
    (bounds : NewParameter → MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (arguments : (computedNativeStream count domain bounds).Arguments sizes) :
    ∃ padding : List (Option Letter),
      List.ofFn ((computedNativeStream count domain bounds).compute sizes ⟨arguments, trivial⟩) =
        (List.replicate
          (MvPolynomial.eval (computedSizeAssignment bounds sizes (arguments ()).1) count)
          (Sum.inr (1 : Fin 3) : Letter) ++ (Sum.inr (0 : Fin 3) : Letter) ::
          domain.word (computedSizeAssignment bounds sizes (arguments ()).1) (arguments ()).2).map some ++
        none :: padding := by
  dsimp only [computedNativeStream, followedBy, atComputedUnarySizes, padComputedArray]
  rw [padArrayValues_list, nativeWordStream_list]
  exact ⟨_, List.append_assoc _ _ _⟩

end Polytime2.Complexity
