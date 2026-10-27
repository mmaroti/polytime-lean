import Polytime2.Primitives.BitOperations
import Polytime2.Computation.Fields
import Polytime2.Encoding.Dependent

/-! # Resizing mathematical bit vectors

Keep low bits and truncate or zero extend to the requested width. Certification
composes zero extension to a common width with an existing prefix projection.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Resize a word, preserving its low bits and using zero extension when needed. -/
noncomputable def resizeBits (source target : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (bitVectors source) (bitVectors target)
    (fun sizes value => value.setWidth (MvPolynomial.eval sizes target))

theorem resizeBits_realizable (source target : MvPolynomial Parameter ℕ) :
    (resizeBits source target).Realizable := by
  let common := source + target
  let extend := encodingMap (bitVectors source) (bitVectors common)
    (fun sizes value => value.setWidth (MvPolynomial.eval sizes common))
  have extended : extend.Realizable := by
    apply zeroExtendEncoding_realizable (bitVectors source) (bitVectors common) target
    · intro sizes
      simp [width, common]
    · intro sizes value
      rw [bits_setWidth _ (by simp [common])]
      simp [common]
  let takePrefix := encodingMap (bitVectors common) (bitVectors target)
    (fun sizes value => value.setWidth (MvPolynomial.eval sizes target))
  have projected : takePrefix.Realizable := by
    apply Realizable.Internal.fieldProjection _ _ 0
    intro sizes value
    refine ⟨[], (ArrayEncoding.bits value.val).drop (MvPolynomial.eval sizes target), ?_, rfl⟩
    change ArrayEncoding.bits value.val = [] ++
      (ArrayEncoding.bits (value.val.setWidth (MvPolynomial.eval sizes target)) ++ _)
    rw [List.nil_append, bits_setWidth_take _ (by simp [common])]
    exact (List.take_append_drop _ _).symm
  have combined := extended.followedBy projected rfl (by intros; trivial)
  apply combined.withSpecification (fun _ _ => True) (resizeBits source target).compute (by intros; trivial)
  intro sizes arguments valid
  exact BitVec.setWidth_setWidth_of_le (arguments ()) (by simp [common])

end Polytime2.Computation
