import Polytime2.Arrays.FirstFalse

/-! # Boolean arrays as exact-width bit vectors

The mathematical array and bit-vector presentations share canonical bits.
This adapter reuses the identity encoding map, with no traversal or padding.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Present an ordinary Boolean array as its exact little-endian bit vector. -/
noncomputable def booleanArrayBits (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  encodingMap (booleans.arrayOfLength length) (bitVectors length)
    (fun _ values => (BitVec.ofBoolListLE (List.ofFn values)).cast (by simp only [List.length_ofFn]))

theorem booleanArrayBits_realizable (length : MvPolynomial Parameter ℕ) :
    (booleanArrayBits length).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    have clog : Nat.clog 2 2 = 1 := by decide
    simp [width, arrayOfLength_widthPolynomial, booleans, clog]
  · intro sizes values
    rw [FirstFalse.boolean_bits (Parameter := Parameter)]
    exact (ArrayEncoding.bits_ofBoolListLE (List.ofFn values) (by simp only [List.length_ofFn])).symm

/-- The adapter preserves exactly the source array's ordered bits. -/
theorem booleanArrayBits_correct (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : Fin (MvPolynomial.eval sizes length) → Bool) :
    ArrayEncoding.bits ((booleanArrayBits length).compute sizes ⟨(fun _ => values), trivial⟩) =
      List.ofFn values :=
  ArrayEncoding.bits_ofBoolListLE (List.ofFn values) (by simp only [List.length_ofFn])

end Polytime2.Computation
