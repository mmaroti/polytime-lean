import Polytime2.Encoding.EncodedArray
import Polytime2.Encoding.BinaryEncoding
import Mathlib.Data.Fintype.Basic

/-! # Canonical finite subsets of a finite coordinate interval

The public carrier is an ordinary finset. Its canonical bits are its membership
flags in coordinate order, including the zero-width encoding of the empty
interval. Clique witnesses use this codec without exposing storage masks.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Membership flags give an equivalence with ordinary finite subsets. -/
noncomputable def finiteSubsetEquiv (size : ℕ) : Finset (Fin size) ≃ (Fin size → Bool) where
  toFun selected index := decide (index ∈ selected)
  invFun flags := Finset.univ.filter (fun index => flags index = true)
  left_inv := by intro selected; ext index; simp
  right_inv := by intro flags; funext index; simp

/-- Encode exactly one membership bit per mathematical coordinate. -/
noncomputable def finiteSubsets (length : MvPolynomial Parameter ℕ) : EncodedDomain Parameter :=
  (booleans.arrayOfLength length).reindex
    (fun sizes => Finset (Fin (MvPolynomial.eval sizes length)))
    (fun sizes => finiteSubsetEquiv (MvPolynomial.eval sizes length))

/-- Every bit records membership, with no inactive or noncanonical storage. -/
theorem finiteSubsets_bits (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (selected : Finset (Fin (MvPolynomial.eval sizes length))) :
    ArrayEncoding.bits ((finiteSubsets length).encode sizes selected) =
      List.ofFn (fun index => decide (index ∈ selected)) := by
  change ArrayEncoding.bits ((booleans.arrayOfLength length).encode sizes
    (finiteSubsetEquiv _ selected)) = _
  rw [arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  have scalar (flag : Bool) : ArrayEncoding.bits (booleans.encode sizes flag) = [flag] := by
    cases flag <;> simp [booleans, fixed, ofCodec, ArrayEncoding.bits, List.ofFn_succ] <;> decide
  simp only [scalar]
  change (List.ofFn ((fun flag : Bool => [flag]) ∘ (fun index => decide (index ∈ selected)))).flatten = _
  rw [← List.map_ofFn]
  exact List.flatMap_singleton' _

end Polytime2.EncodedDomain
