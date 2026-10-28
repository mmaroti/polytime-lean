import Polytime2.Arithmetic.UnaryWidth
import Polytime2.Arrays.Count
import Polytime2.TM0.WordBits

/-! # Reading a stored unary count as an ordinary bounded index

The count's canonical bits are Boolean flags. The existing flag counter
recovers its mathematical value, including zero and the capacity itself.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

/-- Preserve a bounded natural while converting its unary codec to binary. -/
noncomputable def boundedUnaryToIndex (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (boundedUnary capacity) (boundedIndex (capacity + 1)) (fun _ _ => True)
    (fun _ count => ⟨count.val.val, by have bounded := count.val.isLt; simpa using bounded⟩)

theorem boundedUnaryToIndex_realizable (capacity : MvPolynomial Parameter ℕ) :
    (boundedUnaryToIndex capacity).Realizable := by
  have flags := (encode_realizable (boundedUnary capacity)).reinterpretOutput
    (booleans.arrayOfLength capacity) (fun _ word index => word.getLsbD index.val)
    (by intros; simp [width, boundedUnary, encodingMap, unaryMap]) (by
      intro sizes word
      rw [WordBits.boolean_arrayOfLength_bits]
      rfl)
  have counted := flags.followedBy (countFlags_realizable capacity) rfl (by intros; trivial)
  apply counted.withEncodedOutput (boundedIndex (capacity + 1)) (boundedUnaryToIndex capacity).compute
    (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  apply congrArg ArrayEncoding.bits
  apply BitVec.eq_of_toNat_eq
  have count := countFlags_correct capacity sizes
    (fun index => ((boundedUnary capacity).encode sizes (arguments.val ())).getLsbD index.val)
  change _ = ((countFlags capacity).compute sizes
    ⟨(fun _ index => ((boundedUnary capacity).encode sizes (arguments.val ())).getLsbD index.val), trivial⟩).toNat
  rw [count]
  change _ = (ArrayEncoding.bits ((boundedUnary capacity).encode sizes (arguments.val ()))).count true
  simp [boundedUnaryToIndex, unaryMap, boundedIndex, boundedIndexOfWidth, boundedUnary,
    BoundedUnary.encode_bits, BoundedUnary.bits_count]

end Polytime2.Computation
