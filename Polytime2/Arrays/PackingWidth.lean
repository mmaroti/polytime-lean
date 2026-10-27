import Polytime2.Arrays.PackingRead
import Polytime2.Arrays.Capacity

/-! # Validating the exact width of a stored array field

The stored count is read once and compared with the requested mathematical
polynomial length. The guard is total even when that length exceeds the host
capacity. Extraction remains a separate computation behind this guard.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {HostParameter Parameter : Type} [Fintype HostParameter] [Fintype Parameter]

private noncomputable def storedArrayCount (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    Computation Parameter Unit :=
  unaryMap ((boundedArray element capacity).renameParameters names)
    ((boundedUnary capacity).renameParameters names) (fun _ _ => True) (fun _ field => field.val.1)

private theorem storedArrayCount_realizable (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (storedArrayCount element capacity names).Realizable := by
  exact (boundedArrayCount_realizable element capacity).renameParameters names

/-- Test the stored field length against an exact mathematical polynomial.
This guard alone does not validate any element codes. -/
noncomputable def boundedArrayHasLength (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (requested : MvPolynomial Parameter ℕ) : Computation Parameter Unit where
  inputDomains _ := (boundedArray element capacity).renameParameters names
  outputDomain := booleans
  precondition _ _ := True
  compute sizes arguments := decide ((arguments.val ()).1.val = MvPolynomial.eval sizes requested)

theorem boundedArrayHasLength_realizable (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter)
    (requested : MvPolynomial Parameter ℕ) :
    (boundedArrayHasLength element capacity names requested).Realizable := by
  let renamedCapacity := MvPolynomial.rename names capacity
  have count := (storedArrayCount_realizable element capacity names).reinterpretOutput
    (boundedUnary renamedCapacity)
    (fun sizes value => ⟨value.val, by simpa only [renamedCapacity, MvPolynomial.eval_rename] using value.isLt⟩)
    (by intro sizes; simp [width, renamedCapacity, boundedUnary, storedArrayCount, unaryMap])
    (by
      intro sizes value
      change ArrayEncoding.bits ((boundedUnary renamedCapacity).encode sizes _) =
        ArrayEncoding.bits (((boundedUnary capacity).renameParameters names).encode sizes value)
      rw [renameParameters_bits]
      change ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval sizes renamedCapacity) _) =
        ArrayEncoding.bits (BoundedUnary.encode (MvPolynomial.eval (sizes ∘ names) capacity) value)
      rw [BoundedUnary.encode_bits, BoundedUnary.encode_bits]
      simp only [renamedCapacity, MvPolynomial.eval_rename])
  have checked := count.followedBy (boundedUnaryEqualsPolynomial_realizable renamedCapacity requested)
    rfl (by intros; trivial)
  exact checked.withSpecification (fun _ _ => True)
    (boundedArrayHasLength element capacity names requested).compute (by intros; trivial) (by intros; rfl)

end Polytime2.Computation
