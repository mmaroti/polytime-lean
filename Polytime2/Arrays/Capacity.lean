import Polytime2.Arithmetic.UnaryWidth
import Polytime2.Computation.ParameterRename
import Polytime2.Arrays.PackingResult

/-! # Stored array capacity conversion

Increasing capacity preserves the actual count and every mathematical element.
Only the internal unary count capacity and zero-padded payload width change.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

variable {Parameter : Type} [Fintype Parameter]

variable {HostParameter : Type} [Fintype HostParameter]

/-- Move size renaming inside a stored-array codec. The actual count and
mathematical elements stay unchanged. -/
noncomputable def boundedArrayRename (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    Computation Parameter Unit :=
  encodingMap ((boundedArray element capacity).renameParameters names)
    (boundedArray (element.renameParameters names) (MvPolynomial.rename names capacity))
    (fun sizes field => ⟨⟨field.1.val, by
      simpa only [MvPolynomial.eval_rename] using field.1.isLt⟩, field.2⟩)

theorem boundedArrayRename_realizable (element : EncodedDomain HostParameter)
    (capacity : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (boundedArrayRename element capacity names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [width, boundedArray, renameParameters_widthPolynomial, boundedUnary, ofBoundedCodec]
  · intro sizes field
    rw [renameParameters_bits]
    exact boundedArrayConvert_bits element (element.renameParameters names) capacity
      (MvPolynomial.rename names capacity) (sizes ∘ names) sizes
      (MvPolynomial.eval_rename names sizes capacity).symm id
      (renameParameters_width element names sizes).symm
      (fun value => (renameParameters_bits element names sizes value).symm) field

/-- View a directly renamed polynomial array through the original array codec
at the projected sizes, without changing its elements or canonical bits. -/
noncomputable def arrayOfLengthRenameView (element : EncodedDomain HostParameter)
    (length : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((element.renameParameters names).arrayOfLength (MvPolynomial.rename names length))
    ((element.arrayOfLength length).renameParameters names)
    (fun sizes values index => values (Fin.cast (MvPolynomial.eval_rename names sizes length).symm index))

theorem arrayOfLengthRenameView_realizable (element : EncodedDomain HostParameter)
    (length : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (arrayOfLengthRenameView element length names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [width, renameParameters_widthPolynomial]
  · intro sizes values
    rw [renameParameters_bits]
    simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, renameParameters_bits]
    exact congrArg List.flatten (List.ofFn_congr (MvPolynomial.eval_rename names sizes length)
      (fun index => ArrayEncoding.bits (element.encode (sizes ∘ names) (values index))))

/-- Move a size renaming inside a polynomial array while preserving every
mathematical element and its canonical bits. -/
noncomputable def arrayOfLengthRename (element : EncodedDomain HostParameter)
    (length : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) : Computation Parameter Unit :=
  encodingMap ((element.arrayOfLength length).renameParameters names)
    ((element.renameParameters names).arrayOfLength (MvPolynomial.rename names length))
    (fun sizes values index => values (Fin.cast (MvPolynomial.eval_rename names sizes length) index))

theorem arrayOfLengthRename_realizable (element : EncodedDomain HostParameter)
    (length : MvPolynomial HostParameter ℕ) (names : HostParameter → Parameter) :
    (arrayOfLengthRename element length names).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    simp [width, renameParameters_widthPolynomial]
  · intro sizes values
    rw [renameParameters_bits]
    simp only [arrayOfLength_encode_bits, ArrayEncoding.bits_encode, renameParameters_bits]
    exact congrArg List.flatten (List.ofFn_congr (MvPolynomial.eval_rename names sizes length).symm
      (fun index => ArrayEncoding.bits (element.encode (sizes ∘ names) (values index))))

/-- Increase a stored array's capacity, retaining its actual count and elements. -/
noncomputable def boundedArrayResize (element : EncodedDomain Parameter)
    (source target : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (boundedArray element source) (boundedArray element target)
    (fun sizes _ => MvPolynomial.eval sizes source ≤ MvPolynomial.eval sizes target)
    (fun _ field => ⟨⟨field.val.1.val, by have bounded := field.val.1.isLt; omega⟩, field.val.2⟩)

theorem boundedArrayResize_realizable (element : EncodedDomain Parameter)
    (source target : MvPolynomial Parameter ℕ) : (boundedArrayResize element source target).Realizable := by
  let computation := boundedArrayResize element source target
  have count := ((boundedArrayCount_realizable element source).withPrecondition computation.precondition
    (by intros; trivial)).followedBy (boundedUnaryResize_realizable source target) rfl
      (by intro sizes arguments valid; exact valid)
  have raw := (boundedArrayPayload_realizable element source).followedBy
    (resizeBits_realizable (source * element.widthPolynomial) (target * element.widthPolynomial))
    rfl (by intros; trivial)
  have payload := raw.withPrecondition computation.precondition (by intros; trivial)
  apply (count.prodMk payload).withEncodedOutput (boundedArray element target) computation.compute
    (by intros; rfl)
  intro sizes arguments
  apply congrArg CallingConvention.tape
  apply congrArg ArrayEncoding.bits
  change ((boundedUnary target).prod (bitVectors (target * element.widthPolynomial))).encode sizes
    (_, (ArrayEncoding.encode (element.encode sizes) (arguments.val ()).1.val (arguments.val ()).2).setWidth
      (MvPolynomial.eval sizes (target * element.widthPolynomial))) =
    ((boundedUnary target).prod (bitVectors (target * element.widthPolynomial))).encode sizes
      (_, ((ArrayEncoding.encode (element.encode sizes) (arguments.val ()).1.val (arguments.val ()).2).setWidth
        (MvPolynomial.eval sizes (source * element.widthPolynomial))).setWidth
          (MvPolynomial.eval sizes (target * element.widthPolynomial)))
  congr 2
  have bounded : (arguments.val ()).1.val * element.width sizes ≤
      MvPolynomial.eval sizes (source * element.widthPolynomial) := by
    simp only [map_mul]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (arguments.val ()).1.isLt)
  dsimp only [width] at bounded
  exact (BitVec.setWidth_setWidth (by omega)).symm

end Polytime2.Computation
