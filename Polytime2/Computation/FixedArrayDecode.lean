import Polytime2.Computation.CodecDecode
import Polytime2.Primitives.FiniteOperations
import Polytime2.Arrays.Transform
import Polytime2.Arrays.AllTrue
import Polytime2.Computation.Constant

/-! # Certified decoding of arrays over a specialization-fixed codec

A fixed scalar bit width makes scalar validation a finite specialization.
Array length is an arbitrary runtime polynomial. No inhabitant or default
value is needed for rejected codes or empty arrays.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain

namespace FixedArrayDecode

variable {Parameter : Type} [Fintype Parameter]
variable (element : EncodedDomain Empty) (length : MvPolynomial Parameter ℕ)

private noncomputable def valueBits : EncodedDomain Parameter :=
  (bitVectors element.widthPolynomial).constant

private noncomputable def valueValid : Computation Parameter Unit :=
  unaryMap (valueBits element) booleans (fun _ _ => True)
    (fun _ bits => (element.decode Empty.elim bits.val).isSome)

private theorem valueValid_realizable : (valueValid (Parameter := Parameter) element).Realizable := by
  let source : EncodedDomain Empty := bitVectors element.widthPolynomial
  let test := fun bits => (element.decode Empty.elim bits).isSome
  have raw := (finitePredicate_realizable source test).withConstantSizes (Parameter := Parameter)
  exact raw.reinterpretOutput (booleans : EncodedDomain Parameter) (fun _ value => value)
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, constant_encode_bits,
      booleans, fixed_encode_bits])

/-- Validate every entry of an exactly framed scalar-code array. No default
value or inhabitance hypothesis is needed, even for a zero-width carrier. -/
private noncomputable def codesValid : Computation Parameter Unit :=
  (mapArray (valueBits element) booleans length
    (fun _ bits => (element.decode Empty.elim bits).isSome)).followedBy
      (arrayAllTrue length) rfl (by intros; trivial)

private theorem codesValid_realizable : (codesValid element length).Realizable := by
  have mapped := mapArray_realizable (valueBits element) booleans length
    (fun _ bits => (element.decode Empty.elim bits).isSome)
    (valueValid_realizable element)
  exact mapped.followedBy (arrayAllTrue_realizable length) rfl (by intros; trivial)

/-- Validation accepts exactly when each canonical scalar decoder succeeds. -/
private theorem codesValid_correct (sizes : Parameter → ℕ)
    (arguments : (codesValid element length).Arguments sizes) :
    (codesValid element length).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∀ index, (element.decode Empty.elim
        (arguments () index)).isSome = true := by
  exact arrayAllTrue_correct length sizes _

private noncomputable def codeArray : EncodedDomain Parameter :=
  (valueBits element).arrayOfLength length

private theorem codeArray_full (sizes : Parameter → ℕ) :
    Function.Surjective ((codeArray element length).encode sizes) := by
  apply arrayOfLength_encode_surjective
  intro array bits
  refine ⟨bits.cast (by simp [valueBits, width, EncodedDomain.constant, bitVectors]), ?_⟩
  simp [valueBits, EncodedDomain.constant, bitVectors, ofCodec]

/-- Frame an exact array-width bit vector into all scalar code blocks.
Framing accepts every pattern; validity is checked by the subsequent decoder. -/
private noncomputable def bitBlocks : Computation Parameter Unit :=
  decodeFullCodec (codeArray element length) (codeArray_full element length)

private theorem bitBlocks_realizable : (bitBlocks element length).Realizable :=
  decodeFullCodec_realizable _ _

/-- Framing preserves the exact input bits, including at zero width. -/
private theorem bitBlocks_correct (sizes : Parameter → ℕ)
    (bits : BitVec ((codeArray element length).width sizes)) :
    (codeArray element length).encode sizes
      ((bitBlocks element length).compute sizes ⟨(fun _ => bits), trivial⟩) = bits :=
  (codeArray element length).encode_decode sizes bits _
    (decodeFullCodec_correct (codeArray element length) (codeArray_full element length) sizes bits)

private noncomputable def decodedArray : EncodedDomain Parameter :=
  (element.constant : EncodedDomain Parameter).arrayOfLength
    length

private noncomputable def readCodes : Computation Parameter Unit where
  inputDomains _ := codeArray element length
  outputDomain := decodedArray element length
  precondition _ arguments := ∀ index,
    (element.decode Empty.elim
      (arguments () index)).isSome = true
  compute _ arguments index :=
    (element.decode Empty.elim
      (arguments.val () index)).get (arguments.property index)

private theorem readCodes_realizable : (readCodes element length).Realizable := by
  have copied := (copy_realizable (codeArray element length)).withPrecondition
    (readCodes element length).precondition (by intros; trivial)
  apply copied.withEncodedOutput (decodedArray element length) (readCodes element length).compute
    (by intro sizes; simp [decodedArray, codeArray, valueBits, width, constant_widthPolynomial,
      copy, withPrecondition])
  intro sizes arguments
  apply congrArg CallingConvention.tape
  change ArrayEncoding.bits ((decodedArray element length).encode sizes _) =
    ArrayEncoding.bits ((codeArray element length).encode sizes (arguments.val ()))
  simp only [decodedArray, codeArray, arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext index
  change ArrayEncoding.bits ((element.constant).encode sizes _) =
    ArrayEncoding.bits ((valueBits element).encode sizes (arguments.val () index))
  rw [constant_encode_bits]
  have canonical := element.encode_decode
    Empty.elim (arguments.val () index) _ (Option.some_get (arguments.property index)).symm
  simpa [readCodes, valueBits, constant_encode_bits, bitVectors, ofCodec, ArrayEncoding.bits_cast]
    using congrArg ArrayEncoding.bits canonical

/-- Decode every entry of an exactly framed code array. Invalid entries reject
before the bit-preserving reader runs; successful output contains actual values. -/
private noncomputable def decodeCodes : Computation Parameter Unit :=
  (readCodes element length).optionalGuard (fun _ _ => True)
    (fun sizes arguments => (codesValid element length).compute sizes ⟨arguments, trivial⟩)
    (fun sizes arguments _ accepted => (codesValid_correct element length sizes arguments).mp accepted)

private theorem decodeCodes_realizable : (decodeCodes element length).Realizable := by
  exact (readCodes_realizable element length).optionalGuard (fun _ _ => True)
    (fun sizes arguments => (codesValid element length).compute sizes ⟨arguments, trivial⟩)
    (fun sizes arguments _ accepted => (codesValid_correct element length sizes arguments).mp accepted)
    (codesValid_realizable element length)

private theorem decode_blocks (sizes : Parameter → ℕ)
    (blocks : (codeArray element length).Carrier sizes)
    (values : (decodedArray element length).Carrier sizes) :
    (decodedArray element length).decode sizes ((codeArray element length).encode sizes blocks) = some values ↔
      ∀ index, element.decode Empty.elim (blocks index) = some (values index) := by
  simp only [decodedArray, codeArray, arrayOfLength, ofCodec, BitVec.cast_cast, BitVec.cast_eq]
  rw [ArrayEncoding.decode_encoded_iff]
  apply forall_congr'
  intro index
  simp [valueBits, EncodedDomain.constant, bitVectors, ofCodec]

private theorem decodeCodes_correct (sizes : Parameter → ℕ)
    (blocks : (codeArray element length).Carrier sizes) :
    (decodeCodes element length).compute sizes ⟨(fun _ => blocks), trivial⟩ =
      (decodedArray element length).decode sizes ((codeArray element length).encode sizes blocks) := by
  classical
  apply Option.ext
  intro values
  rw [decode_blocks]
  dsimp only [decodeCodes, optionalGuard]
  split
  · next accepted =>
    simp only [Option.some.injEq]
    constructor
    · intro equal
      subst values
      intro index
      exact (Option.some_get _).symm
    · intro entries
      funext index
      exact Option.some.inj ((Option.some_get _).trans (entries index))
  · next rejected =>
    simp only [reduceCtorEq, false_iff]
    intro entries
    apply rejected
    apply (codesValid_correct element length sizes (fun _ => blocks)).mpr
    intro index
    rw [entries index]
    rfl

end FixedArrayDecode

variable {Parameter : Type} [Fintype Parameter]

/-- Canonical exact-width array decoding over a fixed scalar codec. Its
realization validates all scalar blocks, including unused finite-carrier codes. -/
noncomputable def decodeFixedArray (element : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  decodeCanonicalBits (element.constant.arrayOfLength length)

theorem decodeFixedArray_realizable (element : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) : (decodeFixedArray element length).Realizable := by
  have ready := (FixedArrayDecode.bitBlocks_realizable element length).followedBy
    (FixedArrayDecode.decodeCodes_realizable element length) rfl (by intros; trivial)
  apply ready.withSpecification (fun _ _ => True) (decodeFixedArray element length).compute (by intros; trivial)
  intro sizes arguments valid
  let blocks := (FixedArrayDecode.bitBlocks element length).compute sizes ⟨arguments, trivial⟩
  have correct := FixedArrayDecode.decodeCodes_correct element length sizes blocks
  have framed := FixedArrayDecode.bitBlocks_correct element length sizes (arguments ())
  change (FixedArrayDecode.decodeCodes element length).compute sizes ⟨(fun _ => blocks), trivial⟩ = _
  rw [correct]
  change (element.constant.arrayOfLength length).decode sizes
    ((FixedArrayDecode.codeArray element length).encode sizes blocks) = _
  rw [framed]
  rfl

/-- The certified array decoder agrees with canonical decoding on every exact
bit pattern. This equation is also the interface for stored-field decoders. -/
theorem decodeFixedArray_correct (element : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (bits : BitVec ((element.constant.arrayOfLength length).width sizes)) :
    (decodeFixedArray element length).compute sizes ⟨(fun _ => bits), trivial⟩ =
      (element.constant.arrayOfLength length).decode sizes bits := rfl

/-- Canonical arrays round-trip through the certified decoder. -/
theorem decodeFixedArray_roundtrip (element : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (values : (element.constant.arrayOfLength length).Carrier sizes) :
    (decodeFixedArray element length).compute sizes
      ⟨(fun _ => (element.constant.arrayOfLength length).encode sizes values), trivial⟩ = some values :=
  (element.constant.arrayOfLength length).decode_encode sizes values

/-- Successful decoding characterizes exactly the canonical input pattern. -/
theorem decodeFixedArray_some_iff (element : EncodedDomain Empty)
    (length : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (bits : BitVec ((element.constant.arrayOfLength length).width sizes))
    (values : (element.constant.arrayOfLength length).Carrier sizes) :
    (decodeFixedArray element length).compute sizes ⟨(fun _ => bits), trivial⟩ = some values ↔
      (element.constant.arrayOfLength length).encode sizes values = bits := by
  constructor
  · exact (element.constant.arrayOfLength length).encode_decode sizes bits values
  · intro canonical
    rw [← canonical]
    exact decodeFixedArray_roundtrip element length sizes values

/-- Named-coordinate arrays reuse polynomial-length decoding through the
existing carrier equivalence; no extra decoder or scalar validation is needed. -/
theorem decodeFixedNamedArray_realizable (element : EncodedDomain Empty) (parameter : Parameter) :
    (decodeCanonicalBits (element.constant.array parameter)).Realizable :=
  decodeCanonicalBits_reindex _ _ _ (decodeFixedArray_realizable element (MvPolynomial.X parameter))

end Polytime2.Computation
