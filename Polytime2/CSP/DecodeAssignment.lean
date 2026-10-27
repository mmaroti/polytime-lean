import Polytime2.CSP.Encoding
import Polytime2.Primitives.FiniteOperations
import Polytime2.Arrays.Transform
import Polytime2.Arrays.AllTrue
import Polytime2.Computation.FullCodec
import Polytime2.Computation.Substitution
import Polytime2.Computation.BooleanBits
import Polytime2.Arrays.PackingRead
import Polytime2.Arrays.PackingWidth
import Polytime2.Encoding.Word
import Polytime2.Arrays.BooleanField
import Polytime2.Complexity.BinaryDecoder

/-! # Finite assignment-code validation

Each assignment entry uses the existing fixed-carrier codec. Decoding an
entry returns an actual carrier value or none, including when the carrier is
empty. Guarded array decoding returns actual assignments when all entry codes
are valid. Raw word framing remains separate.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (Carrier : Type) [Fintype Carrier]

private noncomputable def valueBits : EncodedDomain Unit :=
  (bitVectors (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).widthPolynomial).constant

private noncomputable def valueValid : Computation Unit Unit :=
  unaryMap (valueBits Carrier) booleans (fun _ _ => True)
    (fun _ bits => ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim bits.val).isSome)

private theorem valueValid_realizable : (valueValid Carrier).Realizable := by
  let source := bitVectors (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).widthPolynomial
  let test := fun bits => ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim bits).isSome
  have raw := (finitePredicate_realizable source test).withConstantSizes (Parameter := Unit)
  exact raw.reinterpretOutput (booleans : EncodedDomain Unit) (fun _ value => value)
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, booleans, width])
    (by intros; simp [withConstantSizes, finitePredicate, finiteOperation, constant_encode_bits,
      booleans, fixed_encode_bits])

/-- Validate every entry of an exactly framed assignment-code array. No default
value or inhabitance hypothesis is needed, even for a zero-width carrier. -/
noncomputable def assignmentCodesValid : Computation Unit Unit :=
  (mapArray (valueBits Carrier) booleans (MvPolynomial.X ())
    (fun _ bits => ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim bits).isSome)).followedBy
      (arrayAllTrue (MvPolynomial.X ())) rfl (by intros; trivial)

theorem assignmentCodesValid_realizable : (assignmentCodesValid Carrier).Realizable := by
  have mapped := mapArray_realizable (valueBits Carrier) booleans (MvPolynomial.X ())
    (fun _ bits => ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim bits).isSome)
    (valueValid_realizable Carrier)
  exact mapped.followedBy (arrayAllTrue_realizable (MvPolynomial.X ())) rfl (by intros; trivial)

/-- Validation accepts exactly when each canonical scalar decoder succeeds. -/
theorem assignmentCodesValid_correct (sizes : Unit → ℕ)
    (arguments : (assignmentCodesValid Carrier).Arguments sizes) :
    (assignmentCodesValid Carrier).compute sizes ⟨arguments, trivial⟩ = true ↔
      ∀ index, ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
        (arguments () index)).isSome = true := by
  exact arrayAllTrue_correct (MvPolynomial.X ()) sizes _

private noncomputable def codeArray : EncodedDomain Unit :=
  (valueBits Carrier).arrayOfLength (MvPolynomial.X ())

private theorem codeArray_full (sizes : Unit → ℕ) :
    Function.Surjective ((codeArray Carrier).encode sizes) := by
  apply arrayOfLength_encode_surjective
  intro assignment bits
  refine ⟨bits.cast (by simp [valueBits, width, EncodedDomain.constant, bitVectors]), ?_⟩
  simp [valueBits, EncodedDomain.constant, bitVectors, ofCodec]

/-- Frame an exact assignment-width bit vector into all scalar code blocks.
Framing accepts every pattern; validity is checked by the subsequent decoder. -/
noncomputable def assignmentBitBlocks : Computation Unit Unit :=
  decodeFullCodec (codeArray Carrier) (codeArray_full Carrier)

theorem assignmentBitBlocks_realizable : (assignmentBitBlocks Carrier).Realizable :=
  decodeFullCodec_realizable _ _

/-- Framing preserves the exact input bits, including at zero width. -/
theorem assignmentBitBlocks_correct (sizes : Unit → ℕ)
    (bits : BitVec ((codeArray Carrier).width sizes)) :
    (codeArray Carrier).encode sizes
      ((assignmentBitBlocks Carrier).compute sizes ⟨(fun _ => bits), trivial⟩) = bits :=
  (codeArray Carrier).encode_decode sizes bits _
    (decodeFullCodec_correct (codeArray Carrier) (codeArray_full Carrier) sizes bits)

private noncomputable def decodedArray : EncodedDomain Unit :=
  ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).constant : EncodedDomain Unit).arrayOfLength
    (MvPolynomial.X ())

private noncomputable def readCodes : Computation Unit Unit where
  inputDomains _ := codeArray Carrier
  outputDomain := decodedArray Carrier
  precondition _ arguments := ∀ index,
    ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
      (arguments () index)).isSome = true
  compute _ arguments index :=
    ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
      (arguments.val () index)).get (arguments.property index)

private theorem readCodes_realizable : (readCodes Carrier).Realizable := by
  have copied := (copy_realizable (codeArray Carrier)).withPrecondition
    (readCodes Carrier).precondition (by intros; trivial)
  apply copied.withEncodedOutput (decodedArray Carrier) (readCodes Carrier).compute
    (by intro sizes; simp [decodedArray, codeArray, valueBits, width, constant_widthPolynomial,
      copy, withPrecondition])
  intro sizes arguments
  apply congrArg CallingConvention.tape
  change ArrayEncoding.bits ((decodedArray Carrier).encode sizes _) =
    ArrayEncoding.bits ((codeArray Carrier).encode sizes (arguments.val ()))
  simp only [decodedArray, codeArray, arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext index
  change ArrayEncoding.bits (((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).constant).encode sizes _) =
    ArrayEncoding.bits ((valueBits Carrier).encode sizes (arguments.val () index))
  rw [constant_encode_bits]
  have canonical := (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).encode_decode
    Empty.elim (arguments.val () index) _ (Option.some_get (arguments.property index)).symm
  simpa [readCodes, valueBits, constant_encode_bits, bitVectors, ofCodec, ArrayEncoding.bits_cast]
    using congrArg ArrayEncoding.bits canonical

/-- Decode every entry of an exactly framed code array. Invalid entries reject
before the bit-preserving reader runs; successful output contains actual values. -/
noncomputable def decodeAssignmentCodes : Computation Unit Unit :=
  (readCodes Carrier).optionalGuard (fun _ _ => True)
    (fun sizes arguments => (assignmentCodesValid Carrier).compute sizes ⟨arguments, trivial⟩)
    (fun sizes arguments _ accepted => (assignmentCodesValid_correct Carrier sizes arguments).mp accepted)

theorem decodeAssignmentCodes_realizable : (decodeAssignmentCodes Carrier).Realizable := by
  exact (readCodes_realizable Carrier).optionalGuard (fun _ _ => True)
    (fun sizes arguments => (assignmentCodesValid Carrier).compute sizes ⟨arguments, trivial⟩)
    (fun sizes arguments _ accepted => (assignmentCodesValid_correct Carrier sizes arguments).mp accepted)
    (assignmentCodesValid_realizable Carrier)

/-- The total decoder succeeds exactly when all entry codes are valid. -/
theorem decodeAssignmentCodes_isSome (sizes : Unit → ℕ)
    (arguments : (decodeAssignmentCodes Carrier).Arguments sizes) :
    ((decodeAssignmentCodes Carrier).compute sizes ⟨arguments, trivial⟩).isSome = true ↔
      ∀ index, ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
        (arguments () index)).isSome = true := by
  classical
  simp only [decodeAssignmentCodes, optionalGuard]
  split
  · next accepted => exact iff_of_true rfl ((assignmentCodesValid_correct Carrier sizes arguments).mp accepted)
  · next rejected =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact fun valid => rejected ((assignmentCodesValid_correct Carrier sizes arguments).mpr valid)

/-- Every returned value decodes the corresponding input block. -/
theorem decodeAssignmentCodes_some (sizes : Unit → ℕ)
    (arguments : (decodeAssignmentCodes Carrier).Arguments sizes)
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier)
    (accepted : (decodeAssignmentCodes Carrier).compute sizes ⟨arguments, trivial⟩ = some values) :
    ∀ index, (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
      (arguments () index) = some (values index) := by
  simp only [decodeAssignmentCodes, optionalGuard] at accepted
  split at accepted
  · next valid =>
      cases Option.some.inj accepted
      intro index
      exact (Option.some_get _).symm
  · cases accepted

/-- Entry-wise canonical decoding is sufficient for the guarded array decoder
to return the specified assignment. -/
theorem decodeAssignmentCodes_of_entries (sizes : Unit → ℕ)
    (arguments : (decodeAssignmentCodes Carrier).Arguments sizes)
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier)
    (entries : ∀ index, (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
      (arguments () index) = some (values index)) :
    (decodeAssignmentCodes Carrier).compute sizes ⟨arguments, trivial⟩ = some values := by
  have valid : (assignmentCodesValid Carrier).compute sizes ⟨arguments, trivial⟩ = true :=
    (assignmentCodesValid_correct Carrier sizes arguments).mpr (by intro index; rw [entries index]; rfl)
  simp only [decodeAssignmentCodes, optionalGuard, dite_eq_left valid]
  apply congrArg some
  funext index
  change ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode Empty.elim
    (arguments () index)).get _ = values index
  exact Option.some.inj ((Option.some_get _).trans (entries index))

/-- Decode an exact-width assignment bit vector, rejecting unused scalar codes.
Raw word symbols and the external field length must be checked separately. -/
noncomputable def decodeAssignmentBits : Computation Unit Unit :=
  (assignmentBitBlocks Carrier).followedBy (decodeAssignmentCodes Carrier) rfl
    (by intros; trivial)

theorem decodeAssignmentBits_realizable : (decodeAssignmentBits Carrier).Realizable :=
  (assignmentBitBlocks_realizable Carrier).followedBy (decodeAssignmentCodes_realizable Carrier)
    rfl (by intros; trivial)

/-- Every returned assignment has exactly the original canonical bits. -/
theorem decodeAssignmentBits_some (sizes : Unit → ℕ)
    (bits : BitVec ((codeArray Carrier).width sizes))
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier)
    (accepted : (decodeAssignmentBits Carrier).compute sizes ⟨(fun _ => bits), trivial⟩ = some values) :
    ArrayEncoding.bits ((decodedArray Carrier).encode sizes values) = ArrayEncoding.bits bits := by
  let blocks := (assignmentBitBlocks Carrier).compute sizes ⟨(fun _ => bits), trivial⟩
  have entries := decodeAssignmentCodes_some Carrier sizes (fun _ => blocks) values accepted
  rw [← assignmentBitBlocks_correct Carrier sizes bits]
  change ArrayEncoding.bits ((decodedArray Carrier).encode sizes values) =
    ArrayEncoding.bits ((codeArray Carrier).encode sizes blocks)
  simp only [decodedArray, codeArray, arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext index
  rw [constant_encode_bits]
  have canonical := (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).encode_decode
    Empty.elim (blocks index) (values index) (entries index)
  simpa [valueBits, EncodedDomain.constant, bitVectors, ofCodec, ArrayEncoding.bits_cast]
    using congrArg ArrayEncoding.bits canonical

private noncomputable def canonicalCodes (sizes : Unit → ℕ)
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier) :
    (codeArray Carrier).Carrier sizes :=
  fun index => (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).encode Empty.elim (values index)

private theorem canonicalCodes_bits (sizes : Unit → ℕ)
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier) :
    ArrayEncoding.bits ((codeArray Carrier).encode sizes (canonicalCodes Carrier sizes values)) =
      ArrayEncoding.bits ((decodedArray Carrier).encode sizes values) := by
  simp only [codeArray, decodedArray, arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext index
  simp [canonicalCodes, valueBits, constant_encode_bits, bitVectors]

/-- Canonical entry encodings always decode back to the whole assignment. -/
theorem decodeAssignmentBits_roundtrip (sizes : Unit → ℕ)
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier) :
    (decodeAssignmentBits Carrier).compute sizes
      ⟨(fun _ => (codeArray Carrier).encode sizes (canonicalCodes Carrier sizes values)), trivial⟩ =
      some values := by
  have unpacked := (codeArray Carrier).encode_injective sizes
    (assignmentBitBlocks_correct Carrier sizes
      ((codeArray Carrier).encode sizes (canonicalCodes Carrier sizes values)))
  change (decodeAssignmentCodes Carrier).compute sizes
    ⟨(fun _ => (assignmentBitBlocks Carrier).compute sizes
      ⟨(fun _ => (codeArray Carrier).encode sizes (canonicalCodes Carrier sizes values)), trivial⟩), trivial⟩ = _
  rw [unpacked]
  apply decodeAssignmentCodes_of_entries
  intro index
  exact (fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).decode_encode Empty.elim (values index)

/-- Exact-width decoding accepts precisely the canonical bits of its result.
This covers unused entry codes as well as valid assignments. -/
theorem decodeAssignmentBits_some_iff (sizes : Unit → ℕ)
    (bits : BitVec ((codeArray Carrier).width sizes))
    (values : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Carrier) :
    (decodeAssignmentBits Carrier).compute sizes ⟨(fun _ => bits), trivial⟩ = some values ↔
      ArrayEncoding.bits bits = ArrayEncoding.bits ((decodedArray Carrier).encode sizes values) := by
  constructor
  · intro accepted
    exact (decodeAssignmentBits_some Carrier sizes bits values accepted).symm
  · intro canonical
    have same : bits = (codeArray Carrier).encode sizes (canonicalCodes Carrier sizes values) :=
      ArrayEncoding.bits_injective (canonical.trans (canonicalCodes_bits Carrier sizes values).symm)
    rw [same]
    exact decodeAssignmentBits_roundtrip Carrier sizes values

/-- The certified bit decoder agrees with canonical array decoding on every
exact-width pattern, including malformed finite-carrier codes. -/
theorem decodeAssignmentBits_correct (sizes : Unit → ℕ)
    (bits : BitVec ((codeArray Carrier).width sizes)) :
    (decodeAssignmentBits Carrier).compute sizes ⟨(fun _ => bits), trivial⟩ =
      (decodedArray Carrier).decode sizes (bits.cast (by
        simp [codeArray, decodedArray, valueBits, width, constant_widthPolynomial])) := by
  apply Option.ext
  intro values
  rw [decodeAssignmentBits_some_iff]
  constructor
  · intro canonical
    have equal : bits.cast (show (codeArray Carrier).width sizes = (decodedArray Carrier).width sizes by
        simp [codeArray, decodedArray, valueBits, width, constant_widthPolynomial]) =
        (decodedArray Carrier).encode sizes values :=
      ArrayEncoding.bits_injective (by simpa only [ArrayEncoding.bits_cast] using canonical)
    rw [equal]
    exact (decodedArray Carrier).decode_encode sizes values
  · intro decoded
    have canonical := congrArg ArrayEncoding.bits
      ((decodedArray Carrier).encode_decode sizes _ values decoded)
    simpa only [ArrayEncoding.bits_cast] using canonical.symm

private noncomputable def fieldBitDecoder :=
  (decodeAssignmentBits Carrier).substitute (fun _ : Unit => (MvPolynomial.X true : MvPolynomial Bool ℕ))

private noncomputable def fieldBitsDomain : EncodedDomain Bool :=
  bitVectors ((fieldBitDecoder Carrier).inputDomains ()).widthPolynomial

private noncomputable def fieldBitsValue (sizes : Bool → ℕ) (bits : (fieldBitsDomain Carrier).Carrier sizes) :
    ((fieldBitDecoder Carrier).inputDomains ()).Carrier sizes :=
  bits.cast (SizeSubstitution.polynomial_eval (fun _ : Unit => MvPolynomial.X true)
    (codeArray Carrier).widthPolynomial sizes)

private noncomputable def fieldBitReader : Computation Bool Unit :=
  (fieldBitDecoder Carrier).reinterpretInputs (fun _ => fieldBitsDomain Carrier)
    (fun _ sizes => fieldBitsValue Carrier sizes) (fun _ _ => True) (by intros; trivial)

private theorem fieldBitReader_realizable : (fieldBitReader Carrier).Realizable := by
  have ready := (decodeAssignmentBits_realizable Carrier).substitute
    (fun _ : Unit => (MvPolynomial.X true : MvPolynomial Bool ℕ))
  apply ready.reinterpretInputs (fun _ => fieldBitsDomain Carrier)
    (fun _ sizes => fieldBitsValue Carrier sizes) (by intros; rfl) _ (fun _ _ => True)
    (by intros; trivial)
  intro name sizes bits
  cases name
  simp [fieldBitDecoder, fieldBitsDomain, fieldBitsValue, Computation.substitute,
    EncodedDomain.substitute, decodeAssignmentBits, assignmentBitBlocks, decodeFullCodec,
    encodingMap, unaryMap, followedBy, bitVectors, ofCodec]

private noncomputable def readAssignmentBooleans : Computation Bool Unit :=
  boundedArrayAtLength (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) ((fieldBitReader Carrier).inputDomains ()).widthPolynomial booleans
    (fun _ => True) (fun _ _ value => value)

private theorem readAssignmentBooleans_realizable : (readAssignmentBooleans Carrier).Realizable :=
  boundedArrayAtLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) ((fieldBitReader Carrier).inputDomains ()).widthPolynomial booleans
    (fun _ => True) (fun _ _ value => value)
    (by intros; simp only [booleans, fixed_encode_bits])

/-- Read a Boolean witness field of the exact assignment width at the supplied
variable count. Invalid scalar codes return none; mismatching field lengths
must be rejected before this partial reader runs. -/
noncomputable def readAssignmentField : Computation Bool Unit :=
  ((readAssignmentBooleans Carrier).followedBy
    (booleanArrayBits ((fieldBitReader Carrier).inputDomains ()).widthPolynomial)
    rfl (by intros; trivial)).followedBy (fieldBitReader Carrier) rfl (by intros; trivial)

theorem readAssignmentField_realizable : (readAssignmentField Carrier).Realizable :=
  ((readAssignmentBooleans_realizable Carrier).followedBy
    (booleanArrayBits_realizable ((fieldBitReader Carrier).inputDomains ()).widthPolynomial)
    rfl (by intros; trivial)).followedBy (fieldBitReader_realizable Carrier) rfl (by intros; trivial)

/-- The partial field reader requires only the exact mathematical assignment
width; the host capacity does not add an admissibility condition. -/
theorem readAssignmentField_precondition (sizes : Bool → ℕ)
    (arguments : (readAssignmentField Carrier).Arguments sizes) :
    (readAssignmentField Carrier).precondition sizes arguments ↔
      (arguments ()).1.val = sizes true * Nat.clog 2 (Fintype.card Carrier) := by
  change ((arguments ()).1.val = MvPolynomial.eval sizes
    ((fieldBitReader Carrier).inputDomains ()).widthPolynomial ∧ True) ↔ _
  simp only [and_true]
  simp [fieldBitReader, reinterpretInputs, fieldBitsDomain, fieldBitDecoder, Computation.substitute,
    decodeAssignmentBits, assignmentBitBlocks, decodeFullCodec, encodingMap, unaryMap,
    codeArray, valueBits, followedBy, EncodedDomain.substitute, SizeSubstitution.polynomial_eval,
    SizeSubstitution.assignment, width, EncodedDomain.constant, bitVectors]

private theorem readAssignmentField_decodeWord (sizes : Bool → ℕ)
    (arguments : (readAssignmentField Carrier).Arguments sizes)
    (valid : (readAssignmentField Carrier).precondition sizes arguments) :
    (readAssignmentField Carrier).compute sizes ⟨arguments, valid⟩ =
      (decodedArray Carrier).decodeWord
        (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)
        ((List.ofFn (arguments ()).2).map Sum.inl) := by
  let assigned := SizeSubstitution.assignment (fun _ : Unit => (MvPolynomial.X true : MvPolynomial Bool ℕ)) sizes
  let extracted := (readAssignmentBooleans Carrier).compute sizes ⟨arguments, valid⟩
  let bits := (booleanArrayBits ((fieldBitReader Carrier).inputDomains ()).widthPolynomial).compute sizes
    ⟨(fun _ => extracted), trivial⟩
  let input := fieldBitsValue Carrier sizes bits
  have bitsCorrect : ArrayEncoding.bits input = List.ofFn (arguments ()).2 := by
    change ArrayEncoding.bits (bits.cast _) = _
    rw [ArrayEncoding.bits_cast]
    change ArrayEncoding.bits ((booleanArrayBits _).compute sizes ⟨(fun _ => extracted), trivial⟩) = _
    rw [booleanArrayBits_correct]
    change List.ofFn (fun index => (arguments ()).2 (Fin.cast valid.1.symm index)) = _
    exact (List.ofFn_congr valid.1 (arguments ()).2).symm
  change (decodeAssignmentBits Carrier).compute assigned ⟨(fun _ => input), trivial⟩ = _
  apply Option.ext
  intro values
  rw [decodeAssignmentBits_some_iff]
  constructor
  · intro canonical
    have wordEqual : (decodedArray Carrier).word assigned values =
        (List.ofFn (arguments ()).2).map Sum.inl := by
      unfold EncodedDomain.word
      rw [← canonical, bitsCorrect]
    rw [← wordEqual]
    exact (decodedArray Carrier).decodeWord_word assigned values
  · intro decoded
    have canonical := (decodedArray Carrier).word_decodeWord assigned
      ((List.ofFn (arguments ()).2).map Sum.inl) values decoded
    rw [bitsCorrect]
    exact (List.map_injective_iff.mpr Sum.inl_injective canonical).symm

/-- Decode a stored Boolean assignment field. Incorrect lengths and unused
entry codes return none, without requiring an inhabited template carrier. -/
noncomputable def decodeStoredAssignment : Computation Bool Unit where
  inputDomains := (readAssignmentField Carrier).inputDomains
  outputDomain := (readAssignmentField Carrier).outputDomain
  precondition _ _ := True
  compute sizes arguments := if fits : (arguments.val ()).1.val =
      MvPolynomial.eval sizes ((fieldBitReader Carrier).inputDomains ()).widthPolynomial then
    (readAssignmentField Carrier).compute sizes ⟨arguments.val, fits, trivial⟩
    else none

theorem decodeStoredAssignment_realizable : (decodeStoredAssignment Carrier).Realizable := by
  let condition := fun sizes (arguments : (decodeStoredAssignment Carrier).Arguments sizes) =>
    decide ((arguments ()).1.val =
      MvPolynomial.eval sizes ((fieldBitReader Carrier).inputDomains ()).widthPolynomial)
  have guard := boundedArrayHasLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) ((fieldBitReader Carrier).inputDomains ()).widthPolynomial
  apply Realizable.ofCases (computation := decodeStoredAssignment Carrier) condition guard
  · let selected := fun sizes arguments => True ∧ condition sizes arguments = true
    have active := (readAssignmentField_realizable Carrier).withPrecondition selected (by
      intro sizes arguments valid
      exact ⟨of_decide_eq_true valid.2, trivial⟩)
    apply active.withSpecification selected _ (by intros; trivial)
    intro sizes arguments valid
    dsimp only [decodeStoredAssignment]
    rw [dite_eq_left (of_decide_eq_true valid.2)]
    rfl
  · let rejected := fun sizes arguments => True ∧ condition sizes arguments = false
    have absent := (optionalNone_realizable (decodedArray Carrier)).substitute
      (fun _ : Unit => (MvPolynomial.X true : MvPolynomial Bool ℕ))
    have prepared := absent.onResults (readAssignmentField Carrier).inputDomains rejected
      (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
    apply prepared.withSpecification rejected _ (by intros; trivial)
    intro sizes arguments valid
    dsimp only [decodeStoredAssignment]
    rw [dite_eq_right (by
      intro fits
      have accepted : condition sizes arguments = true := decide_eq_true fits
      rw [valid.2] at accepted
      contradiction)]
    rfl

/-- Both truncated and overlong stored witnesses reject before entry decoding. -/
theorem decodeStoredAssignment_wrong_length (sizes : Bool → ℕ)
    (arguments : (decodeStoredAssignment Carrier).Arguments sizes)
    (mismatch : (arguments ()).1.val ≠ sizes true * Nat.clog 2 (Fintype.card Carrier)) :
    (decodeStoredAssignment Carrier).compute sizes ⟨arguments, trivial⟩ = none := by
  have notFits : (arguments ()).1.val ≠
      MvPolynomial.eval sizes ((fieldBitReader Carrier).inputDomains ()).widthPolynomial := by
    intro fits
    exact mismatch ((readAssignmentField_precondition Carrier sizes arguments).mp ⟨fits, trivial⟩)
  dsimp only [decodeStoredAssignment]
  rw [dite_eq_right notFits]

/-- Stored Boolean witness decoding agrees with canonical decoding for every
field length and every scalar code, including empty template carriers. -/
theorem decodeStoredAssignment_correct (sizes : Bool → ℕ)
    (arguments : (decodeStoredAssignment Carrier).Arguments sizes) :
    (decodeStoredAssignment Carrier).compute sizes ⟨arguments, trivial⟩ =
      (decodedArray Carrier).decodeWord
        (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)
        ((List.ofFn (arguments ()).2).map Sum.inl) := by
  dsimp only [decodeStoredAssignment]
  split_ifs with fits
  · exact readAssignmentField_decodeWord Carrier sizes arguments _
  · have mismatch : (arguments ()).1.val ≠ (decodedArray Carrier).width
        (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes) := by
      intro equal
      apply fits
      simpa [fieldBitReader, reinterpretInputs, fieldBitsDomain, fieldBitDecoder, Computation.substitute,
        decodeAssignmentBits, assignmentBitBlocks, decodeFullCodec, encodingMap, unaryMap,
        codeArray, decodedArray, valueBits, followedBy, EncodedDomain.substitute,
        SizeSubstitution.polynomial_eval, SizeSubstitution.assignment, width,
        EncodedDomain.constant, bitVectors] using equal
    rw [EncodedDomain.decodeWord_eq_decodeBinaryWord]
    rw [(decodeBinaryWord_some_iff _ _).mpr rfl]
    change none = if length : (List.ofFn (arguments ()).2).length = _ then _ else none
    rw [dite_eq_right (by simpa only [List.length_ofFn] using mismatch)]

private noncomputable def binaryAssignmentConsumer : Computation Bool Unit :=
  (storedBooleanFieldView false).followedBy (decodeStoredAssignment Carrier) rfl (by intros; trivial)

private theorem binaryAssignmentConsumer_realizable : (binaryAssignmentConsumer Carrier).Realizable :=
  (storedBooleanFieldView_realizable false).followedBy (decodeStoredAssignment_realizable Carrier)
    rfl (by intros; trivial)

/-- Decode a stored witness word at the supplied variable count. Nonbinary
symbols, incorrect lengths, and unused finite-carrier codes all reject. -/
noncomputable def decodeAssignmentWordField : Computation Bool Unit :=
  (Complexity.storedBinaryWordDecoder (MvPolynomial.X false)).followedBy
    (optionalElim (storedBooleanField false) (binaryAssignmentConsumer Carrier).outputDomain
      (fun _ => none) (fun sizes field =>
        (binaryAssignmentConsumer Carrier).compute sizes ⟨(fun _ => field), trivial⟩))
    rfl (by intros; trivial)

theorem decodeAssignmentWordField_realizable : (decodeAssignmentWordField Carrier).Realizable := by
  have absent := (optionalNone_realizable (decodedArray Carrier)).substitute
    (fun _ : Unit => (MvPolynomial.X true : MvPolynomial Bool ℕ))
  have absentReady := absent.onResults (Empty.elim : Empty → EncodedDomain Bool) (fun _ _ => True)
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  have consumer := optionalElim_realizable (storedBooleanField false)
    (binaryAssignmentConsumer Carrier).outputDomain (fun _ => none)
    (fun sizes field => (binaryAssignmentConsumer Carrier).compute sizes ⟨(fun _ => field), trivial⟩)
    absentReady (binaryAssignmentConsumer_realizable Carrier)
  exact (Complexity.storedBinaryWordDecoder_realizable (MvPolynomial.X false)).followedBy
    consumer rfl (by intros; trivial)

/-- The complete stored word decoder agrees with canonical array-word decoding
on every field, including malformed words and empty carriers. -/
theorem decodeAssignmentWordField_correct (sizes : Bool → ℕ)
    (field : (boundedArray
      ((fixed (Fintype.equivFin Complexity.Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X false)).Carrier sizes) :
    (decodeAssignmentWordField Carrier).compute sizes ⟨(fun _ => field), trivial⟩ =
      (decodedArray Carrier).decodeWord
        (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)
        (List.ofFn field.2) := by
  let binary := (Complexity.storedBinaryWordDecoder (MvPolynomial.X false)).compute sizes
    ⟨(fun _ => field), trivial⟩
  have matching := Complexity.storedBinaryWordDecoder_correct (MvPolynomial.X false) sizes field
  change binary.elim none (fun bits => (binaryAssignmentConsumer Carrier).compute sizes
    ⟨(fun _ => bits), trivial⟩) = _
  rw [decodeWord_eq_decodeBinaryWord, ← matching]
  change binary.elim none _ = (binary.map _).bind _
  cases decoded : binary with
  | none => rfl
  | some bits =>
    change (decodeStoredAssignment Carrier).compute sizes
      ⟨(fun _ => renamedBooleanFieldValue false sizes bits), trivial⟩ = _
    rw [decodeStoredAssignment_correct, decodeWord_eq_decodeBinaryWord]
    rw [(decodeBinaryWord_some_iff _ _).mpr rfl]
    rfl

private noncomputable def namedAssignmentValue (sizes : Bool → ℕ)
    (value : (decodedArray Carrier).Carrier
      (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)) :
    Fin (sizes true) → Carrier :=
  fun index => value (Fin.cast (by simp [SizeSubstitution.assignment]) index)

private theorem namedAssignmentValue_bits (sizes : Bool → ℕ)
    (value : (decodedArray Carrier).Carrier
      (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)) :
    ArrayEncoding.bits ((decodedArray Carrier).encode
      (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes) value) =
    ArrayEncoding.bits ((assignmentDomain Carrier).encode (fun _ => sizes true)
      (namedAssignmentValue Carrier sizes value)) := by
  change _ = ArrayEncoding.bits
    ((((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).constant : EncodedDomain Unit).array ()).encode
      (fun _ => sizes true) (namedAssignmentValue Carrier sizes value))
  rw [array_X_encode_bits]
  simp only [decodedArray, arrayOfLength_encode_bits, ArrayEncoding.bits_encode, constant_encode_bits]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp [SizeSubstitution.assignment]
  · intro index firstBound secondBound
    simp only [List.getElem_ofFn]
    change ArrayEncoding.bits ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).encode Empty.elim
      (value _)) = ArrayEncoding.bits ((fixed (Fintype.equivFin Carrier) : EncodedDomain Empty).encode Empty.elim
      (value _))
    congr 2

private noncomputable def namedAssignmentOutput : EncodedDomain Bool :=
  (optional (assignmentDomain Carrier)).renameParameters (fun _ : Unit => true)

private theorem namedAssignmentOutput_bits (sizes : Bool → ℕ)
    (value : (decodeAssignmentWordField Carrier).outputDomain.Carrier sizes) :
    ArrayEncoding.bits ((namedAssignmentOutput Carrier).encode sizes
      (value.map (namedAssignmentValue Carrier sizes))) =
      ArrayEncoding.bits ((decodeAssignmentWordField Carrier).outputDomain.encode sizes value) := by
  change ArrayEncoding.bits (((optional (assignmentDomain Carrier)).renameParameters
    (fun _ : Unit => true)).encode sizes _) =
      ArrayEncoding.bits (((optional (decodedArray Carrier)).substitute
        (fun _ : Unit => MvPolynomial.X true)).encode sizes value)
  rw [renameParameters_bits, substitute_encode_bits]
  exact (optional_encode_bits_congr (decodedArray Carrier) (assignmentDomain Carrier)
    (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes)
    (fun _ => sizes true) (namedAssignmentValue Carrier sizes)
    (by simp [decodedArray, assignmentDomain, width, SizeSubstitution.assignment])
    (namedAssignmentValue_bits Carrier sizes) value).symm

/-- Decode a stored witness to the canonical named assignment domain consumed
by the CSP checker. All malformed fields reject. -/
noncomputable def decodeAssignmentWitnessField : Computation Bool Unit :=
  (decodeAssignmentWordField Carrier).reinterpretOutput (namedAssignmentOutput Carrier)
    (fun sizes value => value.map (namedAssignmentValue Carrier sizes))

theorem decodeAssignmentWitnessField_realizable : (decodeAssignmentWitnessField Carrier).Realizable := by
  apply (decodeAssignmentWordField_realizable Carrier).reinterpretOutput
    (namedAssignmentOutput Carrier) (fun sizes value => value.map (namedAssignmentValue Carrier sizes))
  · intro sizes
    have lengths := congrArg List.length (namedAssignmentOutput_bits Carrier sizes none)
    simpa only [ArrayEncoding.bits, List.length_ofFn] using lengths
  · exact namedAssignmentOutput_bits Carrier

/-- The named witness decoder agrees with the exact assignment codec used by
the CSP checker on every stored word, including all decoding failures. -/
theorem decodeAssignmentWitnessField_correct (sizes : Bool → ℕ)
    (field : (boundedArray
      ((fixed (Fintype.equivFin Complexity.Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X false)).Carrier sizes) :
    (decodeAssignmentWitnessField Carrier).compute sizes ⟨(fun _ => field), trivial⟩ =
      (assignmentDomain Carrier).decodeWord (fun _ => sizes true) (List.ofFn field.2) := by
  change ((decodeAssignmentWordField Carrier).compute sizes ⟨(fun _ => field), trivial⟩).map
    (namedAssignmentValue Carrier sizes) = _
  rw [decodeAssignmentWordField_correct]
  apply Option.ext
  intro values
  rw [Option.map_eq_some_iff, decodeWord_eq_some_iff]
  constructor
  · rintro ⟨array, decoded, matching⟩
    rw [decodeWord_eq_some_iff] at decoded
    rw [← matching]
    have bits := congrArg (List.map (Sum.inl : Bool → Complexity.Letter))
      (namedAssignmentValue_bits Carrier sizes array)
    exact bits.symm.trans decoded
  · intro canonical
    let array : (decodedArray Carrier).Carrier
        (SizeSubstitution.assignment (fun _ : Unit => MvPolynomial.X true) sizes) :=
      fun index => values (Fin.cast (by simp [SizeSubstitution.assignment]) index)
    have matching : namedAssignmentValue Carrier sizes array = values := by
      funext index
      rfl
    refine ⟨array, ?_, matching⟩
    rw [decodeWord_eq_some_iff]
    have bits := congrArg (List.map (Sum.inl : Bool → Complexity.Letter))
      (namedAssignmentValue_bits Carrier sizes array)
    exact bits.trans (by simpa only [matching, EncodedDomain.word] using canonical)

end Polytime2.CSP
