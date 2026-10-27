import Polytime2.Complexity.WordArrays
import Polytime2.Arrays.AllTrue
import Polytime2.Arrays.FixedArrayResult
import Polytime2.Computation.Optional
import Polytime2.Encoding.Word

/-! # Total decoding of binary word fields

Every nonbinary letter rejects. Successful output contains exactly the actual
bits, with no padding or default data. The empty field decodes to an empty bit
array. Width checks and domain-specific code validation are separate steps.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation
open EncodedDomain.Internal (letterBit isBinaryLetter)

private noncomputable def bitArray : Computation Unit Unit :=
  mapArray letterDomain booleans (MvPolynomial.X ()) (fun _ letter => letterBit letter)

private theorem bitArray_realizable : bitArray.Realizable :=
  mapArray_realizable letterDomain booleans (MvPolynomial.X ()) (fun _ letter => letterBit letter)
    (letterTest_realizable letterBit)

private theorem binaryGuard_realizable :
    (Computation.mk bitArray.inputDomains booleans (fun _ _ => True)
      (fun _ arguments => (List.ofFn (arguments.val ())).all isBinaryLetter)).Realizable := by
  have flags := mapArray_realizable letterDomain booleans (MvPolynomial.X ())
    (fun _ letter => isBinaryLetter letter) (letterTest_realizable isBinaryLetter)
  have checked := flags.followedBy (arrayAllTrue_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
  apply checked.withSpecification (fun _ _ => True) _ (by intros; trivial)
  intro sizes arguments valid
  change (List.ofFn (fun index => isBinaryLetter (arguments () index))).all id = _
  rw [List.ofFn_comp' (arguments ()) isBinaryLetter]
  simp only [List.all_map, Function.comp_def, id_eq]

/-- Decode a binary field, rejecting any nonbinary letter before returning bits. -/
noncomputable def binaryWordDecoder : Computation Unit Unit :=
  bitArray.optionalGuard (fun _ _ => True)
    (fun _ arguments => (List.ofFn (arguments ())).all isBinaryLetter) (by intros; trivial)

theorem binaryWordDecoder_realizable : binaryWordDecoder.Realizable :=
  bitArray_realizable.optionalGuard (fun _ _ => True)
    (fun _ arguments => (List.ofFn (arguments ())).all isBinaryLetter)
    (by intros; trivial) binaryGuard_realizable

/-- Acceptance, rejection, and returned bits agree with strict binary decoding. -/
theorem binaryWordDecoder_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (binaryWordDecoder.compute sizes ⟨(fun _ => letters), trivial⟩).map List.ofFn =
      decodeBinaryWord (List.ofFn letters) := by
  have mapped : List.ofFn (fun index => letterBit (letters index)) = (List.ofFn letters).map letterBit := by
    rw [List.map_ofFn]
    rfl
  rw [decodeBinaryWord_eq_all]
  dsimp only [binaryWordDecoder, optionalGuard, bitArray, mapArray]
  split_ifs with accepted
  · simp only [Option.map_some]
    exact congrArg some mapped
  · rfl

private noncomputable def storedBooleanElement : EncodedDomain Empty := booleans

private noncomputable def namedBits : Computation Unit Unit :=
  bitArray.reinterpretOutput ((storedBooleanElement.constant : EncodedDomain Unit).array ())
    (fun sizes => (arrayParameterEquiv booleans () sizes).symm)

private theorem namedBits_realizable : namedBits.Realizable := by
  apply bitArray_realizable.reinterpretOutput
  · intro sizes
    have clog : Nat.clog 2 2 = 1 := by decide
    simp [bitArray, storedBooleanElement, width, booleans, clog, mapArray]
  · intro sizes values
    have converted : ArrayEncoding.bits (((storedBooleanElement.constant : EncodedDomain Unit).array ()).encode sizes
        ((arrayParameterEquiv booleans () sizes).symm values)) =
        ArrayEncoding.bits (((booleans : EncodedDomain Unit).array ()).encode sizes
          ((arrayParameterEquiv booleans () sizes).symm values)) := by
      rw [array_encode_bits, array_encode_bits]
      simp only [ArrayEncoding.bits_encode, storedBooleanElement, constant_encode_bits, booleans, fixed_encode_bits]
    rw [converted]
    exact array_X_encode_bits booleans () sizes _

private noncomputable def binaryParts : Computation Unit Unit where
  inputDomains := bitArray.inputDomains
  outputDomain := booleans.prod namedBits.outputDomain
  precondition _ _ := True
  compute sizes arguments := ((List.ofFn (arguments.val ())).all isBinaryLetter, namedBits.compute sizes arguments)

private theorem binaryParts_realizable : binaryParts.Realizable :=
  binaryGuard_realizable.prodMk namedBits_realizable

private noncomputable def namedParts : Computation Unit Unit :=
  binaryParts.reinterpretInputs (fun _ : Unit => letterDomain.array ())
    (fun _ sizes => arrayParameterEquiv letterDomain () sizes) (fun _ _ => True) (by intros; trivial)

private theorem namedParts_realizable : namedParts.Realizable :=
  binaryParts_realizable.reinterpretInputs (fun _ : Unit => letterDomain.array ())
    (fun _ sizes => arrayParameterEquiv letterDomain () sizes)
    (by intros; rfl) (fun _ sizes values => array_X_encode_bits letterDomain () sizes values)
    (fun _ _ => True) (by intros; trivial)

section StoredFields

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def storedBinaryParts (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (callFixedArray (fixed (Fintype.equivFin Letter)) capacity namedParts rfl (by intros; trivial)).followedBy
    (retainFixedArrayFlag storedBooleanElement capacity) rfl (by intros; trivial)

private theorem storedBinaryParts_realizable (capacity : MvPolynomial Parameter ℕ) :
    (storedBinaryParts capacity).Realizable :=
  (namedParts_realizable.callFixedArray (fixed (Fintype.equivFin Letter)) capacity
    rfl (by intros; trivial)).followedBy
      (retainFixedArrayFlag_realizable storedBooleanElement capacity) rfl (by intros; trivial)

private noncomputable def selectStoredBits (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  unaryMap (storedBinaryParts capacity).outputDomain
    (optional (boundedArray (storedBooleanElement.constant : EncodedDomain Parameter) capacity))
    (fun _ _ => True) (fun _ parts => if (show Bool from parts.val.1) then some parts.val.2 else none)

private theorem selectStoredBits_realizable (capacity : MvPolynomial Parameter ℕ) :
    (selectStoredBits capacity).Realizable := by
  let packed := boundedArray (storedBooleanElement.constant : EncodedDomain Parameter) capacity
  exact (optionalWhen_realizable packed).onResults (selectStoredBits capacity).inputDomains (fun _ _ => True)
    (fun choice _ arguments => match choice with | false => (arguments.val ()).1 | true => (arguments.val ()).2)
    (by intros; trivial) (by
      intro choice
      cases choice
      · exact pairProjection_realizable booleans packed false
      · exact pairProjection_realizable booleans packed true)

/-- Strictly decode a stored word to an optional Boolean field with the same
actual count. Nonbinary symbols reject; padding remains internal. -/
noncomputable def storedBinaryWordDecoder (capacity : MvPolynomial Parameter ℕ) : Computation Parameter Unit :=
  (storedBinaryParts capacity).followedBy (selectStoredBits capacity) rfl (by intros; trivial)

theorem storedBinaryWordDecoder_realizable (capacity : MvPolynomial Parameter ℕ) :
    (storedBinaryWordDecoder capacity).Realizable :=
  (storedBinaryParts_realizable capacity).followedBy (selectStoredBits_realizable capacity) rfl (by intros; trivial)

private theorem storedBinaryParts_correct (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant) capacity).Carrier sizes) :
    (storedBinaryParts capacity).compute sizes ⟨(fun _ => field), trivial⟩ =
      ((List.ofFn field.2).all isBinaryLetter,
        ⟨field.1, (fun index => letterBit (field.2 index))⟩) := by
  let actual : Unit → ℕ := fun _ => field.1.val
  have sameLetters : List.ofFn (arrayParameterEquiv letterDomain () actual field.2) = List.ofFn field.2 :=
    (List.ofFn_congr (MvPolynomial.eval_X (f := actual) ()).symm field.2).symm
  apply Prod.ext
  · change (List.ofFn (arrayParameterEquiv letterDomain () actual field.2)).all isBinaryLetter = _
    rw [sameLetters]
  · apply Sigma.ext rfl
    apply heq_of_eq
    funext index
    apply congrArg letterBit
    apply congrArg field.2
    apply Fin.ext
    rfl

/-- The strict stored-field decoder agrees with binary word decoding for all
field contents, including empty fields and malformed letters. -/
theorem storedBinaryWordDecoder_correct (capacity : MvPolynomial Parameter ℕ) (sizes : Parameter → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant) capacity).Carrier sizes) :
    ((storedBinaryWordDecoder capacity).compute sizes ⟨(fun _ => field), trivial⟩).map
      (fun result => List.ofFn result.2) = decodeBinaryWord (List.ofFn field.2) := by
  change ((selectStoredBits capacity).compute sizes
    ⟨(fun _ => (storedBinaryParts capacity).compute sizes ⟨(fun _ => field), trivial⟩), trivial⟩).map _ = _
  rw [storedBinaryParts_correct capacity, decodeBinaryWord_eq_all]
  dsimp only [selectStoredBits, unaryMap]
  split_ifs with accepted
  · simp only [Option.map_some]
    congr 1
    rw [List.map_ofFn]
    rfl
  · rfl

end StoredFields

end Polytime2.Complexity
