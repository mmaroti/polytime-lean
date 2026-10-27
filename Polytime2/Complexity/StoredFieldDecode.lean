import Polytime2.Computation.CodecDecode
import Polytime2.Computation.BooleanBits
import Polytime2.Arrays.BooleanField
import Polytime2.Arrays.PackingWidth
import Polytime2.Complexity.BinaryDecoder

/-! # Canonical decoding of stored fields

The target is an ordinary encoded mathematical domain. A caller supplies a
certificate for its exact-width decoder; binary-letter validation, exact-width
checking, and extraction are shared. Every malformed field returns none.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Computation

open EncodedDomain Complexity

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def fieldBooleans (domain : EncodedDomain Parameter) (host : Parameter) :
    Computation Parameter Unit :=
  boundedArrayAtLength (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => host) domain.widthPolynomial booleans (fun _ => True) (fun _ _ value => value)

private theorem fieldBooleans_realizable (domain : EncodedDomain Parameter) (host : Parameter) :
    (fieldBooleans domain host).Realizable :=
  boundedArrayAtLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => host) domain.widthPolynomial booleans (fun _ => True) (fun _ _ value => value)
    (by intros; simp only [booleans, fixed_encode_bits])

/-- Read exactly the target's mathematical bit width. The sole precondition is
that the stored field has that length; capacity padding is never returned. -/
noncomputable def readStoredBits (domain : EncodedDomain Parameter) (host : Parameter) :
    Computation Parameter Unit :=
  (((storedBooleanFieldView host).withPrecondition
    (fun sizes arguments => (arguments ()).1.val = domain.width sizes) (by intros; trivial)).followedBy
      (fieldBooleans domain host) rfl (by intro sizes arguments valid; exact ⟨valid, trivial⟩)).followedBy
        (booleanArrayBits domain.widthPolynomial) rfl (by intros; trivial)

theorem readStoredBits_realizable (domain : EncodedDomain Parameter) (host : Parameter) :
    (readStoredBits domain host).Realizable :=
  (((storedBooleanFieldView_realizable host).withPrecondition
    (fun sizes arguments => (arguments ()).1.val = domain.width sizes) (by intros; trivial)).followedBy
      (fieldBooleans_realizable domain host) rfl (by intro sizes arguments valid; exact ⟨valid, trivial⟩)).followedBy
        (booleanArrayBits_realizable domain.widthPolynomial) rfl (by intros; trivial)

/-- Exact field extraction preserves precisely the actual list of bits. -/
theorem readStoredBits_correct (domain : EncodedDomain Parameter) (host : Parameter)
    (sizes : Parameter → ℕ) (field : (storedBooleanField host).Carrier sizes)
    (valid : field.1.val = domain.width sizes) :
    ArrayEncoding.bits ((readStoredBits domain host).compute sizes ⟨(fun _ => field), valid⟩) =
      List.ofFn field.2 := by
  change ArrayEncoding.bits ((booleanArrayBits domain.widthPolynomial).compute sizes
    ⟨(fun _ index => field.2 (Fin.cast valid.symm index)), trivial⟩) = _
  rw [booleanArrayBits_correct]
  exact (List.ofFn_congr valid field.2).symm

private noncomputable def readDecodedBits (domain : EncodedDomain Parameter) (host : Parameter) :
    Computation Parameter Unit :=
  (readStoredBits domain host).followedBy (decodeCanonicalBits domain) rfl (by intros; trivial)

/-- Decode a stored Boolean field. A failed width guard returns none directly,
so a partial optional-result decoder acquires no additional optional layer. -/
noncomputable def decodeStoredBits (domain : EncodedDomain Parameter) (host : Parameter) :
    Computation Parameter Unit :=
  (readDecodedBits domain host).guarded (fun _ => none) (fun _ _ => True)
    (fun sizes arguments => decide ((arguments ()).1.val = domain.width sizes))
    (fun sizes arguments _ accepted =>
      show (arguments ()).1.val = domain.width sizes from of_decide_eq_true accepted)

theorem decodeStoredBits_realizable (domain : EncodedDomain Parameter) (host : Parameter)
    (decoderReady : (decodeCanonicalBits domain).Realizable) :
    (decodeStoredBits domain host).Realizable := by
  classical
  have readReady := (readStoredBits_realizable domain host).followedBy decoderReady rfl (by intros; trivial)
  have guardReady := (boundedArrayHasLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => host) domain.widthPolynomial).onResults (fun _ => storedBooleanField host)
    (fun _ _ => True) (fun _ sizes arguments => renamedBooleanFieldValue host sizes (arguments.val ()))
    (by intros; trivial) (fun _ => storedBooleanFieldView_realizable host)
  exact readReady.guarded (fun _ => none) (optionalNone_realizable domain) (fun _ _ => True)
    (fun sizes arguments => decide ((arguments ()).1.val = domain.width sizes))
    (fun sizes arguments _ accepted =>
      show (arguments ()).1.val = domain.width sizes from of_decide_eq_true accepted) guardReady

/-- On every stored Boolean field, including every wrong length, certified
field decoding agrees with canonical word decoding. -/
theorem decodeStoredBits_correct (domain : EncodedDomain Parameter) (host : Parameter)
    (sizes : Parameter → ℕ) (field : (storedBooleanField host).Carrier sizes) :
    (decodeStoredBits domain host).compute sizes ⟨(fun _ => field), trivial⟩ =
      domain.decodeWord sizes ((List.ofFn field.2).map Sum.inl) := by
  rw [decodeWord_eq_decodeBinaryWord, (decodeBinaryWord_some_iff _ _).mpr rfl]
  change (if accepted : decide (field.1.val = domain.width sizes) = true then _ else none) =
    (if length : (List.ofFn field.2).length = domain.width sizes then _ else none)
  by_cases fits : field.1.val = domain.width sizes
  · rw [dite_eq_left (decide_eq_true fits), dite_eq_left (by simpa only [List.length_ofFn] using fits)]
    apply congrArg (domain.decode sizes)
    apply ArrayEncoding.bits_injective
    rw [readStoredBits_correct domain host sizes field fits, ArrayEncoding.bits_ofBoolListLE]
  · rw [dite_eq_right (by simpa only [decide_eq_true_eq] using fits),
      dite_eq_right (by simpa only [List.length_ofFn] using fits)]

/-- Decode a stored external word using a supplied canonical exact-width
bit decoder. Nonbinary letters, wrong lengths, and invalid scalar codes reject. -/
noncomputable def decodeStoredWord (domain : EncodedDomain Parameter) (host : Parameter) :
    Computation Parameter Unit :=
  (storedBinaryWordDecoder (MvPolynomial.X host)).followedBy
    (optionalBind (storedBooleanField host) domain
      (fun sizes field => (decodeStoredBits domain host).compute sizes ⟨(fun _ => field), trivial⟩))
    rfl (by intros; trivial)

theorem decodeStoredWord_realizable (domain : EncodedDomain Parameter) (host : Parameter)
    (decoderReady : (decodeCanonicalBits domain).Realizable) :
    (decodeStoredWord domain host).Realizable :=
  (storedBinaryWordDecoder_realizable (MvPolynomial.X host)).followedBy
    (optionalBind_realizable (storedBooleanField host) domain
      (fun sizes field => (decodeStoredBits domain host).compute sizes ⟨(fun _ => field), trivial⟩)
      (decodeStoredBits_realizable domain host decoderReady)) rfl (by intros; trivial)

/-- The complete stored-field decoder has the canonical contract on all words,
not just binary or well-framed fields. -/
theorem decodeStoredWord_correct (domain : EncodedDomain Parameter) (host : Parameter)
    (sizes : Parameter → ℕ)
    (field : (boundedArray ((fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant)
      (MvPolynomial.X host)).Carrier sizes) :
    (decodeStoredWord domain host).compute sizes ⟨(fun _ => field), trivial⟩ =
      domain.decodeWord sizes (List.ofFn field.2) := by
  let binary := (storedBinaryWordDecoder (MvPolynomial.X host)).compute sizes ⟨(fun _ => field), trivial⟩
  have matching := storedBinaryWordDecoder_correct (MvPolynomial.X host) sizes field
  change binary.bind (fun bits => (decodeStoredBits domain host).compute sizes ⟨(fun _ => bits), trivial⟩) = _
  rw [decodeWord_eq_decodeBinaryWord, ← matching]
  change binary.bind _ = (binary.map _).bind _
  cases binary with
  | none => rfl
  | some bits =>
    change (decodeStoredBits domain host).compute sizes ⟨(fun _ => bits), trivial⟩ = _
    rw [decodeStoredBits_correct, decodeWord_eq_decodeBinaryWord]
    rw [(decodeBinaryWord_some_iff _ _).mpr rfl]
    rfl

end Polytime2.Computation
