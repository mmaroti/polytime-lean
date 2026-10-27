import Polytime2.CSP.Encoding
import Polytime2.Computation.FullCodec
import Polytime2.Arrays.PackingRead
import Polytime2.Arrays.PackingWidth
import Polytime2.Computation.Optional
import Polytime2.Computation.BooleanBits
import Polytime2.Encoding.Word

/-! # Reading a dense instance from an exact Boolean field

The false size parameter is the host field capacity; the true parameter is
the mathematical variable count. A caller must establish the exact dense
instance width before invoking this partial computation. Reading, Boolean
reinterpretation, and dense decoding use existing composition rules.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

private noncomputable def targetDomain : EncodedDomain Bool :=
  (instanceDomain L).renameParameters (fun _ : Unit => true)

private noncomputable def readBooleans : Computation Bool Unit :=
  boundedArrayAtLength (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) (targetDomain L).widthPolynomial booleans
    (fun _ => True) (fun _ _ value => value)

private theorem readBooleans_realizable : (readBooleans L).Realizable :=
  boundedArrayAtLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) (targetDomain L).widthPolynomial booleans
    (fun _ => True) (fun _ _ value => value)
    (by intros; simp only [booleans, fixed_encode_bits])

/-- Read and decode a Boolean field whose stored length is the exact instance
width at the supplied variable count. Raw letters and mismatching widths must
be rejected by the caller before entering this computation. -/
noncomputable def readDenseInstanceField : Computation Bool Unit :=
  ((readBooleans L).followedBy (booleanArrayBits (targetDomain L).widthPolynomial)
    rfl (by intros; trivial)).followedBy
      (decodeFullCodec (targetDomain L)
        (renameParameters_encode_surjective (instanceDomain L)
          (instanceDomain_encode_surjective L) (fun _ : Unit => true)))
      rfl (by intros; trivial)

theorem readDenseInstanceField_realizable : (readDenseInstanceField L).Realizable :=
  ((readBooleans_realizable L).followedBy (booleanArrayBits_realizable (targetDomain L).widthPolynomial)
    rfl (by intros; trivial)).followedBy
      (decodeFullCodec_realizable (targetDomain L)
        (renameParameters_encode_surjective (instanceDomain L)
          (instanceDomain_encode_surjective L) (fun _ : Unit => true)))
      rfl (by intros; trivial)

/-- The reader's sole mathematical precondition is the exact dense width. -/
theorem readDenseInstanceField_precondition (sizes : Bool → ℕ)
    (arguments : (readDenseInstanceField L).Arguments sizes) :
    (readDenseInstanceField L).precondition sizes arguments ↔
      (arguments ()).1.val = (instanceDomain L).width (fun _ => sizes true) := by
  change ((arguments ()).1.val = (targetDomain L).width sizes ∧ True) ↔ _
  rw [and_true]
  change _ ↔ (arguments ()).1.val = (instanceDomain L).width (sizes ∘ (fun _ : Unit => true))
  rw [← renameParameters_width (instanceDomain L) (fun _ : Unit => true) sizes]
  rfl

/-- The decoded structure's canonical bits are exactly the field's actual bits.
The host capacity and its zero padding are absent from the mathematical result. -/
theorem readDenseInstanceField_bits (sizes : Bool → ℕ)
    (arguments : (readDenseInstanceField L).Arguments sizes)
    (valid : (readDenseInstanceField L).precondition sizes arguments) :
    ArrayEncoding.bits ((instanceDomain L).encode (fun _ => sizes true)
      ((readDenseInstanceField L).compute sizes ⟨arguments, valid⟩)) =
        List.ofFn (arguments ()).2 := by
  let field := arguments ()
  let extracted := (readBooleans L).compute sizes ⟨arguments, valid⟩
  let bits := (booleanArrayBits (targetDomain L).widthPolynomial).compute sizes
    ⟨(fun _ => extracted), trivial⟩
  have canonical := (targetDomain L).encode_decode sizes bits _
    (decodeFullCodec_correct (targetDomain L)
      (renameParameters_encode_surjective (instanceDomain L)
        (instanceDomain_encode_surjective L) (fun _ : Unit => true)) sizes bits)
  change ArrayEncoding.bits ((instanceDomain L).encode (sizes ∘ (fun _ : Unit => true)) _) = _
  rw [← renameParameters_bits (instanceDomain L) (fun _ : Unit => true) sizes]
  change ArrayEncoding.bits ((targetDomain L).encode sizes
    ((decodeFullCodec (targetDomain L)
      (renameParameters_encode_surjective (instanceDomain L)
        (instanceDomain_encode_surjective L) (fun _ : Unit => true))).compute sizes
          ⟨(fun _ => bits), trivial⟩)) = _
  rw [canonical]
  change ArrayEncoding.bits ((booleanArrayBits (targetDomain L).widthPolynomial).compute sizes
    ⟨(fun _ => extracted), trivial⟩) = _
  rw [booleanArrayBits_correct]
  change List.ofFn (fun position => field.2 (Fin.cast valid.1.symm position)) = List.ofFn field.2
  exact (List.ofFn_congr valid.1 field.2).symm

/-- Reading an exact Boolean field agrees with canonical word decoding. -/
theorem readDenseInstanceField_decodeWord (sizes : Bool → ℕ)
    (arguments : (readDenseInstanceField L).Arguments sizes)
    (valid : (readDenseInstanceField L).precondition sizes arguments) :
    (instanceDomain L).decodeWord (fun _ => sizes true)
      ((List.ofFn (arguments ()).2).map Sum.inl) =
        some ((readDenseInstanceField L).compute sizes ⟨arguments, valid⟩) := by
  have canonical : (instanceDomain L).word (fun _ => sizes true)
      ((readDenseInstanceField L).compute sizes ⟨arguments, valid⟩) =
        (List.ofFn (arguments ()).2).map Sum.inl :=
    congrArg (List.map Sum.inl) (readDenseInstanceField_bits L sizes arguments valid)
  rw [← canonical]
  exact (instanceDomain L).decodeWord_word _ _

/-- Decode a stored Boolean instance field, rejecting every mismatching length
before invoking the exact-width reader. This is total on stored Boolean fields. -/
noncomputable def decodeStoredInstance : Computation Bool Unit :=
  (readDenseInstanceField L).optionalGuard (fun _ _ => True)
    (fun sizes arguments => decide ((arguments ()).1.val = MvPolynomial.eval sizes (targetDomain L).widthPolynomial))
    (by
      intro sizes arguments _ accepted
      change (arguments ()).1.val = MvPolynomial.eval sizes (targetDomain L).widthPolynomial ∧ True
      exact ⟨of_decide_eq_true accepted, trivial⟩)

theorem decodeStoredInstance_realizable : (decodeStoredInstance L).Realizable := by
  have guard := boundedArrayHasLength_realizable (booleans : EncodedDomain Unit) (MvPolynomial.X ())
    (fun _ : Unit => false) (targetDomain L).widthPolynomial
  exact (readDenseInstanceField_realizable L).optionalGuard (fun _ _ => True)
    (fun sizes arguments => decide ((arguments ()).1.val = MvPolynomial.eval sizes (targetDomain L).widthPolynomial))
    (by
      intro sizes arguments _ accepted
      change (arguments ()).1.val = MvPolynomial.eval sizes (targetDomain L).widthPolynomial ∧ True
      exact ⟨of_decide_eq_true accepted, trivial⟩) guard

/-- Width validation and extraction together agree with canonical instance
word decoding on every stored Boolean field. -/
theorem decodeStoredInstance_correct (sizes : Bool → ℕ)
    (arguments : (decodeStoredInstance L).Arguments sizes) :
    (decodeStoredInstance L).compute sizes ⟨arguments, trivial⟩ =
      (instanceDomain L).decodeWord (fun _ => sizes true) ((List.ofFn (arguments ()).2).map Sum.inl) := by
  dsimp only [decodeStoredInstance, optionalGuard]
  split_ifs with accepted
  · exact (readDenseInstanceField_decodeWord L sizes arguments _).symm
  · have mismatch : ¬(arguments ()).1.val = (instanceDomain L).width (fun _ => sizes true) := by
      intro equal
      have sameWidth := renameParameters_width (instanceDomain L) (fun _ : Unit => true) sizes
      apply accepted
      apply decide_eq_true
      exact equal.trans sameWidth.symm
    rw [EncodedDomain.decodeWord_eq_decodeBinaryWord]
    rw [(decodeBinaryWord_some_iff _ _).mpr rfl]
    change none = if length : (List.ofFn (arguments ()).2).length =
        (instanceDomain L).width (fun _ => sizes true) then _ else none
    rw [dite_eq_right (by simpa only [List.length_ofFn] using mismatch)]

end Polytime2.CSP
