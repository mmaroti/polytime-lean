import Polytime2.CSP.FieldCheck
import Polytime2.Complexity.StoredHeaderPayload

/-! # Checking an instance word and witness at a supplied variable count

Strict stored-header parsing supplies the instance tables. Both exact word
fields then enter the certified field checker. The caller supplies the count
separately and proves agreement with a successfully parsed instance header.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open EncodedDomain Polytime2.Computation Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]
variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

private noncomputable def hostField : EncodedDomain Unit :=
  boundedArray letterDomain (MvPolynomial.X ())

private noncomputable def nativeField : EncodedDomain Bool :=
  hostField.renameParameters (fun _ : Unit => false)

private noncomputable def directElement : EncodedDomain Bool :=
  (fixed (Fintype.equivFin Letter) : EncodedDomain Empty).constant

private noncomputable def directField : EncodedDomain Bool :=
  boundedArray directElement (MvPolynomial.X false)

private noncomputable def nativeFieldValue (sizes : Bool → ℕ) (field : nativeField.Carrier sizes) :
    directField.Carrier sizes :=
  boundedArrayConvert letterDomain directElement (MvPolynomial.X ()) (MvPolynomial.X false)
    (sizes ∘ (fun _ : Unit => false)) sizes (by simp) (fun value => value) field

private noncomputable def nativeChecker : Computation Bool Bool :=
  (fieldChecker L Carrier).reinterpretInputs (fun _ => nativeField)
    (fun _ sizes => nativeFieldValue sizes) (fun _ _ => True) (by intros; trivial)

private theorem nativeChecker_realizable : (nativeChecker L Carrier).Realizable := by
  apply (fieldChecker_realizable L Carrier).reinterpretInputs (fun _ => nativeField)
    (fun _ sizes => nativeFieldValue sizes) _ _ (fun _ _ => True) (by intros; trivial)
  · intro name sizes
    change nativeField.width sizes = directField.width sizes
    simp [nativeField, hostField, directField, directElement, width, boundedArray, boundedUnary,
      ofBoundedCodec, renameParameters_widthPolynomial, letterDomain]
  · intro name sizes field
    change ArrayEncoding.bits ((hostField.renameParameters (fun _ : Unit => false)).encode sizes field) =
      ArrayEncoding.bits (directField.encode sizes (nativeFieldValue sizes field))
    rw [renameParameters_bits]
    exact boundedArrayConvert_bits letterDomain directElement (MvPolynomial.X ()) (MvPolynomial.X false)
      (sizes ∘ (fun _ : Unit => false)) sizes (by simp) (fun value => value)
      (by simp [width, letterDomain, directElement])
      (by intro value; simp [letterDomain, directElement, constant_encode_bits]) field

private theorem nativeChecker_correct (sizes : Bool → ℕ) (arguments : (nativeChecker L Carrier).Arguments sizes) :
    (nativeChecker L Carrier).compute sizes ⟨arguments, trivial⟩ =
      tableWordVerifier L Carrier (sizes true) (List.ofFn (arguments false).2) (List.ofFn (arguments true).2) :=
  fieldChecker_correct L Carrier sizes (fun choice => nativeFieldValue sizes (arguments choice))

private noncomputable def instancePayload : Computation Bool Unit :=
  (storedHeaderPayload.renameParameters (fun _ : Unit => false)).followedBy
    (optionalRename hostField (fun _ : Unit => false)) rfl (by intros; trivial)

private theorem instancePayload_realizable : instancePayload.Realizable :=
  (storedHeaderPayload_realizable.renameParameters (fun _ : Unit => false)).followedBy
    (optionalRename_realizable hostField (fun _ : Unit => false)) rfl (by intros; trivial)

private theorem instancePayload_correct (sizes : Bool → ℕ) (field : nativeField.Carrier sizes) :
    (instancePayload.compute sizes ⟨(fun _ => field), trivial⟩).map (fun result => List.ofFn result.2) =
      (readPairHeader (List.ofFn field.2)).map Prod.snd :=
  storedHeaderPayload_correct (sizes ∘ (fun _ : Unit => false)) field

private noncomputable def optionalNativeChecker : Computation Bool Bool :=
  optionalDecision (nativeChecker L Carrier).inputDomains
    (fun sizes arguments => (nativeChecker L Carrier).compute sizes ⟨arguments, trivial⟩)

private theorem optionalNativeChecker_realizable : (optionalNativeChecker L Carrier).Realizable :=
  optionalDecision_realizable _ _ (nativeChecker_realizable L Carrier)

private noncomputable def preparedFields (sizes : Bool → ℕ) (arguments : Bool → nativeField.Carrier sizes) :
    (optionalNativeChecker L Carrier).Arguments sizes :=
  fun choice => match choice with
    | false => instancePayload.compute sizes ⟨(fun _ => arguments false), trivial⟩
    | true => some (arguments true)

/-- Check an instance word and witness at a supplied count. Header and field
failures reject before the assignment checker is called. -/
noncomputable def instanceWordChecker : Computation Bool Bool :=
  (optionalNativeChecker L Carrier).onResults (fun _ => nativeField) (fun _ _ => True)
    (fun choice sizes arguments => preparedFields L Carrier sizes arguments.val choice) (by intros; trivial)

theorem instanceWordChecker_realizable : (instanceWordChecker L Carrier).Realizable := by
  apply (optionalNativeChecker_realizable L Carrier).onResults (fun _ => nativeField) (fun _ _ => True)
    (fun choice sizes arguments => preparedFields L Carrier sizes arguments.val choice) (by intros; trivial)
  intro choice
  cases choice
  · exact instancePayload_realizable.onArguments (fun _ : Bool => nativeField) (fun _ _ => True)
      (fun _ => false) (by intros; rfl) (by intros; trivial)
  · exact (optionalSome_realizable nativeField).onArguments (fun _ : Bool => nativeField) (fun _ _ => True)
      (fun _ => true) (by intros; rfl) (by intros; trivial)

/-- Strict header parsing and field checking compose on every input word. The
supplied count is used for decoding; the caller establishes header agreement. -/
theorem instanceWordChecker_correct (sizes : Bool → ℕ)
    (arguments : (instanceWordChecker L Carrier).Arguments sizes) :
    (instanceWordChecker L Carrier).compute sizes ⟨arguments, trivial⟩ =
      (readPairHeader (List.ofFn (arguments false).2)).elim false
        (fun parsed => tableWordVerifier L Carrier (sizes true) parsed.2 (List.ofFn (arguments true).2)) := by
  let parsed := instancePayload.compute sizes ⟨(fun _ => arguments false), trivial⟩
  have decision : (instanceWordChecker L Carrier).compute sizes ⟨arguments, trivial⟩ =
      parsed.elim false (fun field => tableWordVerifier L Carrier (sizes true)
        (List.ofFn field.2) (List.ofFn (arguments true).2)) := by
    change (optionalDecision (nativeChecker L Carrier).inputDomains
      (fun sizes values => (nativeChecker L Carrier).compute sizes ⟨values, trivial⟩)).compute sizes
        ⟨(fun choice => match choice with | false => parsed | true => some (arguments true)), trivial⟩ = _
    cases parsed <;> simp [optionalDecision, Bool.forall_bool, nativeChecker_correct]
  rw [decision]
  have observed := congrArg
    (fun result : Option Word => result.elim false
      (fun tables => tableWordVerifier L Carrier (sizes true) tables (List.ofFn (arguments true).2)))
    (instancePayload_correct sizes (arguments false))
  simpa only [Option.elim_map, Function.comp_def, parsed] using observed

end Polytime2.CSP
