import Polytime2.Complexity.HeaderPayload
import Polytime2.Arrays.PackingRead
import Polytime2.Computation.ComputedHost

/-! # Header payloads from exact stored word fields

Retain a parser's result in the original host-field codec before returning
from a computed-size call. The actual field length remains internal.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def hostField : EncodedDomain Unit :=
  boundedArray letterDomain (MvPolynomial.X ())

private noncomputable def directHostField : EncodedDomain Bool :=
  boundedArray (letterDomain.renameParameters (fun _ : Unit => true)) (MvPolynomial.X false)

private noncomputable def hostFieldValue (sizes : Bool → ℕ)
    (field : directHostField.Carrier sizes) : hostField.Carrier (sizes ∘ (fun _ : Unit => false)) :=
  boundedArrayConvert (letterDomain.renameParameters (fun _ : Unit => true)) letterDomain
    (MvPolynomial.X false) (MvPolynomial.X ()) sizes (sizes ∘ (fun _ : Unit => false))
    (by simp) (fun value => value) field

private theorem hostFieldValue_bits (sizes : Bool → ℕ) (field : directHostField.Carrier sizes) :
    ArrayEncoding.bits (directHostField.encode sizes field) =
      ArrayEncoding.bits (hostField.encode (sizes ∘ (fun _ : Unit => false)) (hostFieldValue sizes field)) := by
  exact boundedArrayConvert_bits (letterDomain.renameParameters (fun _ : Unit => true)) letterDomain
    (MvPolynomial.X false) (MvPolynomial.X ()) sizes (sizes ∘ (fun _ : Unit => false))
    (by simp) (fun value => value)
    (by simp [width, letterDomain, renameParameters_widthPolynomial])
    (by intro value; simp [renameParameters_bits, letterDomain, constant_encode_bits]) field

private noncomputable def hostOutput : EncodedDomain Bool :=
  (optional hostField).renameParameters (fun _ : Unit => false)

private theorem hostOutput_bits (sizes : Bool → ℕ)
    (value : headerPayloadAtHost.outputDomain.Carrier sizes) :
    ArrayEncoding.bits (hostOutput.encode sizes (value.map (hostFieldValue sizes))) =
      ArrayEncoding.bits (headerPayloadAtHost.outputDomain.encode sizes value) := by
  change ArrayEncoding.bits (((optional hostField).renameParameters (fun _ : Unit => false)).encode sizes _) =
    ArrayEncoding.bits ((optional directHostField).encode sizes value)
  rw [renameParameters_bits]
  exact (optional_encode_bits_congr directHostField hostField sizes (sizes ∘ (fun _ : Unit => false))
    (hostFieldValue sizes)
    (by simp [directHostField, hostField, width, boundedArray, boundedUnary, ofBoundedCodec,
      letterDomain, renameParameters_widthPolynomial])
    (hostFieldValue_bits sizes) value).symm

private noncomputable def parserWithHostOutput : Computation Bool Unit :=
  headerPayloadAtHost.reinterpretOutput hostOutput (fun sizes value => value.map (hostFieldValue sizes))

private theorem parserWithHostOutput_realizable : parserWithHostOutput.Realizable := by
  apply headerPayloadAtHost_realizable.reinterpretOutput hostOutput
    (fun sizes value => value.map (hostFieldValue sizes))
  · intro sizes
    have lengths := congrArg List.length (hostOutput_bits sizes none)
    simpa only [ArrayEncoding.bits, List.length_ofFn] using lengths
  · exact hostOutput_bits

private theorem parserWithHostOutput_correct (sizes : Bool → ℕ)
    (arguments : parserWithHostOutput.Arguments sizes) (fits : sizes true ≤ sizes false) :
    (parserWithHostOutput.compute sizes ⟨arguments, fits⟩).map (fun field => List.ofFn field.2) =
      (readPairHeader (List.ofFn (arguments ()))).map Prod.snd := by
  change ((headerPayloadAtHost.compute sizes ⟨arguments, fits⟩).map (hostFieldValue sizes)).map _ = _
  rw [Option.map_map]
  exact headerPayloadAtHost_correct sizes arguments fits

private def hostNames : Unit → Unit ⊕ Unit := fun _ => .inl ()
private def actualNames : Unit → Unit ⊕ Unit := fun _ => .inr ()
private def parserSizeNames : Bool → Unit ⊕ Unit
  | false => .inl ()
  | true => .inr ()

private noncomputable def parserOnSizes : Computation (Unit ⊕ Unit) Unit :=
  ((parserWithHostOutput.renameParameters parserSizeNames).reinterpretInputs
    (fun _ => (letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters actualNames)
    (fun _ _ value => value) (fun sizes _ => sizes (.inr ()) ≤ sizes (.inl ()))
    (by intros; assumption)).reinterpretOutput ((optional hostField).renameParameters hostNames)
      (fun _ value => value)

private theorem parserOnSizes_realizable : parserOnSizes.Realizable := by
  have prepared := (parserWithHostOutput_realizable.renameParameters parserSizeNames).reinterpretInputs
    (fun _ : Unit => (letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters actualNames)
    (fun _ _ value => value) (by
      intro name sizes
      change ((letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters actualNames).width sizes =
        (((letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters (fun _ : Unit => true)).renameParameters
          parserSizeNames).width sizes
      simp only [renameParameters_width]
      rfl) (by
      intro name sizes value
      change ArrayEncoding.bits (((letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters actualNames).encode sizes value) =
        ArrayEncoding.bits ((((letterDomain.arrayOfLength (MvPolynomial.X ())).renameParameters
          (fun _ : Unit => true)).renameParameters parserSizeNames).encode sizes value)
      rw [renameParameters_bits, renameParameters_bits, renameParameters_bits]
      rfl) (fun sizes _ => sizes (.inr ()) ≤ sizes (.inl ())) (by intros; assumption)
  apply prepared.reinterpretOutput ((optional hostField).renameParameters hostNames) (fun _ value => value)
  · intro sizes
    change ((optional hostField).renameParameters hostNames).width sizes =
      (((optional hostField).renameParameters (fun _ : Unit => false)).renameParameters parserSizeNames).width sizes
    simp only [renameParameters_width]
    rfl
  · intro sizes value
    change ArrayEncoding.bits (((optional hostField).renameParameters hostNames).encode sizes value) =
      ArrayEncoding.bits ((((optional hostField).renameParameters (fun _ : Unit => false)).renameParameters
        parserSizeNames).encode sizes value)
    rw [renameParameters_bits, renameParameters_bits, renameParameters_bits]
    rfl

private theorem parserOnSizes_correct (sizes : (Unit ⊕ Unit) → ℕ)
    (arguments : parserOnSizes.Arguments sizes) (fits : sizes (.inr ()) ≤ sizes (.inl ())) :
    (parserOnSizes.compute sizes ⟨arguments, fits⟩).map (fun field => List.ofFn field.2) =
      (readPairHeader (List.ofFn (arguments ()))).map Prod.snd := by
  exact parserWithHostOutput_correct (sizes ∘ parserSizeNames) arguments fits

private noncomputable def readLetters : Computation (Unit ⊕ Unit) Unit :=
  boundedArrayAtLength letterDomain (MvPolynomial.X ()) hostNames
    (MvPolynomial.rename actualNames (MvPolynomial.X ())) (letterDomain.renameParameters actualNames)
    (fun _ => True) (fun _ _ value => value)

private theorem readLetters_realizable : readLetters.Realizable :=
  boundedArrayAtLength_realizable letterDomain (MvPolynomial.X ()) hostNames
    (MvPolynomial.rename actualNames (MvPolynomial.X ())) (letterDomain.renameParameters actualNames)
    (fun _ => True) (fun _ _ value => value)
    (by intro sizes valid value; simp [renameParameters_bits, letterDomain, constant_encode_bits])

private theorem storedLengthFits (sizes : (Unit ⊕ Unit) → ℕ)
    (arguments : readLetters.Arguments sizes) (valid : readLetters.precondition sizes arguments) :
    sizes (.inr ()) ≤ sizes (.inl ()) := by
  have bound := (arguments ()).1.isLt
  change (arguments ()).1.val < MvPolynomial.eval (sizes ∘ hostNames) (MvPolynomial.X ()) + 1 at bound
  change (arguments ()).1.val = MvPolynomial.eval sizes (MvPolynomial.rename actualNames (MvPolynomial.X ())) ∧ True at valid
  simp only [MvPolynomial.eval_rename, MvPolynomial.eval_X, Function.comp_apply, hostNames, actualNames] at bound valid
  omega

private noncomputable def storedParserCallee : Computation (Unit ⊕ Unit) Unit :=
  (readLetters.followedBy (arrayOfLengthRenameView letterDomain (MvPolynomial.X ()) actualNames)
    rfl (by intros; trivial)).followedBy parserOnSizes rfl storedLengthFits

private theorem storedParserCallee_realizable : storedParserCallee.Realizable :=
  (readLetters_realizable.followedBy
    (arrayOfLengthRenameView_realizable letterDomain (MvPolynomial.X ()) actualNames)
    rfl (by intros; trivial)).followedBy parserOnSizes_realizable rfl storedLengthFits

private theorem storedParserCallee_correct (sizes : (Unit ⊕ Unit) → ℕ)
    (arguments : storedParserCallee.Arguments sizes)
    (valid : storedParserCallee.precondition sizes arguments) :
    (storedParserCallee.compute sizes ⟨arguments, valid⟩).map (fun field => List.ofFn field.2) =
      (readPairHeader (List.ofFn (arguments ()).2)).map Prod.snd := by
  let letters := readLetters.compute sizes ⟨arguments, valid⟩
  let viewed := (arrayOfLengthRenameView letterDomain (MvPolynomial.X ()) actualNames).compute sizes
    ⟨(fun _ => letters), trivial⟩
  change (parserOnSizes.compute sizes ⟨(fun _ => viewed), storedLengthFits sizes arguments valid⟩).map _ = _
  rw [parserOnSizes_correct]
  have length := valid.1.trans (MvPolynomial.eval_rename actualNames sizes (MvPolynomial.X ()))
  have same : List.ofFn viewed = List.ofFn (arguments ()).2 := by
    exact (List.ofFn_congr length (arguments ()).2).symm
  exact congrArg (fun word => (readPairHeader word).map Prod.snd) same

private noncomputable def storedCounts (sizes : Unit → ℕ) (field : hostField.Carrier sizes) :
    (computedSizeDomain (fun _ : Unit => (MvPolynomial.X () : MvPolynomial Unit ℕ))).Carrier sizes :=
  fun _ => (boundedArrayCount letterDomain (MvPolynomial.X ())).compute sizes ⟨(fun _ => field), trivial⟩

private noncomputable def countedParser : Computation Unit Unit :=
  storedParserCallee.atComputedHostSizes (fun _ : Unit => MvPolynomial.X ()) hostField (optional hostField)
    storedCounts (by rfl) (by rfl)

private theorem countedParser_realizable : countedParser.Realizable := by
  apply storedParserCallee_realizable.atComputedHostSizes
  intro name
  exact boundedArrayCount_realizable letterDomain (MvPolynomial.X ())

private theorem countedParser_total (sizes : Unit → ℕ) (arguments : countedParser.Arguments sizes) :
    countedParser.precondition sizes arguments := by
  simp [countedParser, atComputedHostSizes, atComputedHostInput, storedParserCallee, readLetters,
    followedBy, boundedArrayAtLength, unaryMap, computedSizeAssignment, extendedSizeBounds,
    extendedSizeValues, storedCounts, boundedArrayCount, boundedArrayStorage, pairProjection,
    actualNames]

/-- Parse a stored field at its actual length and retain the exact suffix in
its original host codec. Every malformed header returns none. -/
noncomputable def storedHeaderPayload : Computation Unit Unit :=
  countedParser.withPrecondition (fun _ _ => True) (by intro sizes arguments _; exact countedParser_total sizes arguments)

theorem storedHeaderPayload_realizable : storedHeaderPayload.Realizable :=
  countedParser_realizable.withPrecondition (fun _ _ => True)
    (by intro sizes arguments _; exact countedParser_total sizes arguments)

/-- The total stored-field parser agrees with mathematical header decoding on
all exact field contents; neither count storage nor padding adds letters. -/
theorem storedHeaderPayload_correct (sizes : Unit → ℕ)
    (field : (boundedArray letterDomain (MvPolynomial.X ())).Carrier sizes) :
    (storedHeaderPayload.compute sizes ⟨(fun _ => field), trivial⟩).map (fun result => List.ofFn result.2) =
      (readPairHeader (List.ofFn field.2)).map Prod.snd := by
  dsimp only [storedHeaderPayload, withPrecondition, countedParser]
  rw [atComputedHostSizes_compute]
  dsimp only [atComputedHostInput]
  let bounds : Unit → MvPolynomial Unit ℕ := fun _ => MvPolynomial.X ()
  let actual := computedSizeAssignment (extendedSizeBounds bounds) sizes
    (extendedSizeValues bounds sizes (storedCounts sizes field))
  have correct := storedParserCallee_correct actual (fun _ => field)
    (countedParser_total sizes (fun _ => field))
  exact correct

end Polytime2.Complexity
