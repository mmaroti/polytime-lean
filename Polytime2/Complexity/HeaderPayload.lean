import Polytime2.Complexity.HeaderParser
import Polytime2.Arrays.Capacity

/-! # Strict header parsing with an exact retained suffix

Drop the parsed count only after validating the header. The returned bounded
array consists exactly of the remaining letters, including an empty suffix.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def payloadField : EncodedDomain Unit :=
  boundedArray letterDomain (MvPolynomial.X ())

private noncomputable def parsedHeader : EncodedDomain Unit :=
  (boundedIndex (MvPolynomial.X () + 1)).prod payloadField

private noncomputable def suffixConsumer : Computation Unit Unit :=
  optionalElim parsedHeader (optional payloadField) (fun _ => none) (fun _ parsed => some parsed.2)

private theorem suffixConsumer_realizable : suffixConsumer.Realizable := by
  have selected := (pairProjection_realizable (boundedIndex (MvPolynomial.X () + 1)) payloadField true).followedBy
    (optionalSome_realizable payloadField) rfl (by intros; trivial)
  exact optionalElim_realizable parsedHeader (optional payloadField) (fun _ => none)
    (fun _ parsed => some parsed.2) (optionalNone_realizable payloadField) selected

/-- Parse a header and return precisely its suffix, rejecting malformed headers. -/
noncomputable def headerPayloadParser : Computation Unit Unit :=
  headerParser.followedBy suffixConsumer rfl (by intros; trivial)

theorem headerPayloadParser_realizable : headerPayloadParser.Realizable :=
  headerParser_realizable.followedBy suffixConsumer_realizable rfl (by intros; trivial)

/-- Dropping the count preserves the exact mathematical parse result. -/
theorem headerPayloadParser_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (headerPayloadParser.compute sizes ⟨(fun _ => letters), trivial⟩).map
      (fun field => List.ofFn field.2) = (readPairHeader (List.ofFn letters)).map Prod.snd := by
  let parsed := headerParser.compute sizes ⟨(fun _ => letters), trivial⟩
  have projected : headerPayloadParser.compute sizes ⟨(fun _ => letters), trivial⟩ = parsed.map Prod.snd := by
    change parsed.elim none (fun result => some result.2) = parsed.map Prod.snd
    cases parsed <;> rfl
  rw [projected, Option.map_map]
  rw [← headerParser_correct sizes letters, Option.map_map]
  rfl

private noncomputable def suffixAtHost : Computation Bool Unit :=
  ((boundedArrayRename letterDomain (MvPolynomial.X ()) (fun _ : Unit => true)).withPrecondition
    (fun sizes _ => sizes true ≤ sizes false) (by intros; trivial)).followedBy
      (boundedArrayResize (letterDomain.renameParameters (fun _ : Unit => true))
        (MvPolynomial.rename (fun _ : Unit => true) (MvPolynomial.X ())) (MvPolynomial.X false))
      rfl (by
        intro sizes arguments valid
        change sizes true ≤ sizes false at valid
        simpa only [boundedArrayResize, unaryMap, MvPolynomial.eval_rename, MvPolynomial.eval_X,
          Function.comp_apply] using valid)

private theorem suffixAtHost_realizable : suffixAtHost.Realizable :=
  ((boundedArrayRename_realizable letterDomain (MvPolynomial.X ()) (fun _ : Unit => true)).withPrecondition
    (fun sizes _ => sizes true ≤ sizes false) (by intros; trivial)).followedBy
      (boundedArrayResize_realizable (letterDomain.renameParameters (fun _ : Unit => true))
        (MvPolynomial.rename (fun _ : Unit => true) (MvPolynomial.X ())) (MvPolynomial.X false))
      rfl (by
        intro sizes arguments valid
        change sizes true ≤ sizes false at valid
        simpa only [boundedArrayResize, unaryMap, MvPolynomial.eval_rename, MvPolynomial.eval_X,
          Function.comp_apply] using valid)

private noncomputable def selectedSuffix : Computation Bool Unit :=
  ((optionalGet ((payloadField).renameParameters (fun _ : Unit => true))).withPrecondition
    (fun sizes arguments => (arguments ()).isSome = true ∧ sizes true ≤ sizes false)
    (by intro sizes arguments valid; exact valid.1)).followedBy suffixAtHost rfl
      (by intro sizes arguments valid; exact valid.2)

private theorem selectedSuffix_realizable : selectedSuffix.Realizable :=
  ((optionalGet_realizable ((payloadField).renameParameters (fun _ : Unit => true))).withPrecondition
    (fun sizes arguments => (arguments ()).isSome = true ∧ sizes true ≤ sizes false)
    (by intro sizes arguments valid; exact valid.1)).followedBy suffixAtHost_realizable rfl
      (by intro sizes arguments valid; exact valid.2)

/-- Retain an optional parsed suffix at the caller's capacity. Its actual
length and letters are preserved; an absent parse remains absent. -/
noncomputable def retainHeaderSuffix : Computation Bool Unit :=
  selectedSuffix.optionalGuard (fun sizes _ => sizes true ≤ sizes false)
    (fun _ arguments => (arguments ()).isSome)
    (by intro sizes arguments fits present; exact ⟨present, fits⟩)

theorem retainHeaderSuffix_realizable : retainHeaderSuffix.Realizable := by
  have guard := (optionalIsSome_realizable (payloadField.renameParameters (fun _ : Unit => true))).withPrecondition
    (fun sizes _ => sizes true ≤ sizes false) (by intros; trivial)
  exact selectedSuffix_realizable.optionalGuard (fun sizes _ => sizes true ≤ sizes false)
    (fun _ arguments => (arguments ()).isSome)
    (by intro sizes arguments fits present; exact ⟨present, fits⟩) guard

/-- Capacity conversion neither adds letters nor turns a failed parse into a
successful suffix. Only the stored capacity changes. -/
theorem retainHeaderSuffix_correct (sizes : Bool → ℕ)
    (arguments : retainHeaderSuffix.Arguments sizes) (fits : sizes true ≤ sizes false) :
    (retainHeaderSuffix.compute sizes ⟨arguments, fits⟩).map (fun field => List.ofFn field.2) =
      (arguments ()).map (fun field => List.ofFn field.2) := by
  cases chosen : arguments () with
  | none => simp [retainHeaderSuffix, optionalGuard, chosen]
  | some field =>
    have eta : arguments = fun _ => some field := by
      funext name
      cases name
      exact chosen
    subst arguments
    rfl

/-- Parse a field-sized word while retaining its exact suffix at the host
capacity. Empty suffixes are allowed; malformed headers remain rejected. -/
noncomputable def headerPayloadAtHost : Computation Bool Unit :=
  (((headerPayloadParser.renameParameters (fun _ : Unit => true)).withPrecondition
    (fun sizes _ => sizes true ≤ sizes false) (by intros; trivial)).followedBy
      (optionalRename payloadField (fun _ : Unit => true)) rfl (by intros; trivial)).followedBy
        retainHeaderSuffix rfl (by intro sizes arguments valid; exact valid)

theorem headerPayloadAtHost_realizable : headerPayloadAtHost.Realizable :=
  (((headerPayloadParser_realizable.renameParameters (fun _ : Unit => true)).withPrecondition
    (fun sizes _ => sizes true ≤ sizes false) (by intros; trivial)).followedBy
      (optionalRename_realizable payloadField (fun _ : Unit => true)) rfl (by intros; trivial)).followedBy
        retainHeaderSuffix_realizable rfl (by intro sizes arguments valid; exact valid)

/-- Parsing and capacity conversion preserve precisely the actual suffix on
all words, not just successfully parsed inputs. -/
theorem headerPayloadAtHost_correct (sizes : Bool → ℕ)
    (arguments : headerPayloadAtHost.Arguments sizes) (fits : sizes true ≤ sizes false) :
    (headerPayloadAtHost.compute sizes ⟨arguments, fits⟩).map (fun field => List.ofFn field.2) =
      (readPairHeader (List.ofFn (arguments ()))).map Prod.snd := by
  dsimp only [headerPayloadAtHost, followedBy, withPrecondition, Computation.renameParameters,
    optionalRename, encodingMap, unaryMap]
  rw [retainHeaderSuffix_correct]
  exact headerPayloadParser_correct (sizes ∘ (fun _ : Unit => true)) (arguments ())

end Polytime2.Complexity
