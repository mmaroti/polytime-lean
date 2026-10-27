import Polytime2.Complexity.WordArrays
import Polytime2.Arrays.FindFalse
import Polytime2.Arrays.NamedTransform

/-! # Certified boundary search for unary word headers

The first non-count letter is returned as an optional coordinate. A missing
boundary rejects at the caller; a found boundary must still be checked for the
separator. This scan is shared by the outer pair and inner CSP instance header.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

/-- Mark the count symbols, before interpreting any header or payload. -/
noncomputable def unaryCountFlags : Computation Unit Unit :=
  mapArray letterDomain booleans (MvPolynomial.X ())
    (fun _ (letter : Letter) => decide (letter = .inr 1))

theorem unaryCountFlags_realizable : unaryCountFlags.Realizable :=
  mapArray_realizable letterDomain booleans (MvPolynomial.X ())
    (fun _ (letter : Letter) => decide (letter = .inr 1))
    (letterTest_realizable (fun letter => decide (letter = .inr 1)))

/-- The actual number of leading count symbols, including the whole word when
no boundary exists. This is an ordinary prefix length, not a search sentinel. -/
noncomputable def unaryPrefixLength : Computation Unit Unit where
  inputDomains := unaryCountFlags.inputDomains
  outputDomain := boundedIndex (MvPolynomial.X () + 1)
  precondition _ _ := True
  compute sizes arguments := by
    let letters : Word := List.ofFn (arguments.val ())
    exact ⟨letters.findIdx (fun letter => decide (letter ≠ .inr 1)), by
      have bound := List.findIdx_le_length (p := fun letter : Letter => decide (letter ≠ .inr 1))
        (xs := letters)
      simp only [letters, List.length_ofFn] at bound
      simp only [map_add, map_one]
      dsimp only [letters]
      omega⟩

theorem unaryPrefixLength_realizable : unaryPrefixLength.Realizable := by
  let predicate : Letter → Bool := fun letter => decide (letter = .inr 1)
  let counted := unaryCountFlags.followedBy (firstFalse (MvPolynomial.X ())) rfl (by intros; trivial)
  have countedReady : counted.Realizable := unaryCountFlags_realizable.followedBy
    (firstFalse_realizable (MvPolynomial.X ())) rfl (by intros; trivial)
  have refined := countedReady.refineOutput
    (fun sizes value => value.toNat < MvPolynomial.eval sizes (MvPolynomial.X () + 1)) (by
      intro sizes arguments
      have bound := firstFalse_bound (MvPolynomial.X ()) sizes
        (unaryCountFlags.compute sizes arguments)
      simp only [map_add, map_one]
      convert Nat.lt_succ_of_le bound using 1
      rfl)
  have reindexed := refined.reinterpretOutput unaryPrefixLength.outputDomain
    (fun _ value => ⟨value.val.toNat, value.property⟩) (by intros; rfl) (by
      intro sizes value
      apply congrArg ArrayEncoding.bits
      apply BitVec.eq_of_toNat_eq
      simp [unaryPrefixLength, boundedIndex, boundedIndexOfWidth]
      rfl)
  apply reindexed.withSpecification (fun _ _ => True) unaryPrefixLength.compute (by intros; trivial)
  intro sizes arguments valid
  apply Fin.ext
  change ((firstFalse (MvPolynomial.X ())).compute sizes
    ⟨(fun _ index => predicate (arguments () index)), trivial⟩).toNat = _
  rw [firstFalse_correct]
  have mapped : List.ofFn (fun index => predicate (arguments () index)) =
      (List.ofFn (arguments ())).map (predicate) := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.findIdx_map]
  change _ = (List.ofFn (arguments ())).findIdx _
  congr 1

/-- Observe the prefix length without unfolding its realization. -/
theorem unaryPrefixLength_correct (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    (unaryPrefixLength.compute sizes ⟨(fun _ => letters), trivial⟩).val =
      (List.ofFn letters).findIdx (fun letter => decide (letter ≠ .inr 1)) := rfl

/-- A prefix count and its unchanged source word, in that order. -/
noncomputable def prefixInputs (choice : Bool) : EncodedDomain Unit :=
  if choice then letterDomain.arrayOfLength (MvPolynomial.X ())
  else boundedIndex (MvPolynomial.X () + 1)

/-- The supplied count is the actual number of leading count symbols. -/
def prefixCountAgrees (sizes : Unit → ℕ) (arguments : ∀ choice, (prefixInputs choice).Carrier sizes) : Prop :=
  (arguments false).val = (List.ofFn (arguments true)).findIdx
    (fun letter : Letter => decide (letter ≠ .inr 1))

/-- Prepare the actual prefix count once and retain the unchanged word for a
consumer whose precondition is exactly agreement of that count. -/
noncomputable def afterPrefix (output : EncodedDomain Unit)
    (operation : ∀ sizes, {arguments : ∀ choice, (prefixInputs choice).Carrier sizes //
      prefixCountAgrees sizes arguments} → output.Carrier sizes) : Computation Unit Unit where
  inputDomains := unaryPrefixLength.inputDomains
  outputDomain := output
  precondition _ _ := True
  compute sizes arguments := operation sizes
    ⟨(fun choice => match choice with
      | false => unaryPrefixLength.compute sizes arguments
      | true => arguments.val ()), unaryPrefixLength_correct sizes (arguments.val ())⟩

theorem afterPrefix_realizable (output : EncodedDomain Unit)
    (operation : ∀ sizes, {arguments : ∀ choice, (prefixInputs choice).Carrier sizes //
      prefixCountAgrees sizes arguments} → output.Carrier sizes)
    (ready : (Computation.mk prefixInputs output prefixCountAgrees operation).Realizable) :
    (afterPrefix output operation).Realizable := by
  let context : Unit ⊕ Unit → EncodedDomain Unit := Sum.elim unaryPrefixLength.inputDomains
    (fun _ => unaryPrefixLength.outputDomain)
  have continuation := ready.onArguments context
    (fun sizes arguments => prefixCountAgrees sizes (fun choice => match choice with
      | false => arguments (.inr ())
      | true => arguments (.inl ())))
    (fun choice => match choice with | false => .inr () | true => .inl ())
    (by intro choice; cases choice <;> rfl) (by intro sizes arguments; exact arguments.property)
  have complete := unaryPrefixLength_realizable.letThen continuation (by intros; rfl) rfl (by
    intro sizes arguments valid
    exact unaryPrefixLength_correct sizes (arguments ()))
  exact complete.withSpecification (fun _ _ => True) (afterPrefix output operation).compute
    (by intros; trivial) (by
      intro sizes arguments valid
      apply congrArg (operation sizes)
      apply Subtype.ext
      funext choice
      cases choice <;> rfl)

/-- Locate the first letter different from the unary count symbol. This does
not accept a separator or a payload on its own. -/
noncomputable def unaryHeaderBoundary : Computation Unit Unit where
  inputDomains _ := letterDomain.arrayOfLength (MvPolynomial.X ())
  outputDomain := arraySearchResult (MvPolynomial.X ())
  precondition _ _ := True
  compute _ arguments := by
    classical
    exact ArraySearch.firstFalse (fun index => decide (arguments.val () index = .inr 1))

/-- Boundary detection reuses a fixed letter predicate, array map, and the
certified first-false search. It handles zero-length words without a sentinel. -/
theorem unaryHeaderBoundary_realizable : unaryHeaderBoundary.Realizable := by
  let predicate : Letter → Bool := fun letter => decide (letter = .inr 1)
  have mapped := unaryCountFlags_realizable
  have searched := mapped.followedBy (arrayFindFalse_realizable (MvPolynomial.X ())) rfl
    (by intros; trivial)
  apply searched.withSpecification (fun _ _ => True) unaryHeaderBoundary.compute (by intros; trivial)
  intro sizes arguments valid
  simp only [Computation.followedBy, unaryCountFlags, mapArray]
  apply (arrayFindFalse_spec (MvPolynomial.X ()) sizes
    (fun index => predicate (arguments () index))).trans
  apply congrArg ArraySearch.firstFalse
  funext index
  apply Bool.eq_iff_iff.mpr
  simp [predicate]

/-- No boundary exists exactly when the complete word consists of count
symbols; this includes the empty word. -/
theorem unaryHeaderBoundary_none (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter) :
    unaryHeaderBoundary.compute sizes ⟨(fun _ => letters), trivial⟩ = none ↔
      ∀ index, letters index = .inr 1 := by
  unfold unaryHeaderBoundary
  rw [ArraySearch.firstFalse_none]
  simp

/-- A canonical header's boundary is exactly its unary count. The separator
remains available for the caller's checked lookup. -/
theorem unaryHeaderBoundary_prefix (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter)
    (count : ℕ) (payload : Word)
    (serialized : List.ofFn letters = List.replicate count (.inr 1) ++ .inr 0 :: payload) :
    ∃ index, unaryHeaderBoundary.compute sizes ⟨(fun _ => letters), trivial⟩ = some index ∧
      index.val = count := by
  have lengths := congrArg List.length serialized
  simp only [List.length_ofFn, List.length_append, List.length_replicate, List.length_cons] at lengths
  let index : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) := ⟨count, by omega⟩
  refine ⟨index, ?_, rfl⟩
  have same : unaryHeaderBoundary.compute sizes ⟨(fun _ => letters), trivial⟩ =
      ArraySearch.firstFalse (fun position => decide (letters position = .inr 1)) := by
    apply congrArg ArraySearch.firstFalse
    funext position
    apply Bool.eq_iff_iff.mpr
    simp
  rw [same, ArraySearch.firstFalse_some_iff]
  have flags : List.ofFn (fun position => decide (letters position = .inr 1)) =
      (List.ofFn letters).map (fun letter => decide (letter = .inr 1)) := by
    rw [List.map_ofFn]
    rfl
  rw [flags, serialized]
  change ((List.replicate count (.inr 1 : Letter) ++ (.inr 0 : Letter) :: payload).map
    (fun letter : Letter => decide (letter = .inr 1))).findIdx (! ·) = count
  clear flags same serialized lengths index letters sizes
  induction count with
  | zero => simp [List.findIdx_cons]
  | succ count hypothesis =>
    simpa [List.replicate_succ, List.findIdx_cons] using congrArg Nat.succ hypothesis

/-- Successful parsing by the word-level header definition gives the same
count as the certified boundary scan. -/
theorem unaryHeaderBoundary_readPairHeader (sizes : Unit → ℕ)
    (letters : Fin (MvPolynomial.eval sizes (MvPolynomial.X ())) → Letter)
    (count : ℕ) (payload : Word)
    (parsed : readPairHeader (List.ofFn letters) = some (count, payload)) :
    ∃ index, unaryHeaderBoundary.compute sizes ⟨(fun _ => letters), trivial⟩ = some index ∧
      index.val = count :=
  unaryHeaderBoundary_prefix sizes letters count payload (readPairHeader_canonical parsed)

end Polytime2.Complexity
