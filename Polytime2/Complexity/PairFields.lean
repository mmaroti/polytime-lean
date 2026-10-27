import Polytime2.Complexity.PairValidation
import Polytime2.Arrays.Slice
import Polytime2.Arithmetic.WidthOperations

/-! # Exact fields of unary-header words

The mathematical count is bounded by the input length. Endpoint arithmetic and
interval packing use existing computation rules; no word-specific machine or
storage convention is introduced.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation
open Polytime2.Computation.Realizable.Internal

private noncomputable def fieldEndpoint (doubled : Bool) : Computation Unit Unit where
  inputDomains _ := boundedIndex (MvPolynomial.X () + 1)
  outputDomain := arrayPosition (MvPolynomial.X () + 1)
  precondition sizes arguments := (if doubled then 2 * (arguments ()).val else (arguments ()).val) < sizes ()
  compute sizes arguments := ⟨(if doubled then 2 * (arguments.val ()).val else (arguments.val ()).val) + 1, by
    simp only [map_add, map_one, MvPolynomial.eval_X]
    have fits := arguments.property
    split_ifs at * <;> omega⟩

private theorem fieldEndpoint_realizable (doubled : Bool) : (fieldEndpoint doubled).Realizable := by
  let width : MvPolynomial Unit ℕ := MvPolynomial.X () + 1
  have widePower (sizes : Unit → ℕ) : sizes () < 2 ^ MvPolynomial.eval sizes (width + 1) := by
    have power := Nat.lt_two_pow_self (n := sizes () + 2)
    simp only [width, map_add, map_one, MvPolynomial.eval_X]
    have smaller : sizes () < 2 ^ (sizes () + 2) := by omega
    simpa only [Nat.add_assoc, Nat.reduceAdd] using smaller
  let computation := fieldEndpoint doubled
  let inputs := computation.inputDomains
  let allowed := computation.precondition
  have natural := (naturalWiden_realizable width 1).reinterpretInputs inputs
    (fun _ sizes value => ⟨value.val, value.isLt.trans_le Nat.lt_two_pow_self.le⟩)
    (by intros; rfl) (by intros; rfl) allowed (by intros; trivial)
  let widened (sizes : Unit → ℕ) (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :
      (binaryNaturalsOfWidth (width + 1)).Carrier sizes :=
    ⟨(arguments.val ()).val, by
      have bound := (arguments.val ()).isLt
      change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
      simp only [width, map_add, map_one, MvPolynomial.eval_X] at *
      exact bound.trans_le ((Nat.le_succ _).trans Nat.lt_two_pow_self.le)⟩
  have widenedReady : (Computation.mk inputs (binaryNaturalsOfWidth (width + 1)) allowed widened).Realizable :=
    natural.withSpecification allowed widened (by intros; assumption) (by intros; apply Fin.ext; rfl)
  let base (sizes : Unit → ℕ) (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :
      (binaryNaturalsOfWidth (width + 1)).Carrier sizes :=
    ⟨if doubled then 2 * (arguments.val ()).val else (arguments.val ()).val, by
      have fits := arguments.property
      change (if doubled then 2 * (arguments.val ()).val else (arguments.val ()).val) < sizes () at fits
      change _ < 2 ^ MvPolynomial.eval sizes (width + 1)
      have power := widePower sizes
      split_ifs at * <;> omega⟩
  have baseReady : (Computation.mk inputs (binaryNaturalsOfWidth (width + 1)) allowed base).Realizable := by
    cases flag : doubled with
    | false =>
      exact widenedReady.withSpecification allowed base (by intros; assumption)
        (by intros; apply Fin.ext; simp [base, widened, flag])
    | true =>
      have added := (naturalAdd_realizable (width + 1)).onResults inputs allowed
        (fun _ sizes arguments => widened sizes arguments) (by
          intro sizes arguments
          change (widened sizes arguments).val + (widened sizes arguments).val < _
          have bound := (base sizes arguments).isLt
          simpa only [base, flag, ↓reduceIte, widened, two_mul] using bound)
        (fun _ => widenedReady)
      exact added.withSpecification allowed base (by intros; assumption)
        (by
          intro sizes arguments valid
          apply Fin.ext
          change (widened sizes ⟨arguments, valid⟩).val + (widened sizes ⟨arguments, valid⟩).val = _
          simp [base, widened, flag, two_mul])
  have incremented := baseReady.followedBy (naturalIncrement_realizable (width + 1)) rfl (by intros; trivial)
  have bounded sizes (arguments : {arguments : computation.Arguments sizes // allowed sizes arguments}) :
      (base sizes arguments).val + 1 < MvPolynomial.eval sizes (MvPolynomial.X () + 1) := by
    have fits := arguments.property
    change (if doubled then 2 * (arguments.val ()).val else (arguments.val ()).val) < sizes () at fits
    simp only [base, map_add, map_one, MvPolynomial.eval_X]
    split_ifs at * <;> omega
  have refined := incremented.refineOutput
    (fun sizes value => value.val < MvPolynomial.eval sizes (MvPolynomial.X () + 1)) (by
      intro sizes arguments
      change ((base sizes arguments).val + 1) % 2 ^ MvPolynomial.eval sizes (width + 1) < _
      exact (Nat.mod_le _ _).trans_lt (bounded sizes arguments))
  have result := refined.reinterpretOutput computation.outputDomain
    (fun _ value => ⟨value.val.val, value.property⟩) (by intros; rfl) (by intros; rfl)
  apply result.withSpecification allowed computation.compute (by intros; assumption)
  intro sizes arguments valid
  apply Fin.ext
  have fits := bounded sizes ⟨arguments, valid⟩
  have power := widePower sizes
  change ((base sizes ⟨arguments, valid⟩).val + 1) % 2 ^ MvPolynomial.eval sizes (width + 1) = _
  rw [Nat.mod_eq_of_lt (by
    simp only [map_add, map_one, MvPolynomial.eval_X] at fits
    omega)]
  rfl

private noncomputable def wordEnd : Computation Unit Empty where
  inputDomains := Empty.elim
  outputDomain := arrayPosition (MvPolynomial.X () + 1)
  precondition _ _ := True
  compute sizes _ := ⟨sizes (), by simp⟩

private theorem wordEnd_realizable : wordEnd.Realizable := by
  let length : MvPolynomial Unit ℕ := MvPolynomial.X ()
  let width := length + 1
  have magnitude := (polynomialIntegerSize_realizable length).followedBy
    (integerMagnitude_realizable width) rfl (by intros; trivial)
  have widened := magnitude.followedBy (naturalWiden_realizable width 1) rfl (by intros; trivial)
  have refined := widened.refineOutput
    (fun sizes value => value.val < MvPolynomial.eval sizes (length + 1)) (by
      intro sizes arguments
      change ((MvPolynomial.eval sizes length : ℕ) : ℤ).natAbs < MvPolynomial.eval sizes (length + 1)
      simp)
  have result := refined.reinterpretOutput wordEnd.outputDomain
    (fun _ value => ⟨value.val.val, value.property⟩) (by intros; rfl) (by intros; rfl)
  exact result.withSpecification (fun _ _ => True) wordEnd.compute (by intros; trivial)
    (by
      intro sizes arguments valid
      apply Fin.ext
      change ((MvPolynomial.eval sizes length : ℕ) : ℤ).natAbs = sizes ()
      simp [length])

/-- Given the announced input length and sufficient payload, extract the exact
input field and remaining witness. False names the count, true the whole word.
The header's letters are checked separately by `pairValid`. -/
noncomputable def pairFields : Computation Unit Bool where
  inputDomains := prefixInputs
  outputDomain := (boundedArray letterDomain (MvPolynomial.X ())).prod
    (boundedArray letterDomain (MvPolynomial.X ()))
  precondition sizes arguments := 2 * (arguments false).val < sizes ()
  compute sizes arguments :=
    let lower := (fieldEndpoint false).compute sizes ⟨(fun _ => arguments.val false), by
      have fits := arguments.property
      change 2 * (arguments.val false).val < sizes () at fits
      change (arguments.val false).val < sizes ()
      omega⟩
    let middle := (fieldEndpoint true).compute sizes ⟨(fun _ => arguments.val false), arguments.property⟩
    let last := wordEnd.compute sizes ⟨(fun empty => empty.elim), trivial⟩
    let field (witness : Bool) := (arraySlice letterDomain (MvPolynomial.X ())).compute sizes
      ⟨(fun name => match name with
        | none => arguments.val true
        | some false => if witness then middle else lower
        | some true => if witness then last else middle), trivial⟩
    (field false, field true)

theorem pairFields_realizable : pairFields.Realizable := by
  let computation := pairFields
  have endpoint (doubled : Bool) := (fieldEndpoint_realizable doubled).onArguments
    computation.inputDomains computation.precondition (fun _ => false) (by intros; rfl)
    (by
      intro sizes arguments
      have fits := arguments.property
      change 2 * (arguments.val false).val < sizes () at fits
      change (if doubled then 2 * (arguments.val false).val else (arguments.val false).val) < sizes ()
      cases doubled <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
  have last := wordEnd_realizable.onResults computation.inputDomains computation.precondition
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  let endpointValue (doubled : Bool) sizes
      (arguments : {arguments : computation.Arguments sizes // computation.precondition sizes arguments}) :=
    (fieldEndpoint doubled).compute sizes ⟨(fun _ => arguments.val false), by
      have fits := arguments.property
      change 2 * (arguments.val false).val < sizes () at fits
      change (if doubled then 2 * (arguments.val false).val else (arguments.val false).val) < sizes ()
      cases doubled <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  have field (witness : Bool) := (arraySlice_realizable letterDomain (MvPolynomial.X ())).onResults
    computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
    | none => arguments.val true
    | some false => if witness then endpointValue true sizes arguments else endpointValue false sizes arguments
    | some true => if witness then wordEnd.compute sizes ⟨(fun empty => empty.elim), trivial⟩
      else endpointValue true sizes arguments)
    (by intros; trivial) (by
      intro name
      cases name with
      | none => exact Realizable.argument computation.inputDomains true computation.precondition
      | some choice => cases choice <;> cases witness <;>
          first | exact endpoint false | exact endpoint true | exact last)
  exact (field false).prodMk (field true)

/-- The extracted fields have precisely the serialized input and witness
contents; neither result exposes unused capacity. -/
theorem pairFields_correct (sizes : Unit → ℕ) (arguments : pairFields.Arguments sizes)
    (fits : pairFields.precondition sizes arguments) :
    let result := pairFields.compute sizes ⟨arguments, fits⟩
    (List.ofFn result.1.2, List.ofFn result.2.2) =
      (((List.ofFn (arguments true)).drop ((arguments false).val + 1)).take (arguments false).val,
        (List.ofFn (arguments true)).drop (2 * (arguments false).val + 1)) := by
  dsimp only [pairFields]
  rw [arraySlice_correct, arraySlice_correct]
  dsimp only [fieldEndpoint, wordEnd]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have difference : 2 * (arguments false).val + 1 - ((arguments false).val + 1) =
      (arguments false).val := by omega
  rw [difference]
  congr 1
  apply List.take_of_length_le
  simp only [List.length_drop, List.length_ofFn, MvPolynomial.eval_X]
  exact le_rfl

/-- When the supplied count is the parsed header count, the certified fields
are exactly the two words returned by `decodePair`. -/
theorem pairFields_decodePair (sizes : Unit → ℕ) (arguments : pairFields.Arguments sizes)
    (fits : pairFields.precondition sizes arguments) (payload : Word)
    (parsed : readPairHeader (List.ofFn (arguments true)) = some ((arguments false).val, payload)) :
    let result := pairFields.compute sizes ⟨arguments, fits⟩
    decodePair (List.ofFn (arguments true)) = some (List.ofFn result.1.2, List.ofFn result.2.2) := by
  have canonical := readPairHeader_canonical parsed
  have lengths := congrArg List.length canonical
  simp only [List.length_ofFn, List.length_append, List.length_replicate, List.length_cons,
    MvPolynomial.eval_X] at lengths
  have enough : (arguments false).val ≤ payload.length := by
    change 2 * (arguments false).val < sizes () at fits
    omega
  have rest : (List.ofFn (arguments true)).drop ((arguments false).val + 1) = payload := by
    rw [canonical]
    simp [List.drop_append]
  have tail : (List.ofFn (arguments true)).drop (2 * (arguments false).val + 1) =
      payload.drop (arguments false).val := by
    calc
      _ = ((List.ofFn (arguments true)).drop ((arguments false).val + 1)).drop (arguments false).val := by
        rw [List.drop_drop]
        congr 1
        omega
      _ = _ := by rw [rest]
  dsimp only
  rw [pairFields_correct, rest, tail]
  simp only [decodePair, parsed]
  change (if (arguments false).val ≤ payload.length then some _ else none) = some _
  simp only [enough, ↓reduceIte]

/-- Extract a unary header's count and complete remaining payload at a supplied
count. False names the count and true the source word. Only the existence of
a boundary inside the word is required; separator validation is separate. -/
noncomputable def headerFields : Computation Unit Bool where
  inputDomains := pairFields.inputDomains
  outputDomain := (boundedIndex (MvPolynomial.X () + 1)).prod
    (boundedArray letterDomain (MvPolynomial.X ()))
  precondition sizes arguments := (arguments false).val < sizes ()
  compute sizes arguments :=
    (arguments.val false, (arraySlice letterDomain (MvPolynomial.X ())).compute sizes
      ⟨(fun name => match name with
        | none => arguments.val true
        | some false => (fieldEndpoint false).compute sizes
            ⟨(fun _ => arguments.val false), arguments.property⟩
        | some true => wordEnd.compute sizes ⟨(fun empty => empty.elim), trivial⟩), trivial⟩)

theorem headerFields_realizable : headerFields.Realizable := by
  let computation := headerFields
  have lower := (fieldEndpoint_realizable false).onArguments computation.inputDomains computation.precondition
    (fun _ => false) (by intros; rfl) (by intro sizes arguments; exact arguments.property)
  have last := wordEnd_realizable.onResults computation.inputDomains computation.precondition
    (fun empty => empty.elim) (by intros; trivial) (fun empty => empty.elim)
  have payload := (arraySlice_realizable letterDomain (MvPolynomial.X ())).onResults
    computation.inputDomains computation.precondition
    (fun name sizes arguments => match name with
    | none => arguments.val true
    | some false => (fieldEndpoint false).compute sizes ⟨(fun _ => arguments.val false), arguments.property⟩
    | some true => wordEnd.compute sizes ⟨(fun empty => empty.elim), trivial⟩)
    (by intros; trivial) (by
      intro name
      cases name with
      | none => exact Realizable.argument computation.inputDomains true computation.precondition
      | some choice => cases choice; exact lower; exact last)
  exact (Realizable.argument computation.inputDomains false computation.precondition).prodMk payload

/-- The header extractor returns the actual count and unpadded suffix. -/
theorem headerFields_correct (sizes : Unit → ℕ) (arguments : headerFields.Arguments sizes)
    (fits : headerFields.precondition sizes arguments) :
    let result := headerFields.compute sizes ⟨arguments, fits⟩
    (result.1.val, List.ofFn result.2.2) =
      ((arguments false).val, (List.ofFn (arguments true)).drop ((arguments false).val + 1)) := by
  dsimp only [headerFields]
  rw [arraySlice_correct]
  dsimp only [fieldEndpoint, wordEnd]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  apply List.take_of_length_le
  simp only [List.length_drop, List.length_ofFn, MvPolynomial.eval_X]
  exact le_rfl

/-- Header extraction preserves the count and payload returned by successful
word-level parsing. -/
theorem headerFields_readPairHeader (sizes : Unit → ℕ) (arguments : headerFields.Arguments sizes)
    (fits : headerFields.precondition sizes arguments) (payload : Word)
    (parsed : readPairHeader (List.ofFn (arguments true)) = some ((arguments false).val, payload)) :
    let result := headerFields.compute sizes ⟨arguments, fits⟩
    readPairHeader (List.ofFn (arguments true)) = some (result.1.val, List.ofFn result.2.2) := by
  dsimp only
  rw [headerFields_correct]
  have rest : (List.ofFn (arguments true)).drop ((arguments false).val + 1) = payload := by
    rw [readPairHeader_canonical parsed]
    simp [List.drop_append]
  rw [rest]
  exact parsed

end Polytime2.Complexity
