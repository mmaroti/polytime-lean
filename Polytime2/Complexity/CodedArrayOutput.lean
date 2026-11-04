import Polytime2.Complexity.NativeStream

/-! # Exact native export of coded-letter arrays -/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

private noncomputable def blockDomain : EncodedDomain Empty :=
  optional (fixed (Fintype.equivFin Letter))

private noncomputable def blockWidth : ℕ := blockDomain.width Empty.elim

private noncomputable def code (value : Option Letter) : Fin blockWidth → Bool :=
  fun index => (blockDomain.encode Empty.elim value).getLsbD index.val

private noncomputable def decode (bits : Fin blockWidth → Bool) : Option Letter :=
  (blockDomain.decode Empty.elim
    ((BitVec.ofBoolListLE (List.ofFn bits)).cast (List.length_ofFn (f := bits)))).join

private theorem decode_code (value : Option Letter) : decode (code value) = value := by
  have encoded : (BitVec.ofBoolListLE (List.ofFn (code value))).cast
      (List.length_ofFn (f := code value)) = blockDomain.encode Empty.elim value := by
    apply ArrayEncoding.bits_injective
    rw [ArrayEncoding.bits_ofBoolListLE]
    rfl
  simp only [decode, encoded, blockDomain.decode_encode]
  cases value <;> rfl

private theorem width_positive : 0 < blockWidth := by
  change 0 < ((optional (fixed (Parameter := Empty) (Fintype.equivFin Letter))).width Empty.elim)
  norm_num [blockWidth, blockDomain, EncodedDomain.optional, width, reindex, variant,
    fixed, ofCodec, RecordEncoding.domain, VariantEncoding.fields, Fin.sum_univ_succ]

/-- Export an array containing the exact live word and an absent sentinel.
The remaining array entries may be arbitrary valid optional-letter codes. -/
theorem codedArray_polynomialTime {Parameter : Type} [Fintype Parameter]
    {Source : Type*} (capacity : MvPolynomial Parameter ℕ)
    (sizes : Source → Parameter → ℕ)
    (values : ∀ source, (codedLetterDomain.arrayOfLength capacity).Carrier (sizes source))
    (output : Source → Word)
    (stream : ∀ source, ∃ padding : List (Option Letter),
      List.ofFn (values source) = (output source).map some ++ none :: padding) :
    PolynomialTime
      (fun source => (codedLetterDomain.arrayOfLength capacity).word
        (sizes source) (values source)) id output := by
  classical
  let packed := fun value => (output value,
    ((stream value).choose.flatMap (fun letter => List.ofFn (code letter))))
  have decoder := (BlockDecode.polynomialTime blockWidth width_positive decode
    (fun letter => code (some letter)) (fun letter => decode_code (some letter))
    (code none) (decode_code none)).precomp packed
  have sameEncoding : BlockDecode.inputWord (fun letter => code (some letter)) (code none) ∘ packed =
      (fun value => (codedLetterDomain.arrayOfLength capacity).word
        (sizes value) (values value)) := by
    funext value
    dsimp only [Function.comp_def, BlockDecode.inputWord, BlockDecode.inputBits, packed, word]
    congr 1
    rw [arrayOfLength_encode_bits, ArrayEncoding.bits_encode]
    simp only [codedLetterDomain, constant_encode_bits]
    let array : Fin (MvPolynomial.eval (sizes value) capacity) → Option Letter := values value
    change _ = (List.ofFn ((fun letter => List.ofFn (code letter)) ∘ array)).flatten
    rw [← List.map_ofFn (f := array) (g := fun letter => List.ofFn (code letter))]
    change _ = List.flatMap (fun letter => List.ofFn (code letter)) (List.ofFn array)
    have sameList : List.ofFn array = (output value).map some ++ none :: (stream value).choose :=
      (stream value).choose_spec
    have flattened := congrArg (List.flatMap (fun letter => List.ofFn (code letter))) sameList
    simpa [List.flatMap_append, List.flatMap_map, Function.comp_def] using flattened.symm
  rw [sameEncoding] at decoder
  exact decoder


/-- Polynomial size substitution preserves the coded stream's native export.
The codec transport is shared by specialized compiler applications. -/
theorem codedArray_substitute_polynomialTime
    {Parameter HostParameter : Type} [Fintype Parameter] [Fintype HostParameter]
    {Source : Type*} (capacity : MvPolynomial Parameter ℕ)
    (substitution : Parameter → MvPolynomial HostParameter ℕ)
    (sizes : Source → HostParameter → ℕ)
    (values : ∀ source, ((codedLetterDomain.arrayOfLength capacity).substitute substitution).Carrier (sizes source))
    (output : Source → Word)
    (stream : ∀ source, ∃ padding : List (Option Letter),
      List.ofFn (values source) = (output source).map some ++ none :: padding) :
    PolynomialTime
      (fun source => ((codedLetterDomain.arrayOfLength capacity).substitute substitution).word
        (sizes source) (values source)) id output := by
  have decoded := codedArray_polynomialTime capacity
    (fun source => SizeSubstitution.assignment substitution (sizes source)) values output stream
  have encoded : (fun source => (codedLetterDomain.arrayOfLength capacity).word
      (SizeSubstitution.assignment substitution (sizes source)) (values source)) =
      (fun source => ((codedLetterDomain.arrayOfLength capacity).substitute substitution).word
        (sizes source) (values source)) := by
    funext source
    exact (substitute_word (codedLetterDomain.arrayOfLength capacity) substitution
      (sizes source) (values source)).symm
  rw [encoded] at decoded
  exact decoded

end Polytime2.Complexity
