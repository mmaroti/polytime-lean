import Polytime2.Complexity.BlockDecode
import Polytime2.Arrays.Append
import Polytime2.Arrays.Tabulate
import Polytime2.Arrays.FirstFalse
import Polytime2.Computation.Optional
import Polytime2.Primitives.FiniteOperations
import Polytime2.Encoding.Word

/-! # Certified native words as sentinel-terminated coded streams

The ordinary array carrier is `Option Letter`. Live native letters are present
values; absent values terminate the stream and fill its unused capacity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.Complexity

open EncodedDomain Polytime2.Computation

variable {Parameter : Type} [Fintype Parameter]

private noncomputable def fixedLetter : EncodedDomain Empty :=
  fixed (Fintype.equivFin Letter)

/-- Fixed optional native-letter blocks, with absent values encoded as zero. -/
noncomputable def codedLetterDomain : EncodedDomain Parameter :=
  (optional fixedLetter).constant

private noncomputable def binaryLetter : Computation Parameter Unit :=
  unaryMap booleans codedLetterDomain (fun _ _ => True)
    (fun _ value => some (.inl value.val))

private theorem binaryLetter_realizable : (binaryLetter (Parameter := Parameter)).Realizable := by
  have finite := (finiteOperation_realizable (fun _ : Unit => (booleans : EncodedDomain Empty))
    (optional fixedLetter) (fun arguments => some (.inl (arguments ())))).withConstantSizes
    (Parameter := Parameter)
  have viewed := finite.reinterpretInputs (fun _ => (booleans : EncodedDomain Parameter))
    (fun _ _ value => value)
    (by intros; simp [withConstantSizes, finiteOperation, width, booleans])
    (by intros; simp [withConstantSizes, finiteOperation, constant_encode_bits, booleans, fixed_encode_bits])
    (fun _ _ => True) (by intros; trivial)
  exact viewed.withSpecification (fun _ _ => True) binaryLetter.compute
    (by intros; trivial) (by intros; rfl)

private noncomputable def payloadBits (domain : EncodedDomain Parameter) : Computation Parameter Unit :=
  encodingMap domain (booleans.arrayOfLength domain.widthPolynomial)
    (fun sizes value index => (domain.encode sizes value).getLsbD index.val)

private theorem payloadBits_realizable (domain : EncodedDomain Parameter) :
    (payloadBits domain).Realizable := by
  apply encodingMap_realizable
  · intro sizes
    norm_num [width, booleans, fixed, ofCodec]
  · intro sizes value
    rw [FirstFalse.boolean_bits]

private noncomputable def codedPayload (domain : EncodedDomain Parameter) :=
  (payloadBits domain).followedBy
    (mapArray booleans codedLetterDomain domain.widthPolynomial (fun _ bit => some (.inl bit)))
    rfl (by intros; trivial)

private theorem codedPayload_realizable (domain : EncodedDomain Parameter) :
    (codedPayload domain).Realizable :=
  (payloadBits_realizable domain).followedBy
    (mapArray_realizable booleans codedLetterDomain domain.widthPolynomial
      (fun _ bit => some (.inl bit)) binaryLetter_realizable) rfl (by intros; trivial)

private noncomputable def codedHeader (count : MvPolynomial Parameter ℕ) : Computation Parameter Empty :=
  (arrayAppend codedLetterDomain count 1).onResults Empty.elim (fun _ _ => True)
    (fun _ sizes _ =>
      ((arrayReplicate (optional fixedLetter) count (some (.inr 1))).compute sizes ⟨(fun empty => nomatch empty), trivial⟩,
       (arrayReplicate (optional fixedLetter) 1 (some (.inr 0))).compute sizes ⟨(fun empty => nomatch empty), trivial⟩))
    (by intros; trivial)

private theorem codedHeader_realizable (count : MvPolynomial Parameter ℕ) :
    (codedHeader count).Realizable := by
  apply (arrayAppend_realizable codedLetterDomain count 1).onResults
  intro singleton
  cases singleton
  exact (arrayReplicate_realizable (optional fixedLetter) count (some (.inr 1))).prodMk
    (arrayReplicate_realizable (optional fixedLetter) 1 (some (.inr 0)))

/-- Exact live stream for a unary count, separator, and canonical payload. -/
noncomputable def nativeWordArray (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) : Computation Parameter Unit :=
  (arrayAppend codedLetterDomain (count + 1) domain.widthPolynomial).onResults
    (fun _ : Unit => domain) (fun _ _ => True)
    (fun _ sizes arguments =>
      ((codedHeader count).compute sizes ⟨(fun empty => nomatch empty), trivial⟩,
       (codedPayload domain).compute sizes arguments)) (by intros; trivial)

theorem nativeWordArray_realizable (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) : (nativeWordArray count domain).Realizable := by
  have header := (codedHeader_realizable count).onResults (fun _ : Unit => domain)
    (fun _ _ => True) (fun empty => nomatch empty) (by intros; trivial)
    (fun empty => nomatch empty)
  apply (arrayAppend_realizable codedLetterDomain (count + 1) domain.widthPolynomial).onResults
  intro singleton
  cases singleton
  exact header.prodMk (codedPayload_realizable domain)

/-- No padding contributes to the constructed native word. -/
theorem nativeWordArray_list (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (arguments : (nativeWordArray count domain).Arguments sizes) :
    List.ofFn ((nativeWordArray count domain).compute sizes ⟨arguments, trivial⟩) =
      (List.replicate (MvPolynomial.eval sizes count) (Sum.inr (1 : Fin 3) : Letter) ++
        (Sum.inr (0 : Fin 3) : Letter) :: domain.word sizes (arguments ())).map some := by
  change List.ofFn ((arrayAppend codedLetterDomain (count + 1) domain.widthPolynomial).compute sizes _) = _
  rw [arrayAppend_list]
  change List.ofFn ((arrayAppend codedLetterDomain count 1).compute sizes _) ++ _ = _
  rw [arrayAppend_list]
  simp [arrayReplicate, arrayTabulate, codedPayload, followedBy, mapArray, payloadBits,
    encodingMap, unaryMap, word, ArrayEncoding.bits, List.map_ofFn, Function.comp_def]


/-- Live native letters followed by one absent sentinel. -/
noncomputable def nativeWordStream (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) : Computation Parameter Unit :=
  (arrayAppend codedLetterDomain ((count + 1) + domain.widthPolynomial) 1).onResults
    (fun _ : Unit => domain) (fun _ _ => True)
    (fun _ sizes arguments =>
      ((nativeWordArray count domain).compute sizes arguments,
       (arrayReplicate (optional fixedLetter) 1 none).compute sizes
         ⟨(fun empty => nomatch empty), trivial⟩)) (by intros; trivial)

theorem nativeWordStream_realizable (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) : (nativeWordStream count domain).Realizable := by
  have sentinel := (arrayReplicate_realizable (optional fixedLetter) (Parameter := Parameter) 1 none).onResults
    (fun _ : Unit => domain) (fun _ _ => True) (fun empty => nomatch empty)
    (by intros; trivial) (fun empty => nomatch empty)
  apply (arrayAppend_realizable codedLetterDomain ((count + 1) + domain.widthPolynomial) 1).onResults
  intro singleton
  cases singleton
  exact (nativeWordArray_realizable count domain).prodMk sentinel

/-- The sentinel comes immediately after the exact native word. -/
theorem nativeWordStream_list (count : MvPolynomial Parameter ℕ)
    (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (arguments : (nativeWordStream count domain).Arguments sizes) :
    List.ofFn ((nativeWordStream count domain).compute sizes ⟨arguments, trivial⟩) =
      (List.replicate (MvPolynomial.eval sizes count) (Sum.inr (1 : Fin 3) : Letter) ++
        (Sum.inr (0 : Fin 3) : Letter) :: domain.word sizes (arguments ())).map some ++ [none] := by
  change List.ofFn ((arrayAppend codedLetterDomain ((count + 1) + domain.widthPolynomial) 1).compute sizes _) = _
  rw [arrayAppend_list, nativeWordArray_list]
  simp [arrayReplicate, arrayTabulate]

end Polytime2.Complexity
