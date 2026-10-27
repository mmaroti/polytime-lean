import Polytime2.Encoding.EncodedArray
import Polytime2.Encoding.ParameterRename
import Polytime2.Complexity.Languages

/-! # Canonical encoded fields as external words

An encoded field is its exact canonical bit list using binary letters. Decoding
rejects nonbinary letters, incorrect lengths, and words rejected by the domain
codec. These functions specify word representations; their polynomial-time
realization is a separate obligation.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.EncodedDomain

open Complexity

variable {Parameter : Type} [Fintype Parameter]

/-- External binary letters for one canonical field. -/
noncomputable def word (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (value : domain.Carrier sizes) : Word := (ArrayEncoding.bits (domain.encode sizes value)).map Sum.inl

namespace Internal

/-- Project the bit after binary-letter validation; rejected symbols are inactive. -/
def letterBit : Letter → Bool
  | .inl bit => bit
  | .inr _ => false

/-- The binary subset of the external alphabet. -/
def isBinaryLetter : Letter → Bool
  | .inl _ => true
  | .inr _ => false

end Internal

open Internal (letterBit isBinaryLetter)

/-- Reject nonbinary letters and otherwise return the exact bit sequence. -/
def decodeBinaryWord (input : Word) : Option (List Bool) :=
  if input = (input.map letterBit).map Sum.inl then some (input.map letterBit) else none

/-- Reject all nonbinary symbols and all noncanonical field widths. -/
noncomputable def decodeWord (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (input : Word) : Option (domain.Carrier sizes) :=
  let bits := input.map letterBit
  if input = bits.map Sum.inl then
    if length : bits.length = domain.width sizes then
      domain.decode sizes ((BitVec.ofBoolListLE bits).cast length)
    else none
  else none

private theorem ofBits {width : ℕ} (bits : BitVec width)
    (length : (ArrayEncoding.bits bits).length = width) :
    (BitVec.ofBoolListLE (ArrayEncoding.bits bits)).cast length = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, ArrayEncoding.bits,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, within, dite_true, Option.getD_some]

@[simp] private theorem map_letterBit_binary (bits : List Bool) :
    (bits.map (Sum.inl : Bool → Letter)).map letterBit = bits := by
  simp [List.map_map, Function.comp_def, letterBit]

/-- Binary decoding accepts exactly the canonical binary-letter words. -/
theorem decodeBinaryWord_some_iff (input : Word) (bits : List Bool) :
    decodeBinaryWord input = some bits ↔ input = bits.map Sum.inl := by
  constructor
  · intro accepted
    unfold decodeBinaryWord at accepted
    split at accepted
    next binary =>
      cases Option.some.inj accepted
      exact binary
    next invalid => cases accepted
  · intro canonical
    rw [canonical]
    simp [decodeBinaryWord, letterBit, List.map_map, Function.comp_def]

/-- Character-wise validation is equivalent to the canonical binary-word test. -/
theorem decodeBinaryWord_eq_all (input : Word) :
    decodeBinaryWord input =
      if input.all isBinaryLetter then some (input.map letterBit) else none := by
  have canonical : input = (input.map letterBit).map Sum.inl ↔ input.all isBinaryLetter = true := by
    induction input with
    | nil => simp
    | cons letter rest hypothesis =>
      cases letter with
      | inl bit =>
        simpa only [List.map_cons, letterBit, List.cons.injEq, List.all_cons, isBinaryLetter,
          Bool.true_and, true_and] using hypothesis
      | inr symbol => simp [letterBit, isBinaryLetter]
  simp only [decodeBinaryWord, canonical]

/-- Canonical domain decoding factors through the same strict binary parser. -/
theorem decodeWord_eq_decodeBinaryWord (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (input : Word) : domain.decodeWord sizes input = (decodeBinaryWord input).bind (fun bits =>
      if length : bits.length = domain.width sizes then
        domain.decode sizes ((BitVec.ofBoolListLE bits).cast length) else none) := by
  dsimp only [decodeWord, decodeBinaryWord]
  by_cases binary : input = (input.map letterBit).map Sum.inl
  · rw [ite_eq_left binary, ite_eq_left binary]
    rfl
  · rw [ite_eq_right binary, ite_eq_right binary]
    rfl

/-- Canonical fields decode to their actual mathematical value. -/
@[simp] theorem decodeWord_word (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (value : domain.Carrier sizes) : domain.decodeWord sizes (domain.word sizes value) = some value := by
  have length : (ArrayEncoding.bits (domain.encode sizes value)).length = domain.width sizes := by
    simp [ArrayEncoding.bits, width]
  dsimp only [decodeWord, word]
  rw [map_letterBit_binary, ite_eq_left rfl, dite_eq_left length, ofBits]
  exact domain.decode_encode sizes value

/-- Field length is its exact codec width, with no additional framing. -/
@[simp] theorem word_length (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (value : domain.Carrier sizes) : (domain.word sizes value).length = domain.width sizes := by
  simp [word, ArrayEncoding.bits, width]

/-- Decoding accepts only canonical fields. -/
theorem word_decodeWord (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (input : Word) (value : domain.Carrier sizes)
    (accepted : domain.decodeWord sizes input = some value) : domain.word sizes value = input := by
  unfold decodeWord at accepted
  dsimp only at accepted
  split at accepted
  next binary =>
    split at accepted
    next length =>
      have encoded := domain.encode_decode sizes _ value accepted
      unfold word
      rw [encoded]
      have bitsEqual := ArrayEncoding.bits_ofBoolListLE (input.map letterBit) length
      exact (congrArg (List.map Sum.inl) bitsEqual).trans binary.symm
    next invalid => simp at accepted
  next invalid => simp at accepted

/-- A word decodes to a value exactly when it is that value's canonical word. -/
theorem decodeWord_eq_some_iff (domain : EncodedDomain Parameter) (sizes : Parameter → ℕ)
    (input : Word) (value : domain.Carrier sizes) :
    domain.decodeWord sizes input = some value ↔ domain.word sizes value = input := by
  constructor
  · exact domain.word_decodeWord sizes input value
  · intro canonical
    rw [← canonical]
    exact domain.decodeWord_word sizes value

/-- Size renaming preserves canonical word decoding as well as encoded bits. -/
theorem renameParameters_decodeWord {NewParameter : Type} [Fintype NewParameter]
    (domain : EncodedDomain Parameter) (names : Parameter → NewParameter)
    (sizes : NewParameter → ℕ) (input : Word) :
    (domain.renameParameters names).decodeWord sizes input = domain.decodeWord (sizes ∘ names) input := by
  apply Option.ext
  intro value
  rw [decodeWord_eq_some_iff, decodeWord_eq_some_iff]
  simp only [word, renameParameters_bits]

end Polytime2.EncodedDomain
