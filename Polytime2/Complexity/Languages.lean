import Polytime2.Complexity.PolynomialTime
import Mathlib.Computability.Language

/-! # Word languages, polynomial many-one reductions, and NP

Languages are Mathlib sets of words over the fixed five-letter alphabet.
Membership is defined on every word, not only on canonical representations.
`decodedLanguage` explicitly excludes malformed encodings. A reduction is a
total polynomial-time word function preserving yes and no answers on all words.

NP uses polynomial-length word witnesses and a deterministic polynomial-time
TM0 verifier. Input/witness pairs use a unary length prefix followed by the two
words. Its exact length is `2 * input.length + witness.length + 1`; the verifier
is timed on this entire word. Malformed pair encodings must be rejected.
These definitions make no hardness assumptions about SAT or any other language.
-/

namespace Polytime2.Complexity

/-- A Boolean answer is one ordinary binary letter. -/
def encodeBool (answer : Bool) : Word := [Sum.inl answer]

/-- Decode a unary input-length prefix. The symbols `inr 1` and `inr 0` mean
successor and end of header; all other header symbols are invalid. -/
def readPairHeader : Word → Option (ℕ × Word)
  | [] => none
  | letter :: rest =>
    if letter = .inr 0 then some (0, rest)
    else if letter = .inr 1 then (readPairHeader rest).map (fun pair => (pair.1 + 1, pair.2))
    else none

/-- A self-delimiting pair of arbitrary words; payload symbols are unrestricted. -/
def encodePair (pair : Word × Word) : Word :=
  List.replicate pair.1.length (.inr 1) ++ [.inr 0] ++ pair.1 ++ pair.2

/-- Decode the length header, rejecting a missing header or truncated input. -/
def decodePair (word : Word) : Option (Word × Word) := do
  let (size, payload) ← readPairHeader word
  if size ≤ payload.length then some (payload.take size, payload.drop size) else none

/-- A canonical unary header leaves the complete following payload unchanged. -/
theorem readPairHeader_prefix (size : ℕ) (payload : Word) :
    readPairHeader (List.replicate size (.inr 1) ++ .inr 0 :: payload) = some (size, payload) := by
  induction size with
  | zero => simp [readPairHeader]
  | succ size hypothesis => simp [List.replicate_succ, readPairHeader, hypothesis]

/-- Successful header parsing accounts for every consumed symbol. -/
theorem readPairHeader_canonical {word : Word} {size : ℕ} {payload : Word}
    (accepted : readPairHeader word = some (size, payload)) :
    word = List.replicate size (.inr 1) ++ .inr 0 :: payload := by
  induction word generalizing size payload with
  | nil => simp [readPairHeader] at accepted
  | cons letter rest hypothesis =>
    by_cases zero : letter = .inr 0
    · simp [readPairHeader, zero] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      simp [zero]
    · by_cases one : letter = .inr 1
      · cases parsed : readPairHeader rest with
        | none => simp [readPairHeader, zero, one, parsed] at accepted
        | some pair =>
          rcases pair with ⟨count, suffix⟩
          simp [readPairHeader, zero, one, parsed] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          simpa [one, List.replicate_succ] using congrArg (List.cons (.inr 1)) (hypothesis parsed)
      · simp [readPairHeader, zero, one] at accepted

theorem readPairHeader_count {word : Word} {count : ℕ} {payload : Word}
    (parsed : readPairHeader word = some (count, payload)) :
    word.findIdx (fun letter => decide (letter ≠ .inr 1)) = count := by
  rw [readPairHeader_canonical parsed]
  clear parsed word
  induction count with
  | zero => simp [List.findIdx_cons]
  | succ count hypothesis => simpa [List.replicate_succ, List.findIdx_cons] using congrArg Nat.succ hypothesis

theorem decodePair_isSome (word : Word) :
    (decodePair word).isSome = ((readPairHeader word).isSome &&
      decide (2 * word.findIdx (fun letter => decide (letter ≠ .inr 1)) < word.length)) := by
  cases parsed : readPairHeader word with
  | none => simp [decodePair, parsed]
  | some pair =>
    rcases pair with ⟨count, payload⟩
    have length := congrArg List.length (readPairHeader_canonical parsed)
    simp only [List.length_append, List.length_replicate, List.length_cons] at length
    rw [readPairHeader_count parsed]
    simp only [decodePair, parsed, Option.isSome_some, Bool.true_and]
    change (if count ≤ payload.length then some (payload.take count, payload.drop count) else none).isSome = _
    split_ifs with fits
    · have enough : 2 * count < word.length := by omega
      simp [enough]
    · have insufficient : ¬2 * count < word.length := by omega
      simp [insufficient]

/-- Pairing is a canonical encoding, including empty inputs and witnesses. -/
@[simp] theorem decodePair_encodePair (pair : Word × Word) : decodePair (encodePair pair) = some pair := by
  rcases pair with ⟨input, witness⟩
  simp [decodePair, encodePair, List.append_assoc, readPairHeader_prefix]

theorem encodePair_injective : Function.Injective encodePair := by
  intro first second equal
  have decoded := congrArg decodePair equal
  simpa only [decodePair_encodePair, Option.some.injEq] using decoded

/-- Every prefix, separator, and payload symbol contributes to input length. -/
@[simp] theorem encodePair_length (pair : Word × Word) :
    (encodePair pair).length = 2 * pair.1.length + pair.2.length + 1 := by
  simp [encodePair]
  omega

/-- Every successfully decoded pair has exactly the existing canonical framing. -/
theorem decodePair_canonical {word : Word} {pair : Word × Word}
    (parsed : decodePair word = some pair) : word = encodePair pair := by
  cases header : readPairHeader word with
  | none => simp [decodePair, header] at parsed
  | some fields =>
    rcases fields with ⟨count, payload⟩
    simp only [decodePair, header] at parsed
    change (if count ≤ payload.length then some (payload.take count, payload.drop count) else none) = some pair at parsed
    split at parsed
    next fits =>
      have pairEqual := Option.some.inj parsed
      calc
        word = List.replicate count (.inr 1) ++ .inr 0 :: payload := readPairHeader_canonical header
        _ = encodePair (payload.take count, payload.drop count) := by
          simp only [encodePair, List.length_take, Nat.min_eq_left fits]
          simp only [List.append_assoc, List.cons_append, List.nil_append, List.take_append_drop]
        _ = encodePair pair := congrArg encodePair pairEqual
    next outside => simp at parsed

/-- Successful pair decoding accounts for the complete encoded input length. -/
theorem decodePair_length {word : Word} {pair : Word × Word}
    (parsed : decodePair word = some pair) :
    2 * pair.1.length + pair.2.length + 1 = word.length := by
  rw [decodePair_canonical parsed, encodePair_length]

/-- A word represents a yes-instance only when decoding succeeds and the
decoded mathematical value satisfies the problem predicate. -/
def decodedLanguage {Value : Type*} (decode : Word → Option Value) (predicate : Value → Prop) :
    Language Letter := {word | ∃ value, decode word = some value ∧ predicate value}

theorem not_mem_decodedLanguage {Value : Type*} (decode : Word → Option Value)
    (predicate : Value → Prop) {word : Word} (malformed : decode word = none) :
    word ∉ decodedLanguage decode predicate := by
  rintro ⟨value, valid, _⟩
  simp [malformed] at valid

/-- A polynomial many-one reduction translates all words, preserving both
membership and nonmembership, including malformed problem representations. -/
def ManyOneReducible (source target : Language Letter) : Prop :=
  ∃ translate : Word → Word, PolynomialTime id id translate ∧
    ∀ word, word ∈ source ↔ translate word ∈ target

theorem ManyOneReducible.refl (language : Language Letter) : ManyOneReducible language language :=
  ⟨id, PolynomialTime.id id, fun _ => Iff.rfl⟩

theorem ManyOneReducible.trans {source middle target : Language Letter}
    (first : ManyOneReducible source middle) (second : ManyOneReducible middle target) :
    ManyOneReducible source target := by
  obtain ⟨firstMap, firstReady, firstCorrect⟩ := first
  obtain ⟨secondMap, secondReady, secondCorrect⟩ := second
  exact ⟨secondMap ∘ firstMap, secondReady.comp firstReady,
    fun word => (firstCorrect word).trans (secondCorrect (firstMap word))⟩

/-- Membership in P uses a total deterministic polynomial-time decider. -/
def InP (language : Language Letter) : Prop :=
  ∃ decision : Word → Bool, PolynomialTime id encodeBool decision ∧
    ∀ word, decision word = true ↔ word ∈ language

/-- Membership in NP uses polynomial-length witnesses and a total deterministic
polynomial-time verifier. The verifier must reject malformed pair encodings;
the membership equivalence also rules out bounded accepting witnesses for
malformed problem inputs when `language` is a `decodedLanguage`. -/
def InNP (language : Language Letter) : Prop :=
  ∃ (verify : Word → Bool) (witnessBound : Polynomial ℕ),
    PolynomialTime id encodeBool verify ∧
    (∀ word, decodePair word = none → verify word = false) ∧
    ∀ input, input ∈ language ↔
      ∃ witness : Word, witness.length ≤ witnessBound.eval input.length ∧
        verify (encodePair (input, witness)) = true

/-- Every NP language has a polynomial many-one reduction to this language. -/
def NPHard (language : Language Letter) : Prop :=
  ∀ source : Language Letter, InNP source → ManyOneReducible source language

/-- NP-completeness combines membership in NP with polynomial many-one hardness. -/
def NPComplete (language : Language Letter) : Prop := InNP language ∧ NPHard language

/-- Certified reductions transfer hardness without any assumption that P and
NP are distinct. -/
theorem NPHard.of_reduction {source target : Language Letter}
    (hard : NPHard source) (reduction : ManyOneReducible source target) : NPHard target :=
  fun language membership => (hard language membership).trans reduction

end Polytime2.Complexity
