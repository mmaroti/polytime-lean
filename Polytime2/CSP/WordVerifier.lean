import Polytime2.CSP.Checker
import Polytime2.Encoding.Word

/-! # Word representation and witness contract for finite-template CSP

An instance word is a unary variable-count header followed by exactly the
canonical dense instance bits. A witness is exactly the canonical assignment
bits at that count. No alternate widths, nonbinary field symbols, or padding
are accepted. The verifier first parses the input/witness pair, then both
fields, and finally checks the proposed assignment.

This module proves the mathematical acceptance and polynomial witness-length
contracts. The total word verifier's runtime certificate is a separate proof.
-/

set_option backward.isDefEq.respectTransparency false

namespace Polytime2.CSP

open FirstOrder FirstOrder.Language Complexity

variable (L : FirstOrder.Language.{0, 0}) [L.IsRelational] [Fintype (RelationSymbol L)]

/-- A variable count paired with an actual finite relational instance. -/
abbrev SizedInstance := Σ variableCount : ℕ, Instance L variableCount

/-- Unary count followed by canonical dense tables, including nullary bits. -/
noncomputable def instanceWord (input : SizedInstance L) : Word :=
  List.replicate input.1 (.inr 1) ++ .inr 0 :: (instanceDomain L).word (fun _ => input.1) input.2

/-- Reject malformed headers and any noncanonical instance field. -/
noncomputable def decodeInstanceWord (word : Word) : Option (SizedInstance L) := do
  let (variableCount, field) ← readPairHeader word
  let input ← (instanceDomain L).decodeWord (fun _ => variableCount) field
  pure ⟨variableCount, input⟩

@[simp] theorem decodeInstanceWord_instanceWord (input : SizedInstance L) :
    decodeInstanceWord L (instanceWord L input) = some input := by
  rcases input with ⟨variableCount, input⟩
  simp [decodeInstanceWord, instanceWord, readPairHeader_prefix]

theorem instanceWord_decodeInstanceWord (word : Word) (input : SizedInstance L)
    (accepted : decodeInstanceWord L word = some input) : instanceWord L input = word := by
  unfold decodeInstanceWord at accepted
  cases header : readPairHeader word with
  | none => simp [header] at accepted
  | some pair =>
    rcases pair with ⟨variableCount, field⟩
    cases decoded : (instanceDomain L).decodeWord (fun _ => variableCount) field with
    | none => simp [header, decoded] at accepted
    | some value =>
      simp [header, decoded] at accepted
      subst input
      have canonical := (instanceDomain L).word_decodeWord (fun _ => variableCount) field value decoded
      simpa [instanceWord, canonical] using (readPairHeader_canonical header).symm

theorem variableCount_le_instanceWord_length (input : SizedInstance L) :
    input.1 ≤ (instanceWord L input).length := by
  simp [instanceWord]

variable (Carrier : Type) [Fintype Carrier] [L.Structure Carrier]

/-- Assignments use actual carrier values and the existing canonical codec. -/
noncomputable def assignmentWord (variableCount : ℕ) (assignment : Fin variableCount → Carrier) : Word :=
  (assignmentDomain Carrier).word (fun _ => variableCount) assignment

theorem assignmentWord_length (variableCount : ℕ) (assignment : Fin variableCount → Carrier) :
    (assignmentWord Carrier variableCount assignment).length =
      variableCount * Nat.clog 2 (Fintype.card Carrier) := by
  change ((assignmentDomain Carrier).word (fun _ => variableCount) assignment).length = _
  rw [EncodedDomain.word_length]
  simp [EncodedDomain.width, assignmentDomain_widthPolynomial]

/-- The fixed-template word language rejects failed instance decoding. -/
noncomputable def language : Language Letter :=
  decodedLanguage (decodeInstanceWord L) (fun input => Instance.Satisfiable L input.2 Carrier)

/-- Check exact instance-table and assignment words at a fixed variable count.
Every decoding failure rejects; successful fields use the mathematical checker. -/
noncomputable def tableWordVerifier (variableCount : ℕ) (tables witness : Word) : Bool :=
  match (instanceDomain L).decodeWord (fun _ => variableCount) tables,
    (assignmentDomain Carrier).decodeWord (fun _ => variableCount) witness with
  | some input, some assignment =>
    (assignmentChecker L Carrier).compute (fun _ => variableCount)
      ⟨(fun choice => match choice with | false => input | true => assignment), trivial⟩
  | _, _ => false

/-- Mathematical total verifier: parse the pair and the instance header, then
check both exact field codes and the proposed homomorphism. -/
noncomputable def wordVerifier (word : Word) : Bool :=
  match decodePair word with
  | none => false
  | some (inputWord, witness) =>
    match readPairHeader inputWord with
    | none => false
    | some (variableCount, tables) => tableWordVerifier L Carrier variableCount tables witness

/-- Factoring header and table checks preserves the canonical instance-decoder
specification and every malformed-input rejection branch. -/
theorem wordVerifier_decodeInstance (word : Word) :
    wordVerifier L Carrier word =
  match decodePair word with
  | none => false
  | some (inputWord, witness) =>
    match decodeInstanceWord L inputWord with
    | none => false
    | some ⟨variableCount, input⟩ =>
      match (assignmentDomain Carrier).decodeWord (fun _ => variableCount) witness with
      | none => false
      | some assignment =>
        (assignmentChecker L Carrier).compute (fun _ => variableCount)
          ⟨(fun choice => match choice with | false => input | true => assignment), trivial⟩ := by
  cases paired : decodePair word with
  | none => simp [wordVerifier, paired]
  | some pair =>
    rcases pair with ⟨inputWord, witness⟩
    cases header : readPairHeader inputWord with
    | none => simp [wordVerifier, paired, decodeInstanceWord, header]
    | some pair =>
      rcases pair with ⟨count, tables⟩
      cases decoded : (instanceDomain L).decodeWord (fun _ => count) tables <;>
        simp [wordVerifier, paired, header, tableWordVerifier, decodeInstanceWord, decoded]
      cases (assignmentDomain Carrier).decodeWord (fun _ => count) witness <;> rfl

/-- The verifier depends only on a successful outer pair parse, and rejects
failed parses. This form is convenient for certified parser composition. -/
theorem wordVerifier_pairElim (word : Word) :
    wordVerifier L Carrier word = (decodePair word).elim false
      (fun pair => wordVerifier L Carrier (encodePair pair)) := by
  cases paired : decodePair word with
  | none => simp [wordVerifier, paired]
  | some pair =>
    rcases pair with ⟨input, witness⟩
    simp [wordVerifier, paired, decodePair_encodePair]

theorem wordVerifier_malformed_pair (word : Word) (malformed : decodePair word = none) :
    wordVerifier L Carrier word = false := by simp [wordVerifier, malformed]

/-- A correctly encoded witness has precisely its mathematical checker answer. -/
theorem wordVerifier_valid (input : SizedInstance L) (assignment : Fin input.1 → Carrier) :
    wordVerifier L Carrier (encodePair (instanceWord L input, assignmentWord Carrier input.1 assignment)) = true ↔
      Preserves L Carrier input.1 input.2 assignment := by
  rw [wordVerifier_decodeInstance]
  simp only [decodePair_encodePair, decodeInstanceWord_instanceWord,
    assignmentWord]
  rw [EncodedDomain.decodeWord_word]
  exact assignmentChecker_correct L Carrier (fun _ => input.1)
    (fun choice => match choice with | false => input.2 | true => assignment)

/-- Linear witness bound in the complete instance-word length. -/
noncomputable def witnessBound : Polynomial ℕ :=
  Polynomial.C (Nat.clog 2 (Fintype.card Carrier)) * Polynomial.X

/-- CSP membership is exactly existence of a bounded accepting witness. This
includes arbitrary malformed input words and requires no inhabited template. -/
theorem wordVerifier_witnesses (word : Word) :
    word ∈ language L Carrier ↔ ∃ witness : Word,
      witness.length ≤ (witnessBound Carrier).eval word.length ∧
        wordVerifier L Carrier (encodePair (word, witness)) = true := by
  constructor
  · rintro ⟨⟨variableCount, input⟩, decoded, satisfiable⟩
    obtain ⟨assignment, preserves⟩ := (satisfiable_iff_exists_preserves L Carrier variableCount input).mp satisfiable
    have canonical := instanceWord_decodeInstanceWord L word ⟨variableCount, input⟩ decoded
    rw [← canonical]
    refine ⟨assignmentWord Carrier variableCount assignment, ?_, ?_⟩
    · have bound := Nat.mul_le_mul_right (Nat.clog 2 (Fintype.card Carrier))
        (variableCount_le_instanceWord_length L ⟨variableCount, input⟩)
      simpa [assignmentWord_length, witnessBound, Nat.mul_comm] using bound
    · exact (wordVerifier_valid L Carrier ⟨variableCount, input⟩ assignment).mpr preserves
  · rintro ⟨witness, _, accepted⟩
    rw [wordVerifier_decodeInstance] at accepted
    simp only [decodePair_encodePair] at accepted
    cases decoded : decodeInstanceWord L word with
    | none => simp [decoded] at accepted
    | some input =>
      rcases input with ⟨variableCount, input⟩
      cases assigned : (assignmentDomain Carrier).decodeWord (fun _ => variableCount) witness with
      | none => simp [decoded, assigned] at accepted
      | some assignment =>
        simp only [decoded, assigned] at accepted
        refine ⟨⟨variableCount, input⟩, decoded, ?_⟩
        apply (satisfiable_iff_exists_preserves L Carrier variableCount input).mpr
        exact ⟨assignment, (assignmentChecker_correct L Carrier _ _).mp accepted⟩

end Polytime2.CSP
