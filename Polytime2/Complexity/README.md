# Polynomial word complexity

[Project guide](../README.md) · [TM0 export](../TM0/README.md)

[PolynomialTime.lean](PolynomialTime.lean) certifies functions between specified
word encodings with finite Mathlib TM0 machines. `PolynomialTime id id f`
certifies a total word function. One polynomial bounds both transitions and
output length in the complete input word length. `PolynomialTime.id` and
`PolynomialTime.comp` provide identity and composition.

[Languages.lean](Languages.lean) defines polynomial `ManyOneReducible`, `InP`,
`InNP`, `NPHard`, and `NPComplete` using Mathlib word languages. Use
`ManyOneReducible.trans` to compose reductions and `NPHard.of_reduction` to
transfer hardness. These interfaces do not assume SAT hardness or P != NP.
`decodedLanguage` excludes failed decodings explicitly.

NP witnesses are words with a polynomial length bound. The total deterministic
verifier receives `encodePair (input, witness)`, whose exact length includes
the unary input-length header. `decodePair_encodePair` gives the round trip;
the NP contract requires rejection of malformed pair encodings.

[Realizable.lean](Realizable.lean) connects existing computation certificates:

- `ready.polynomialTime` certifies the function between `inputWord` and
  `outputWord` on `computation.AdmissibleInput`.
- `ready.wordFunction` additionally takes a certified total parser/normalizer
  from arbitrary words to admissible inputs.
- `ManyOneReducible.of_realizable` packages the resulting total word function
  with the caller's all-word membership equivalence.

The parser must handle malformed words, and the membership proof must cover
them. An admissible-input certificate alone does not supply a parser or justify
a total word reduction. The size-to-length bridge uses existing unary headers
and exact output widths, including zero sizes and empty parameter families.

[WordArrays.lean](WordArrays.lean) supplies `ready.onWordArrays` for total
Boolean decisions on ordinary arrays of external letters. Use `letterDomain`
for the fixed alphabet codec. The rule includes arbitrary raw-input
preparation, unary length discovery, simulation, and Boolean output cleanup in
one word-length polynomial. There is no framing precondition, including for
the empty word. The caller must still certify its parsing and decision
computation. [RawWords.lean](RawWords.lean) owns the intermediate Boolean-track
entry rule; application parsers need no physical track representation.
Use `ready.onWordDecision` when the specification already gives the answer as
a function of `List.ofFn letters`; this rule handles the length transport.

[UnaryHeader.lean](UnaryHeader.lean) certifies the first non-count position
using the existing finite predicate, array map, and first-false scan. Its
contract agrees with `readPairHeader` on successful headers and handles
missing boundaries. `unaryPrefixLength` returns the actual prefix length,
including the full length for an all-count-symbol word. The count-symbol scan
is shared with payload validation.
[HeaderValidation.lean](HeaderValidation.lean) adds checked
separator lookup and proves `unaryHeaderValid_correct` on all words. Its
`readPairHeader_isSome_polynomialTime` includes raw-word preparation and rejects
missing or incorrect separators. Payload bounds and field decoding remain
separate obligations.

[PairValidation.lean](PairValidation.lean) adds the announced input-length
bound. `pairValid_realizable` certifies the complete pair-validity decision,
and `decodePair_isSome_polynomialTime` exports it on all words. This validates
framing, including truncation; extraction of the two actual fields and their
domain decoding still require certified computations.

[PairFields.lean](PairFields.lean) supplies `pairFields_realizable` for
extraction at an announced count whose payload fits. `pairFields_decodePair`
identifies its exact output arrays with `decodePair` when that count is the
parsed header count. It reuses array slicing and derived-width arithmetic.
[PairParser.lean](PairParser.lean) prepares the count and guards extraction.
`pairParser_realizable` certifies this total parser; `pairParser_correct`
identifies both successful output fields and failed parses with `decodePair`.
The fields still require their application-specific domain decoding.

[HeaderParser.lean](HeaderParser.lean) parses a unary count and its complete
remaining payload, including empty payloads. `headerParser_correct` identifies
accepted and rejected results with `readPairHeader` on all words. It shares
`afterPrefix` and guarded optional execution with the pair parser. Unlike pair
framing, this parser permits any count before a valid separator; no second
count-sized field is required.

[UnarySize.lean](UnarySize.lean) prepares the leading count-symbol prefix in
the bounded unary codec used by computed-size calls. `fieldUnaryHeaderSize`
executes it at a stored field's actual length and retains that length.
Its parsed-header contract identifies the result with the exact parsed count;
separator validation remains separate.
`fieldVariableCount` retains this value in the caller's unary capacity,
discarding the internal actual-length frame without changing the count.

[HeaderPayload.lean](HeaderPayload.lean) composes strict header parsing with
suffix extraction and host-capacity retention. `headerPayloadAtHost_correct`
identifies the optional exact suffix on all words at a supplied field length;
malformed headers reject and capacity padding contributes no letters. Calling
it at a stored field's actual length is certified in
[StoredHeaderPayload.lean](StoredHeaderPayload.lean). `storedHeaderPayload`
uses the stored count and the computed-host call rule, returning an optional
exact suffix in the original host codec. Its correctness theorem covers all
stored fields, including empty fields and malformed headers.

[BinaryDecoder.lean](BinaryDecoder.lean) certifies strict binary-letter
decoding to an optional exact-length Boolean array. Its contract agrees with
`EncodedDomain.decodeBinaryWord`, through which canonical `decodeWord`
factors. Nonbinary symbols reject. Domain widths and finite-carrier code
validation remain separate obligations. `storedBinaryWordDecoder` applies the
same validation at a stored field's actual length and retains its exact count
within the host capacity. Its correctness theorem identifies the optional
output contents with strict binary-word decoding.

[StoredFieldDecode.lean](StoredFieldDecode.lean) composes strict binary-letter
validation, an exact target-width guard, extraction, and a supplied
`decodeCanonicalBits` certificate. `decodeStoredWord_correct` agrees with
`domain.decodeWord` on every stored word, including invalid letters, wrong
lengths, and invalid scalar codes. `decodeStoredBits` supplies the Boolean-field
stage; `readStoredBits` exposes partial exact extraction with precisely the
stored-length equality as its precondition. Dense instances use the full-codec
certificate; CSP witnesses use the fixed-array certificate. Capacity padding
never contributes mathematical elements, and no inhabitance is required.

Foundational alphabet transport and counted sequencing are in
[TM0/WordComposition.lean](../TM0/WordComposition.lean). Application proofs use
the public composition and bridge rules instead of constructing machines.

The [CSP verifier](../CSP/VerifierRealizable.lean) is a complete application of
`onWordDecision`, composing both parsers, strict field decoders, a computed
variable-count call, and the assignment checker before proving membership in NP.

[Cook-Levin foundations](CookLevin/README.md) develop the bounded-machine
circuit construction. `verifier_circuits_uniform` includes the complete
polynomial-time constructor, canonical serialization, polynomial gate bounds,
and correctness on every Boolean assignment. Certified Tseitin conversion
and SAT hardness remain separate tasks.
