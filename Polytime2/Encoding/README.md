# Encoded mathematical domains

[Project guide](../README.md) · [Composition](../Computation/README.md)

Start with [EncodedDomain.lean](EncodedDomain.lean). An encoded domain has a
mathematical carrier family, an exact polynomial bit width, a canonical encoder,
and a partial decoder satisfying round-trip laws. Encoders and decoders are
specifications; polynomial-time realization is a separate obligation.

## Choose an existing constructor

| Mathematical data | Starting point |
| --- | --- |
| Finite types, equivalent carriers, subtypes | [EncodedDomain.lean][base] |
| Words, bounded naturals, coordinates, signed integers | [binary], [integers] |
| Arrays and row-major matrices | [EncodedArray.lean][arrays] |
| Products, heterogeneous records, variants | [Records.lean](Records.lean) |
| Ordinary mathematical sums | [Computation/Sums.lean][sums] |
| An index with a dependent payload | [Dependent.lean](Dependent.lean) |
| A count with an exact-length array | [BoundedArray.lean][bounded] |
| Bounded cyclic/free coordinates and their modulus | [Cyclic.lean][cyclic] |

[cyclic]: Cyclic.lean
[base]: EncodedDomain.lean
[binary]: BinaryEncoding.lean
[integers]: Integers.lean
[arrays]: EncodedArray.lean
[sums]: ../Computation/Sums.lean
[bounded]: BoundedArray.lean

`arrayOfLength_encode_surjective` lifts total use of bit patterns from an
element codec to its array codec. The shared
[fixed-array decoder](../Computation/FixedArrayDecode.lean) uses it to frame
raw bits into blocks before validating the finite carrier codes.
`array_encode_surjective`, `prod_encode_surjective`,
`record_encode_surjective`, `namedRecord_encode_surjective`, and
`reindex_encode_surjective` provide the corresponding constructor rules.
`encode_surjective_iff_decode_total` converts encoder surjectivity to decoder
totality and back. The [CSP instance codec](../CSP/Encoding.lean) uses these
rules structurally, including empty records, empty arrays, and zero widths.

`boundedArrayConvert_bits` lifts equal-width, encoding-preserving element
conversions to stored arrays at equal capacities. Counts and inactive padding
are preserved. Stored-field and parameter-renaming adapters share this rule.

Use ordinary mathematical carriers in public interfaces. Reuse an existing codec
through `reindex` when an equivalence preserves its bits. `restrict` retains the
encoding of each admitted value and rejects excluded words. Coordinate codecs
use their mathematical bounds; their exact width need not be logarithmic.

Record fields concatenate directly. Variants store a discriminator and all
alternative fields, with zero bits in inactive fields; decoding rejects invalid
inactive storage. Use the sum interface when callers need ordinary alternatives.
Dependent codecs retain the actual mathematical payload and reject noncanonical
capacity padding. These storage details belong inside codecs.

## Widths and parameter changes

Exact multivariate polynomials determine current widths. Their certified unary
evaluation is in [PolynomialEvaluator.lean](PolynomialEvaluator.lean), including
`EncodedDomain.width_computable`. Public sizes describe the instance; derive
scratch capacities and temporary widths internally.

Use [ParameterRename.lean](ParameterRename.lean) and
[SizeSubstitution.lean](SizeSubstitution.lean) for parameter transport. Check
constructor lemmas for arrays, products, records, and canonical words before
unfolding encoders or repeating casts. The
[specialization
rules](../Computation/README.md#change-mathematical-representations)
then transport realizability between mathematical domains.

`renameParameters_id`, `renameParameters_comp`, `substitute_id`, and
`substitute_comp` normalize successive parameter changes; `substitute_X`
identifies variable substitution with direct renaming. Renaming also commutes
with fixed codecs, products, records, named arrays, and optional codecs.
For dependent values, use `renameParameters_comp_bits` or
`encode_bits_cast_sizes` instead of rewriting their entire codec.

`ArrayEncoding.bits_encode_congr_entries`, `prod_encode_bits_congr`, and
`record_encode_bits_congr` lift pointwise conversions to complete words.
The existing optional and bounded-array conversion rules also preserve inactive
padding. `ext_of_encode_bits` identifies complete codecs from equal carriers,
exact width polynomials, and canonical bits; width equality remains a separate
obligation even for empty carriers.

A possible future generalization is a width function with a certified
polynomial-time unary evaluator. A polynomial upper bound alone does not supply
the operational width computation needed by generic tape algorithms. The current
interfaces continue to require exact polynomial widths.

## Examples and boundaries

[Word.lean](Word.lean) presents canonical fields as external binary letters.
Its decoder rejects nonbinary symbols, incorrect widths, and invalid codec
values. Both round trips are proved; polynomial-time parsing remains a
separate realization obligation.

`decodeBinaryWord` isolates strict binary-letter validation, and
`decodeWord_eq_decodeBinaryWord` factors canonical field decoding through it.
The [binary decoder](../Complexity/BinaryDecoder.lean) certifies this first
stage; exact-width checks and domain-specific validation remain separate.

[EncodedDomains.lean](../Examples/EncodedDomains.lean) illustrates domains;
[Records.lean](../Examples/Records.lean) exercises records, sums, runtime
widths,
empty carriers, zero-width payloads, and rejection of invalid words.

Signed codec conventions are documented in [Integers.lean](Integers.lean).
Use the [arithmetic guide](../Arithmetic/README.md) for algorithms on those
values, and [computed-size
composition](../Computation/README.md#sizes-and-loops)
for consumers of dependent payloads.
