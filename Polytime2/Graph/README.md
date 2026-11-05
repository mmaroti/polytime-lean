# Finite graphs and clique reductions

[Project guide](../README.md)

[ThreeSATClique.lean](ThreeSATClique.lean) defines the simple occurrence graph
of a three-literal clause array. `assignmentClique_isNClique` transports a
satisfying assignment to a clique of exactly the clause count.
`cliqueAssignment_satisfied` constructs a satisfying assignment from any such
clique, assigning false to variables without selected positive occurrences.
`satisfiable_iff_occurrence_clique` combines both directions, including zero
clauses and repeated literals.

[Encoding.lean](Encoding.lean) encodes ordinary Mathlib simple graphs by dense
adjacency matrices, rejecting loops and asymmetric tables. The shared
[finite-subset codec](../Encoding/FiniteSubsets.lean) encodes ordinary finsets
by their membership bits without exposing masks as mathematical witnesses.

[WitnessSelection.lean](WitnessSelection.lean) certifies the three-way true
literal selector by a fixed finite table. The
[subset operations](../Arrays/FiniteSubsets.lean) certify membership and
construction of ordinary finite subsets through existing lookup and copy.

[LiteralEvaluation.lean](LiteralEvaluation.lean) certifies literal evaluation
and selection of a true position in every clause under the supplied assignment.
`chooseFormulaPositions_satisfied` connects the computed positions to the
mathematical forward witness.

[ForwardClique.lean](ForwardClique.lean) constructs the actual numbered clique
finset. `forwardClique_compute` identifies it with the mathematical witness,
and `forwardClique_isNClique` proves its validity for satisfying assignments.
`forwardClique_tm0` and `forwardClique_polynomialTime` include construction and
bound execution and witness length in the complete serialized source input.

[LiteralCompatibility.lean](LiteralCompatibility.lean) certifies literal and
clause compatibility. [OccurrenceEdge.lean](OccurrenceEdge.lean) combines clause
lookup with compatibility and the distinct-clause test.
[AdjacencyTables.lean](AdjacencyTables.lean) certifies the complete dense
Boolean adjacency table and proves its entries agree with the occurrence graph.

[Construction.lean](Construction.lean) exports `cliqueGraph`, with an ordinary
`SimpleGraph` output. [ReverseClique.lean](ReverseClique.lean) exports
`reverseClique` and proves that every full-size clique yields a satisfying
assignment. Both computations have realizability, standalone TM0, and
polynomial-time certificates, as does the forward witness.

[Reduction.lean](Reduction.lean) is the combined entry point.
`cliqueGraph_correct` relates satisfiability to a clique of the clause count in
the actual computed graph, using both certified witness algorithms. The graph
has exactly three vertices per clause and nine adjacency bits per ordered
clause pair. Variable and clause counts are independent; occurrence dimensions
are derived internally. `reverseClique_absent` specifies the false value for
variables absent from the formula.
[Examples.lean](Examples.lean) checks empty formulas, zero variables, repeated
literals, opposite occurrences, and unused variables.

The certificates bound execution and result length in the complete serialized
source input, including its size headers and supplied witnesses. Output words
encode the payload at the mathematical size index. The clique threshold is the
source clause count. These results certify a reduction between indexed
mathematical instances; they do not establish CLIQUE membership in NP or an
all-word NP-completeness theorem. See the
[complexity guide](../Complexity/README.md) for those additional word-language
obligations.
