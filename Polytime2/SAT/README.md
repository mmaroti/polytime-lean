# Three-literal Boolean formulas

[Project guide](../README.md) · [CSP](../CSP/README.md)

[ThreeSAT.lean](ThreeSAT.lean) supplies shared literals, clauses, and formulas
and their satisfaction predicates. Literals are variable/negation-bit
pairs, clauses are ordered triples, and formulas are lists. The polarity
convention and exact contracts are in the declaration docstrings.

The library covers the empty conjunction, repeated literals, and changes to
unused variables. The [relational interpretation](../CSP/ThreeSAT.lean) proves
equivalence with the eight-relation Boolean CSP. Reuse these definitions for
the planned [3-SAT-to-CLIQUE reduction](../tasks/3-sat-to-clique.md).
`Formula.satisfiable_ofFn_rename` transports satisfiability of clause arrays
along injective variable renamings. The canonical clause-array interface uses
it to forget variable bounds.

[Tseitin.lean](Tseitin.lean) converts shared-wire NAND circuits to these
clauses. `tseitin_correct` proves both witness directions; `tseitin_length`
gives exactly three clauses per gate plus one output clause. `tseitin_variables`
bounds every variable by the circuit's wire count. These are mathematical
proofs. The [clause-array bridge][clauses csp] gives the corresponding
eight-relation CSP instance on the actual finite wire set.

[TseitinProgram.lean](TseitinProgram.lean) certifies the complete conversion
on canonical bounded circuit inputs. Its mathematical specification is exactly
`tseitin`, and `tseitinProgram_polynomialTime` includes input preparation and
serialized clause output. Acyclicity is required for the satisfiability
equivalence, rather than for emission itself. Fixed templates and array
tabulation use the existing product, sum, record, and coordinate codecs.

[FixedInputs.lean](FixedInputs.lean) proves that appending unit clauses fixes
exactly a supplied input prefix; its finite-array theorem avoids list-length
transports at circuit callers.
[FixedInputsProgram.lean](FixedInputsProgram.lean)
certifies construction in the same canonical clause codec.
[FormulaSubstitution.lean](FormulaSubstitution.lean) moves polynomial
specialization inside that codec without changing a bit or variable value.

[FixedFormulaProgram.lean][fixed formulas] assembles the complete verifier
formula with the framed instance fixed and its witness existential. It exposes
`np_formulas_uniform`, including certified construction and exact membership
through satisfiability. The [complete word reduction][reduction] certifies
NP-completeness of the existing relational three-SAT language.

[clauses csp]: ../CSP/ThreeSATClauses.lean
[fixed formulas]: ../Complexity/CookLevin/FixedFormulaProgram.lean
[reduction]: ../Complexity/CookLevin/Reduction.lean
