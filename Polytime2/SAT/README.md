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
Encodings and polynomial-time certificates are separate later work.
