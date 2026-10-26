# Relational CSP foundations

[Project guide](../README.md)

[Basic.lean](Basic.lean) states the fixed-template hardness contract and defines
Taylor operations, relation-preserving polymorphisms, and rigid cores using
Mathlib's first-order structures and homomorphisms. It also proves that
singleton unary relations imply rigidity and that reflexive templates admit
constant homomorphisms.

These are mathematical definitions and proofs. Encoded instance domains,
solvers, reductions, and NP-completeness are not implemented yet. The
[hardness task](../tasks/csp-taylor-hardness.md) records the remaining steps.
The target problems and instance representation live in
[EXAMPLES.md](../../EXAMPLES.md#further-application-fixed-template-csp).
