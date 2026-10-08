# polytime

A Lean library for developing a reusable framework for polynomial-time
algorithms and their complexity certificates.

See [GOAL.md](GOAL.md) for the framework design and [EXAMPLES.md](EXAMPLES.md)
for the initial three targets and five additional examples with their
mathematical contracts.

The Lake package is named `polytime`; its Lean library, root module, and
namespace are named `Polytime`. The project lives at the repository root and
provides a library without an executable.

## Setup and build

Install Lean through Elan, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
```

Lean and Mathlib are pinned to `v4.34.0`. The `lake-manifest.json`
records the resolved dependency revisions. Mathlib's cache command downloads
compiled artifacts to avoid rebuilding Mathlib from source.

For an existing checkout with its manifest, `lake exe cache get` followed by
`lake build` is sufficient; `lake update` resolves dependencies again.

## Using the library

Within this project, or another Lake project that depends on `polytime`, use:

```lean
import Polytime
```

The library currently provides:

- `Polytime.Size`: finite contexts of named size parameters, arbitrary natural
  assignments and executable capacity expressions with derived polynomial witnesses.
- `Polytime.Domain`: recursive Fixed, Product, Sum, and Power domains; their
  mathematical values, exact-width bit encodings, canonical decoders, and
  polynomial-size certificates.
- `Polytime.Examples.Matrices`: K-by-L matrices over a fixed finite carrier,
  including the field `ZMod 5`, with independent dimensions K and L.
- `Polytime.Examples.Domains`: checked boundary cases and binary layouts.
- `Polytime.Tuple`: Boolean tuple lookup/update and bounded natural counters
  with canonical padded binary representations.
- `Polytime.Integer`: unsigned and signed binary presentations and exact bounded
  arithmetic with proved output capacities and a Euclidean division contract.
- `Polytime.Frame`: executable size-header parsing and frame preparation, with
  input preservation and polynomial storage proofs.
- `Polytime.Examples.TupleLookup`: a complete lookup/update tape example,
  including frame preparation and a quadratic machine-runtime proof.
- `Polytime.Examples.TupleComposition`: two indexed exchanges in one prepared
  frame, with result transfer, preservation contracts, and a quadratic runtime proof.

`DomainExpression` directly defines its mathematical values (`Value`), exact bit
width (`bitWidth`), codecs (`encode` and `decode`), and polynomial upper bound
(`sizeBound`) by recursion on the expression. The size-bound proof is separate
from the width computation.

Each constructor has one canonical encoding through `BitCodec`, directly to and
from `BitVec` of the exact width. Fixed domains retain their `FixedPresentation`
to identify mathematical values with binary labels.

For example:

```lean
import Polytime

open Polytime.Examples.Matrices

example : (domain field5).bitWidth (assignment 2 3) = 18 := by
  simp

example : ∃ p : Polytime.SizePolynomial context, ∀ a,
    (domain field5).bitWidth a ≤ p.eval a :=
  polynomial_size field5
```

`SizeContext` contains the type of parameter names and a `Fintype` instance.
`SizeAssignment ctx` is a map from those names to natural numbers.
`SizeExpression ctx` is executable syntax for constants, parameters, addition,
multiplication, and fixed natural powers. `SizePolynomial ctx` supplies the
derived Mathlib polynomial witnesses. All names have the same
role: a context may name N, K, and L, with no distinguished N and no imposed
bounds between their values. Power exponents may be any such polynomial,
including constants.

A complete assignment determines the exact bit width. The library derives a
polynomial upper bound in all declared parameters, valid for every assignment.
For example, K-by-L matrices over `ZMod 5` need exactly `3*K*L` bits.
Algorithm certificates measure runtime in one plus the sum of size parameters.

The size parameters are external indices, not fields encoded in each value.
Encodings concatenate blocks in order from low to high bits; alternatives use
a tag and zero padding.
Unused labels and noncanonical padding are rejected.

Capacity expressions evaluate directly; their derived polynomials agree with
that evaluation. Exact domain widths are executable, including `max` for sums.
The tuple example uses Mathlib's deterministic `TM0`, with 32 states and eight
symbols independent of N. Its framed input has a unary size header, replacement
bit, N-bit binary index, field separator, dense tuple bits, and end delimiter.
It prepares its own cursor and returns the selected old bit followed by the
updated tuple within `32 * (N + 1)^2` tape transitions. Zero length admits no
valid index. The composition example transfers the first selected bit into the
second exchange while preserving the first updated tuple and surrounding storage,
within `384 * (K + L + 1)^2` transitions. A general program language and compiler
remain future work.

`Frame.prepare` reads a self-delimiting unary size header followed by canonical
input bits, retains the header, and reserves blank scratch slots of their exact
widths. Its correctness and polynomial storage bound are proved. The generic
preparer and integer arithmetic still require tape-runtime realization proofs;
they are not registered as certified program primitives. Integer storage is
bounded by bit length, rather than numeric magnitude.
See [GOAL.md](GOAL.md) for the broader specification.

The projects under `temp/` are reference material only. They are excluded from
version control and are not dependencies of this library.

## License

Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>.
Licensed under the [Apache License, Version 2.0](LICENSE).
