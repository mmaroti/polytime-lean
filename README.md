# polytime

A Lean library for developing a reusable framework for polynomial-time
algorithms and their complexity certificates.

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

- `Polytime.Size`: N, finitely many named auxiliary parameters, admissibility,
  and polynomial size expressions with automatically derived bounds in N.
- `Polytime.Domain`: recursive Fixed, Product, Sum, and Power domains; their
  mathematical values, exact-width bit encodings, canonical decoders, and
  polynomial-size certificates.
- `Polytime.Examples.Matrices`: K-by-L matrices over a fixed finite carrier,
  including the field `ZMod 5`, with K,L bounded by N.
- `Polytime.Examples.Domains`: checked boundary cases and binary layouts.

For example:

```lean
import Polytime

open Polytime.Examples.Matrices

example : (domain field5).bitWidth context (assignment 3 2 3) = 18 := by
  simp

example : ∃ p : Polynomial ℕ, ∀ a, context.Admissible a →
    (domain field5).bitWidth context a ≤ p.eval a.N :=
  polynomial_size field5
```

A complete assignment determines the exact bit width. Its size parameters are
external indices, not fields encoded in each value. Encodings concatenate
blocks in order from low to high bits; alternatives use a tag and zero padding.
Unused labels and noncanonical padding are rejected.

Mathlib polynomial construction uses noncomputable definitions. This layer
proves representation and size properties; programs, execution costs, and
machine realization remain future work. See [GOAL.md](GOAL.md) for the broader
specification.

The projects under `temp/` are reference material only. They are excluded from
version control and are not dependencies of this library.
