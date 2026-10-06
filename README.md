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

Add framework modules under `Polytime/` and import them in `Polytime.lean` so
the default build includes them. `Polytime.Basic` currently provides a
documented namespace and a minimal Mathlib import. Computation models,
polynomial bounds, and certificate interfaces remain future work.

The projects under `temp/` are reference material only. They are excluded from
version control and are not dependencies of this library.
