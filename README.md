# polytime

A Lean project developing a reusable framework for polynomial-time algorithms
and their correctness and machine-runtime certificates.

- [GOAL.md](GOAL.md): design requirements.
- [EXAMPLES.md](EXAMPLES.md): target algorithms and building-block libraries.
- [Polytime2](Polytime2/README.md): navigation, topic guides, and proposed next
  tasks.

## Setup and build

Install Lean through Elan, then run from the repository root:

```sh
lake exe cache get
lake build
```

Lean and Mathlib are pinned to `v4.35.0`. The cache command downloads compiled
Mathlib artifacts.

Build the library with `lake build Polytime2`.
Use `import Polytime2` in Lean.

The projects under `temp/` are read-only reference material, excluded from
version control and project dependencies.

## License

Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>.
Licensed under the [Apache License, Version 2.0](LICENSE).
