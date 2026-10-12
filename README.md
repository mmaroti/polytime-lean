# polytime

A Lean project developing reusable frameworks for polynomial-time algorithms
and their correctness and machine-runtime certificates.

- [GOAL.md](GOAL.md): shared design requirements and comparison rules.
- [EXAMPLES.md](EXAMPLES.md): target algorithms and building-block libraries.
- [Polytime1](Polytime1/README.md): single-tape implementation, coverage, and
  next steps.
- [Polytime2](Polytime2/README.md): multi-tape implementation, coverage, and
  next steps.

## Setup and build

Install Lean through Elan, then run from the repository root:

```sh
lake exe cache get
lake build
```

Lean and Mathlib are pinned to `v4.34.0`. The cache command downloads compiled
Mathlib artifacts.

Build one implementation with `lake build Polytime1` or `lake build Polytime2`.
Use `import Polytime1` or `import Polytime2` in Lean.

Run `python3 scripts/check_lean.py --build` to check project headers, named
scopes, and proof placeholders before building. Add `--target Polytime1` or
`--target Polytime2` for a targeted build; omit `--build` for source checks
only.

The projects under `temp/` are read-only reference material, excluded from
version control and project dependencies.

## License

Copyright (c) 2026 Miklos Maroti <mmaroti@math.u-szeged.hu>.
Licensed under the [Apache License, Version 2.0](LICENSE).
