# Markdown

- Always do a minimal amount of edits in the text with minimal amount of
  addition.
- Always fix typos and correct grammar when you notice them.
- All markdown must be line wrapped at 80 columns.

# Lean coding style

- Name every Lean section and close it with a matching named `end`; avoid bare
  `end` commands where possible.
- Make names traceable: use explicit names and declarations whenever possible,
  including for universe levels and implicit parameters.
- Add Lean definitions and theorems only when needed by concrete examples;
  avoid speculative additions.
- Avoid introducing new Lean structures; keep their number to the absolute
  minimum. Always try to reuse Lean structures from Mathlib.
- When a structure or theorem or any other artifact is no longer needed or
  used, then remove it and its documentation.

# Mathematical interfaces

- Write the intended mathematical input, output, and preconditions before
  implementing or certifying an algorithm. Review that statement independently
  of the chosen machine implementation.
- Public carriers should use ordinary mathematical types: matrices, functions,
  finite sets, sums, and dependent pairs. Keep Boolean masks, numbered tags,
  flattened storage, and padding inside codecs when they only serve storage.
- Public size parameters should describe the mathematical instance. Derive
  counter capacities, scratch widths, and temporary dimensions internally.
  Explicit bit widths remain appropriate for operations on mathematical words.
- Public preconditions should express mathematical admissibility. Hide
  requirements arising only from implementation, such as an extra shift bit,
  by preparing sufficient internal storage.
- Return actual mathematical outcomes. Keep search sentinels internal, and
  use sums or options for alternatives. Do not expose invalid result cases
  merely because correctness later proves they cannot occur.
- Specialization-fixed operations should take ordinary mathematical functions.
  Avoid exposing vacuous size assignments or controller choices to callers.
- In Polytime2, retain canonical binary encodings and exact polynomial widths.
  A more natural carrier should reuse the existing codec through an appropriate
  equivalence whenever its canonical bits can remain unchanged.

# Reuse and consolidation

- Before adding a machine, codec, adapter, or realization proof, search for
  existing infrastructure that implements its constituent operations. Prefer
  composition and specialization over a separate implementation.
- Application proofs should use mathematical composition rules. Keep tape
  wiring, scratch preservation, raw bit manipulation, and codec unfolding in
  foundational realization proofs.
- Before repeating a width, encoding, or transport argument, check whether a
  lemma for arrays, products, records, or parameter substitution can express it.
  Add missing constructor lemmas when concrete callers need them.
- When two proofs share the same argument except for element domains, size
  names, or an encoding-preserving conversion, generalize the existing theorem
  and derive both cases from it.
- Introduce a reusable component together with migrations of the existing
  callers that motivated it. Remove superseded implementations, adapters,
  lemmas, and documentation in the same change.
- For consolidation, identify the code being replaced and report the net Lean
  line change, including new infrastructure. Added functionality may increase
  code size; distinguish that from a simplification.
- Before finishing, inspect the exported statements for implementation details
  and the changed proofs for duplicated infrastructure. Run appropriate Lean
  checks and remove completed README next steps.
