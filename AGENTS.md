# Markdown

- Always do a minimal amount of edits in the text with minimal amount of
  addition.
- Always fix typos and correct grammar when you notice them.
- All markdown must be line wrapped at 80 columns.

# Lean style

- Name every Lean section and close it with a matching named `end`; avoid bare
  `end` commands where possible.
- Make names traceable: use explicit names and declarations whenever possible,
  including for universe levels and implicit parameters.
- Add Lean definitions and theorems only when needed by concrete examples;
  avoid speculative additions.
- Avoid introducing new Lean structures, keep their number to the absolute
  minimum. Always try to reuse Lean structures from Mathlib.
- When a structure or theorem or any other artifact is no longer needed or 
  used, then remove it and its documentation.
- Always formalize the most mathematically natural and reusable encoding of
  domains and problems, and not the one that is the easiest to implement.
- Make reusable components. Actively rewrite proofs if it can be shortened
  by using newly introduced components.
