# Lean project

The Lean project of a Mathathon 2026 (Round 1) submission. Toolchain: `leanprover/lean4:v4.35.0`,
Mathlib pinned in `lake-manifest.json`. Build with `lake exe cache get && lake build`.

`CLAIMED.txt` lists the declarations the report relies on; the report has a table that gives, for
each one, the claim it supports and any difference between the two. The check we ran before
publishing: the project builds, and these declarations use no `sorry`, no `native_decide` and no
axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
