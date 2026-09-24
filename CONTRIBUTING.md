# Contributing / Building notes

This library is the shared base of several formalization repositories.  New
modules are welcome when a second formalization needs the same object or
theorem; issues and pull requests are welcome too.

## Building locally

```bash
lake exe cache get   # the first time: prebuilt Mathlib oleans
lake build           # build the library
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The three Mathlib-only files
`Audit/LatticeProbAudit/*/Challenge.lean` are the sole exception: each contains
one documented statement-level `sorry`, checked against its completed solution
by `leanprover/comparator`.

## Adding a module

1. **Place it by subject.**  Walk kernels and Green functions on `ℤ^d` go in
   `LatticeProb/Walk/`, the walk on a general graph in `LatticeProb/Graph/`,
   networks in `LatticeProb/Network/`, general probability in
   `LatticeProb/Prob/`, Gaussian objects in `LatticeProb/Gauss/`.  Use a
   namespace under `LatticeProb` that names the subject, as
   `LatticeProb.Network` or `LatticeProb.BinomialLCLT` do, so that short lemma
   names do not collide across modules.
2. **No `sorry` and no `axiom`.**  Every declaration must reduce to
   `propext`, `Classical.choice` and `Quot.sound`;
   `python3 tools/check_axioms.py` checks the whole library.  A result from the
   literature that is not proved here is stated as a `Prop` in
   `LatticeProb/External/`, with its source in the docstring, and every theorem
   that uses it takes it as an explicit hypothesis.
3. **Docstrings.**  The module starts with a `/- ... -/` header that says what
   it proves and how.  Every definition and every theorem meant for use outside
   the module has a `/-- ... -/` docstring stating the result in words and
   formulas; mark the principal result of a module with a bold lead, as
   `/-- **Freedman's inequality.** ... -/`.
4. **Junk values.**  Where a definition divides, truncates or takes a `toReal`,
   the statements that use it carry the hypotheses under which it means what
   it says, and the docstring names the junk value it guards against.
5. **Index it.**  Add the module to `LatticeProb.lean`; a principal theorem
   also goes into the "Contents" section of `README.md` and into
   `LatticeProb/Meta/AxiomsAudit.lean`.
6. **Adapted code.**  A file adapted from another repository keeps its license
   and is listed in `NOTICE` with the source commit.
7. **Downstream pins.**  The dependent repositories require this library at a
   fixed commit.  Renaming or restating a declaration they use breaks them at
   their next bump, so add a new declaration rather than changing one in use.

## Practical notes

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a library-only rebuild, remove the
  build artifacts under `.lake/build/lib/lean/LatticeProb` (and the
  corresponding `.lake/build/ir/LatticeProb`) and re-run `lake build`.
- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.
- **The comparator surface** is `lake build LatticeProbAudit`, with the
  statement check `lake build LatticeProbAudit.StatementRegression`; see
  [`Audit/README.md`](Audit/README.md).
