# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for three principal
theorems of the library.  The modules live under the root `LatticeProbAudit`
(the Lake library of that name, with source directory `Audit/`), so that they
cannot collide with the `Audit.*` modules of a repository that requires this
library.  Each comparator lives in its own subdirectory:

| Directory | Result | Checked theorem | Library theorems |
| --- | --- | --- | --- |
| `LatticeProbAudit/Kingman/` | Kingman's subadditive ergodic theorem | `LatticeProbAudit.kingman` | `LatticeProb.ae_tendsto_div`, `LatticeProb.tendsto_integral_div` |
| `LatticeProbAudit/GFF/` | the discrete Gaussian free field with zero boundary values | `LatticeProbAudit.gff` | `LatticeProb.Network.killedGreenMatrix_posSemidef`, `LatticeProb.Network.integral_gff`, `LatticeProb.Network.covariance_gff` |
| `LatticeProbAudit/BinomialLocalCLT/` | the binomial local central limit theorem with a `1/m` error | `LatticeProbAudit.binomial_local_clt` | `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.

## What Is Checked

None of the three theorems rests on a cited result, so no challenge carries a
hypothesis beyond the mathematical ones.

- **`Kingman`**: let `T` preserve a finite measure `μ`, and let `g n` be
  measurable, integrable, subadditive along `T`
  (`g (m + n) x ≤ g m x + g n (T^m x)`) and bounded below by `c n`.  Then
  almost everywhere `g n x / n` converges to a finite limit, and
  `(∫ g n) / n` converges to its infimum over `n ≥ 1`.  No definition is
  needed: subadditivity is written out.
- **`GFF`**: on a connected locally finite graph, for a finite set `C` that
  misses some vertex, the killed Green function `g_C` restricted to `C × C` is
  positive semidefinite, and some centred Gaussian measure on `ℝ^C` has
  covariance `g_C`.
- **`BinomialLocalCLT`**: there is `C` such that for every `m ≥ 1` and every
  integer `j` with `|j| ≤ m` and `j ≡ m (mod 2)`,
  `|√m · C(m, (m + j)/2) / 2^m − 2 φ(j/√m)| ≤ C/m`, with `φ` the standard
  normal density written out.  No definition is needed.

## Definition Provenance

Only the `GFF` challenge defines anything.  Its definitions form one
vocabulary block, between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, in the
namespace `LatticeProbAudit`; they are statement-level copies of the library's.

| Challenge declaration | Library source |
| --- | --- |
| `walkOp` | `LatticeProb.Graph.walkOp`, `LatticeProb/Graph/Basic.lean` |
| `killedHeat` | `LatticeProb.Graph.killedHeat`, `LatticeProb/Graph/Basic.lean` |
| `killedGreen` | `LatticeProb.Graph.killedGreen`, `LatticeProb/Graph/Basic.lean` |
| `killedGreenReal` | `LatticeProb.Graph.killedGreenReal`, `LatticeProb/Graph/Basic.lean` |

## Solutions

Each `Solution.lean` imports the library and proves the byte-identical
statement:

- `Kingman/Solution.lean` applies `LatticeProb.ae_tendsto_div` and
  `LatticeProb.tendsto_integral_div`, proving the lower bound on the means that
  the second needs from the linear lower bound on `g n`, and unfolds Mathlib's
  `Subadditive.lim` to the infimum.
- `GFF/Solution.lean` imports `Support/Vocabulary.lean`, a verbatim copy of the
  vocabulary block that imports only Mathlib, rewrites the vocabulary's killed
  Green function into the library's by the bridges of `Support/Bridge.lean`
  (the transition kernels agree by induction on time), and takes the library's
  field `LatticeProb.Network.gff G C` as the Gaussian measure.
- `BinomialLocalCLT/Solution.lean` is the library theorem itself: its
  statement is the challenge's after unfolding `binomPMF` and
  `gaussianDensity`.

`LatticeProbAudit/StatementRegression.lean` is a local check of the
statement-identity part of the comparator: it elaborates each statement in the
challenge environment (`Support/Statements.lean`, which imports only Mathlib
and the vocabulary), checks that each solution theorem has exactly that type
and mentions no constant of the library namespace `LatticeProb`, and prints
the axioms of each solution theorem.  A deliberate change to one statement
makes it fail.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/LatticeProbAudit/Kingman/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block of
the `GFF` challenge is the same as in `Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build LatticeProbAudit.StatementRegression
```

which prints, for each of the three theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.  To run the comparator itself on one pair, build
`LatticeProbAudit` and then, from the repository root,

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/LatticeProbAudit/Kingman/comparator.json
```

with `GFF` or `BinomialLocalCLT` in place of `Kingman` for the other pairs; the
tool revisions are pinned in
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) and
listed in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  A pass is the output
`Your solution is okay!`.

**Status.**  All three solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` was run on all three pairs
at commits `bbe0b90` and `2d30e98`, and every pair passed with the Lean kernel
and again with the independent nanoda kernel enabled.  Results and the
reproduction command are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The
workflow [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs the same check on request, since the builds are Mathlib-scale and Actions
minutes are spent only when asked for.
