# LatticeProbAudit Comparator Surface

This directory contains Mathlib-only comparator challenges for five principal
theorems of the library.  The modules live under the root `LatticeProbAudit`
(the Lake library of that name), so that they cannot collide with the audit
modules of a repository that requires this library.  Each comparator lives in
its own subdirectory:

| Directory | Result | Checked theorem | Library theorems |
| --- | --- | --- | --- |
| `Kingman/` | Kingman's subadditive ergodic theorem | `LatticeProbAudit.kingman` | `LatticeProb.ae_tendsto_div`, `LatticeProb.tendsto_integral_div` |
| `GFF/` | the discrete Gaussian free field with zero boundary values | `LatticeProbAudit.gff` | `LatticeProb.Network.killedGreenMatrix_posSemidef`, `LatticeProb.Network.integral_gff`, `LatticeProb.Network.covariance_gff` |
| `BinomialLocalCLT/` | the binomial local central limit theorem with a `1/m` error | `LatticeProbAudit.binomial_local_clt` | `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT` |
| `BerryEsseen/` | one-dimensional Berry-Esseen for independent non-identical summands | `LatticeProbAudit.berry_esseen_one_dim` | `LatticeProb.berryEsseen_oneDim` |
| `NormalComparison/` | Gaussian orthant comparison with nonnegative correlations | `LatticeProbAudit.normal_comparison` | `LatticeProb.normalComparison_exists` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  [`DESIGN.md`](DESIGN.md) describes the files
of a pair and how the solutions are glued to the library.

## What Is Checked

None of the five comparator statements rests on a cited result, so no challenge carries a
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

- **`BerryEsseen`**: an absolute positive constant bounds the distribution-function
  error for every finite family of centred probability laws, integrable third
  absolute moments and positive total variance. The sum law is the image of
  the product measure under the coordinate sum.
- **`NormalComparison`**: an absolute positive constant bounds the orthant error
  for every dimension, every positive common variance, positive-semidefinite
  covariance with nonnegative entries, and every real threshold vector.
  Singular covariances are included.

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
- `GFF/Solution.lean` imports `GFF/SolutionBasic.lean`, a verbatim copy of the
  vocabulary block that imports only Mathlib, rewrites the vocabulary's killed
  Green function into the library's by the bridges of
  `Support/GFFBridge.lean` (the transition kernels agree by induction on
  time), and takes the library's field `LatticeProb.Network.gff G C` as the
  Gaussian measure.
- `BinomialLocalCLT/Solution.lean` is the library theorem itself: its
  statement is the challenge's after unfolding `binomPMF` and
  `gaussianDensity`.

The comparator itself checks, for each pair, that the solution statement is
the challenge statement and that the dependency closure of the solution theorem
matches the challenge's, over Mathlib alone.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash LatticeProbAudit/check_standalone.sh LatticeProbAudit/Kingman/Challenge.lean
bash LatticeProbAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block of
the `GFF` challenge is the same as in `GFF/SolutionBasic.lean`.  The solutions
build with

```bash
lake build LatticeProbAudit
```

To run the comparator itself on one pair, build `LatticeProbAudit` and then,
from the repository root,

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator LatticeProbAudit/Kingman/comparator.json
```

with `GFF` or `BinomialLocalCLT` in place of `Kingman` for any of the five configured pairs; the
tool revisions are pinned in
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) and
listed in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  A pass is the output
`Your solution is okay!`.

**Recorded status.** The historical results below concern Kingman, GFF and
BinomialLocalCLT. No completed run for BerryEsseen or NormalComparison is
asserted here; their newly selected configurations require actual successful
Solution builds and full Lean/nanoda comparator evidence before a pass claim.
All three historical solutions build.  `leanprover/comparator` at commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, with nanoda at
`6ae1f0cd962f081f6c423454c5da729d841236a7` and landrun at
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, printed `Your solution is okay!`
on all three pairs with the nanoda kernel enabled.  Results and the
reproduction command are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The
workflow [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs the same check on request, since the builds are Mathlib-scale and Actions
minutes are spent only when asked for.
