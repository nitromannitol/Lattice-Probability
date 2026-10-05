# LatticeProbAudit Comparator Surface

This directory contains Mathlib-only comparator challenges for eight principal
theorems of the library.  The modules live under the root `LatticeProbAudit`
(the Lake library of that name), so that they cannot collide with the audit
modules of a repository that requires this library.  Each comparator lives in
its own subdirectory:

| Directory | Result | Checked theorem | Library theorems |
| --- | --- | --- | --- |
| `Kingman/` | Kingman's subadditive ergodic theorem | `LatticeProbAudit.kingman` | `LatticeProb.ae_tendsto_div`, `LatticeProb.tendsto_integral_div` |
| `GFF/` | the discrete Gaussian free field with zero boundary values | `LatticeProbAudit.gff` | `LatticeProb.Network.killedGreenMatrix_posSemidef`, `LatticeProb.Network.integral_gff`, `LatticeProb.Network.covariance_gff` |
| `BinomialLocalCLT/` | the binomial local central limit theorem with a `1/m` error | `LatticeProbAudit.binomial_local_clt` | `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT` |
| `NormalComparison/` | the normal comparison inequality of Li and Shao for the orthant, nonnegative correlations | `LatticeProbAudit.normal_comparison` | `LatticeProb.normalComparison_exists` |
| `BerryEsseen/` | the one-dimensional Berry-Esseen theorem for independent non-identical summands | `LatticeProbAudit.berry_esseen_one_dim` | `LatticeProb.berryEsseen_oneDim` |
| `PittGaussianFKG/` | Pitt's Gaussian association theorem: centred Gaussian families with nonnegative covariances are positively associated | `LatticeProbAudit.pitt_gaussian_fkg` | `LatticeProb.pitt_gaussian_fkg` |
| `MultivariateBerryEsseen/` | the multivariate Berry-Esseen comparison for orthants, with the dimension factor `m` | `LatticeProbAudit.multivariate_berry_esseen_orthant` | `LatticeProb.mvbe_frozenShape_linear_unconditional` |
| `MultivariateBerryEsseenQuarter/` | the same comparison with the frozen factor `m^{1/4}` (the frozen `Sandpile.External.MultivariateBerryEsseen`) | `LatticeProbAudit.multivariate_berry_esseen_quarter` | `LatticeProb.mvbe_frozenQuarter_unconditional` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  [`DESIGN.md`](DESIGN.md) describes the files
of a pair and how the solutions are glued to the library.

## What Is Checked

None of the eight theorems rests on a cited result, so no challenge carries a
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
- **`NormalComparison`**: there is `C > 0` such that for every dimension `m`, variance `v > 0`,
  positive semidefinite `S` with constant diagonal `v` and nonnegative entries, and every `b`, the
  centred Gaussian orthant probability `P(Y ≤ b)` differs from `∏ᵢ P(N(0, v) ≤ bᵢ)` by at most
  `C ∑_{i<j} (S i j / v) exp (−(bᵢ² + bⱼ²) / (2 v (1 + S i j / v)))`.  No definition is needed:
  the laws are Mathlib's `multivariateGaussian` and `gaussianReal`.  The statement is the body of
  the cited proposition unchanged; the library proves it with `C = 1/4`.
- **`BerryEsseen`**: there is an absolute `C > 0` such that for every finite family of probability
  laws `νᵢ` on `ℝ` with mean `0`, finite third absolute moments and total variance `V > 0`, the
  distribution function of the sum of independent variables with these laws (the image of
  `Measure.pi ν` under `y ↦ ∑ᵢ yᵢ`) is within `C (∑ᵢ ∫ |z|³ dνᵢ) / V^{3/2}` of that of `N(0, V)`,
  at every point.  No definition is needed: the law of the sum is written out.
- **`PittGaussianFKG`**: let `X t` (`t ∈ T`) be a centred Gaussian family (Mathlib's `IsGaussianProcess`)
  on a probability space, with measurable integrable members and integrable pairwise products with
  nonnegative expectations.  For any finitely many indices `q 0, …, q (k-1)` and bounded Borel
  coordinatewise nondecreasing `f`, `g` on `Fin k → ℝ`, with `Y = (X (q i))ᵢ`,
  `E f(Y) · E g(Y) ≤ E f(Y) g(Y)`.  Covariance matrices may be singular.  No definition is needed.
- **`MultivariateBerryEsseen`**: for every `M > 0` and `0 < δ < 1` there is `C > 0` such that for all `N`,
  `m ≥ 1`, every centred law `ν` on `ℝ` with `0 < Var ν`, `E|ξ|³ ≤ M Var(ν)^{3/2}`, and every
  `a : Fin N → Fin m → ℝ` whose covariance matrix `Σ_{jk} = Var(ν) ∑ᵢ aᵢⱼ aᵢₖ` has quadratic form in
  `[(1-δ)|v|², (1+δ)|v|²]`, the law of `(∑ᵢ aᵢⱼ ξᵢ)ⱼ` (i.i.d. `ξᵢ ~ ν`) and `N(0, Σ)` differ on every
  orthant `{y_j ≤ h_j}` by at most `C m Var(ν)^{3/2} ∑ᵢ |aᵢ|³`.  The covariance matrix, the
  quadratic form and the coefficient norm are written out; no definition is needed.
- **`MultivariateBerryEsseenQuarter`**: the same statement with the factor `C m^{1/4}` in place of `C m`.  It is
  the frozen multivariate Berry-Esseen comparison of the Sandpile development, proved without a cited input.

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

with any other directory name in place of `Kingman` for the other pairs; the
tool revisions are pinned in
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) and
listed in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  A pass is the output
`Your solution is okay!`.

**Status.**  All eight solutions build.  `leanprover/comparator` at commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, with nanoda at
`6ae1f0cd962f081f6c423454c5da729d841236a7` and landrun at
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, printed `Your solution is okay!`
on all eight pairs with the nanoda kernel enabled.  Results and the
reproduction command are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The
workflow [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs the same check on request, since the builds are Mathlib-scale and Actions
minutes are spent only when asked for.
