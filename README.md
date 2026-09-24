# Lattice-Probability

A machine-checked **Lean 4** library of discrete probability and lattice
potential theory, built on
[`mathlib`](https://github.com/leanprover-community/mathlib4).  It is the
shared base of the formalizations of Ahmed Bou-Rabee's papers.

[![CI](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/comparator.yml)

## What this is

This is a library, not the formalization of one paper.  It collects the
objects and theorems that several formalizations have in common, so that each
of them imports one proof instead of carrying its own: simple random walk on
`ℤ^d` and on locally finite graphs, its transition kernels and Green
functions, local central limit theorems, electrical networks and the killed
Green function, the discrete Gaussian free field, ergodic theorems and
zero-one laws, correlation inequalities, concentration and moment
inequalities, Gaussian processes and Brownian motion, regular variation, and
the topology of curves on the square lattice.

The library is required, at a pinned commit, by the formalization
repositories
[`Divisible-Sandpile-Percolation`](https://github.com/nitromannitol/Divisible-Sandpile-Percolation),
[`Divisible-Sandpile-RWRS`](https://github.com/nitromannitol/Divisible-Sandpile-RWRS),
[`Parking-Sharpness`](https://github.com/nitromannitol/Parking-Sharpness) and
[`Unique-Continuation-Planar`](https://github.com/nitromannitol/Unique-Continuation-Planar),
and by the formalizations in progress of *Dynamic dimensional reduction*,
*Exploding sandpiles*, the random abelian sandpile and discrete elliptic
regularity.

The library has 291 modules, about 70,000 lines and 3,618 declarations.

- **No `sorry`** anywhere in the library.  Each Mathlib-only comparator
  challenge in `Audit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.
- **No custom `axiom`.**  Every declaration of the library reduces to
  `mathlib`'s three standard foundational axioms, `propext`,
  `Classical.choice` and `Quot.sound`.  `python3 tools/check_axioms.py`
  checks this for all 3,618 declarations, and
  [`LatticeProb/Meta/AxiomsAudit.lean`](LatticeProb/Meta/AxiomsAudit.lean)
  prints the axioms of the principal theorems listed below.
- **Cited results are hypotheses.**  Five results from the literature are
  stated as propositions in `LatticeProb/External/` and never proved here: the
  Gaussian logarithmic Sobolev inequality and its Herbst bound, polygonal
  unicoherence, Janiszewski's theorem for polygonal sets, and the
  Rellich-Kondrachov compact embedding in negative Sobolev order.  A theorem
  that uses one of them takes it as an explicit hypothesis, so its statement
  shows what it rests on.  Only the Herbst bound and the Rellich-Kondrachov
  embedding are used, by `LatticeProb.gaussian_lipschitz_concentration` and by
  the compactness results of `LatticeProb/Analysis/Sobolev/`.
- Pinned to Lean `v4.32.0` and `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`.  The dependent repositories use
  the same pin.

## Contents

The principal theorems, by area.  Each name is a Lean declaration; all of
them appear in `LatticeProb/Meta/AxiomsAudit.lean`.

**Walks and Green functions.**  Simple random walk on `ℤ^d` is the kernel
`srwHeat d j x = P_0(X_j = x)`, the lazy walk is `Q`, and the walk on a
general locally finite graph is `LatticeProb.Graph.heat`.

* `LatticeProb.srwHeat_gaussian`: the Gaussian upper bound
  `p_R(0, x) ≤ 3^d C_d R^{-d/2} exp(-|x|² / (8(R + 2d)))` for `R ≥ 1`.
* `LatticeProb.sqrt_le_gR_one_dim`, `gR_one_dim_le`, `log_le_gR_two_dim`,
  `gR_two_dim_le`, `gR_high_dim_le`: the truncated Green function of the lazy
  walk at the origin is of order `√n` in one dimension and `log n` in two, and
  is bounded in dimension three and higher.
* `LatticeProb.tsum_iterate_delta0_eq`: in dimension `d ≥ 3` the Green
  function of the lazy walk is twice that of the simple walk.
* `LatticeProb.exists_srwGreen_gradient` and
  `LatticeProb.exists_srwGreenInf_gradient`: the gradient bound
  `|G(y) - G(z)| ≤ C (1 + |y|)^{1-d}` for neighbours `y, z`, for the truncated
  Green function uniformly in the time horizon when `d ≥ 2`, and for the Green
  function when `d ≥ 3`.
* `LatticeProb.exists_srwGreenInf_le`: `G(0, z) ≤ C (1 + |z|)^{2-d}` for
  `d ≥ 4`; `LatticeProb.exists_tsum_srwGreenInf_sq_tail_le`: the tail
  `∑_{|z| ≥ r} G(0, z)² ≤ C r^{4-d}` for `d ≥ 5`.
* `LatticeProb.srwHitProb_eq_green_ratio`: for `d ≥ 3` the probability that
  the walk from `x` ever hits the origin is `G(x) / G(0)`.
* `LatticeProb.markov_stopping`: the strong Markov property at a bounded
  stopping time.
* `LatticeProb.exists_maxDisp_bound`: the maximal displacement up to time `n`
  exceeds `a` with probability at most `C exp(-c a² / n)`;
  `LatticeProb.srwTail_le`: Hoeffding's bound for the one-dimensional walk.
* `LatticeProb.integral_rangeCard_sq_le`: the range `R_t` satisfies
  `E|R_t|² ≤ 2 (E|R_t|)²`.
* `LatticeProb.T_originBox_le`: the mean exit time of the box of radius `r`,
  summed over the box, is at most `C (2r + 1)^{d+2}`.
* `LatticeProb.Graph.nash_ineq`: the Nash inequality of dimension one on an
  infinite connected graph; `LatticeProb.Graph.heat_diag_le`: the on-diagonal
  bound `p_m(x, x) ≤ 32 d / √m` when every degree is at most `d`, and
  `LatticeProb.Graph.spectralDimensionBound_of_boundedDegree`, the same as a
  spectral dimension bound.
* `LatticeProb.Graph.integrable_exitNat` and `LatticeProb.Graph.markov_exitTime`:
  the exit time of a finite set is integrable, and the strong Markov property
  holds at it.

**Local central limit theorems.**

* `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT`: for the probability
  `P_m(j)` that `m` independent signs sum to `j`,
  `|√m P_m(j) - 2 φ(j / √m)| ≤ C / m` uniformly over `m ≥ 1` and the `j` of the
  parity of `m` with `|j| ≤ m`, where `φ` is the standard normal density.
* `LatticeProb.exists_srwHeat_one_sub_gauss_le_int`: the one-dimensional local
  limit theorem `√(π m) p_{2m}(0, 2k) → exp(-k² / m)`, uniformly on
  `|k| ≤ A √m`.
* `LatticeProb.LocalCLT.srwHeat_eq_fourier`: the Fourier representation of
  `p_j(0, x)` on `ℤ^d` as an integral over the torus `[-π, π]^d`.

**Electrical networks and the killed Green function.**  A network is a locally
finite graph with conductances `c`.  For a finite set `C` that misses some
vertex, `killedGreenReal G C o v` is the Green function `g_C(o, v)` of the walk
killed on leaving `C`.

* `LatticeProb.Network.dirichlet_principle`: a function harmonic on `B` has
  the least energy among the functions with its values off `B`;
  `LatticeProb.Network.rayleigh_monotone`: the minimal energy increases with
  the conductances; `LatticeProb.Network.thomson_principle`: the energy of the
  voltage is at most the energy of any flow with the same divergence.
* `LatticeProb.Network.nashWilliams_le_effRes` and
  `LatticeProb.Network.nashWilliams_nested`: the Nash-Williams lower bound on
  the effective resistance from disjoint cutsets and from nested boundary cuts.
* `LatticeProb.Network.laplacian_killedGreenReal`,
  `LatticeProb.Network.killedGreenReal_symm`: `g_C(o, ·)` vanishes off `C`, has
  Laplacian `-1_o` on `C`, and is symmetric;
  `LatticeProb.Network.energyOn_killedGreenReal`: its energy is twice the
  effective resistance.
* `LatticeProb.Network.one_sub_returnProb` and
  `LatticeProb.Network.escape_eq_inv`: the escape probability from `o` is
  `1 / (deg(o) R_eff)`.
* `LatticeProb.Network.le_of_harmonicOn`: the maximum principle;
  `LatticeProb.Network.exists_voltage`: a bounded voltage with unit source and
  sink at two transient vertices.

**The discrete Gaussian free field.**  `LatticeProb/Network/GFF.lean` defines
the field with zero boundary values on a finite set `C` as
`gff G C = multivariateGaussian 0 (killedGreenMatrix G C)`.

* `LatticeProb.Network.killedGreenMatrix_posSemidef`: on a connected graph the
  killed Green function is positive semidefinite on `C`, because its quadratic
  form is half the Dirichlet energy of a potential.
* `LatticeProb.Network.integral_gff` and `LatticeProb.Network.covariance_gff`:
  the field is centred and its covariance is `g_C`.

**Ergodic theory and zero-one laws.**

* `LatticeProb.maximal_ergodic`: the maximal ergodic theorem, by Garsia's
  proof; `LatticeProb.ae_tendsto_bAvg`: Birkhoff's pointwise ergodic theorem.
* `LatticeProb.ae_tendsto_div`, `LatticeProb.ae_tendsto_gLow` and
  `LatticeProb.tendsto_integral_div`: Kingman's subadditive ergodic theorem.
  For a family subadditive along a transformation that preserves a finite
  measure and bounded below by `c n`, `g_n / n` converges almost everywhere,
  and the means `(∫ g_n) / n` converge to their infimum.
* `LatticeProb.ergodic_decomposition`: the ergodic decomposition of a
  measure-preserving transformation of a standard Borel probability space.
* `LatticeProb.ergodic_coordShift_infinitePi`: Bernoulli shifts are ergodic;
  `LatticeProb.measure_zero_or_one_of_exchangeable`: the Hewitt-Savage
  zero-one law; `LatticeProb.measure_zero_or_one_of_allTranslationInvariant`:
  translation-invariant events of an i.i.d. field on `ℤ^d` have probability
  zero or one.

**Correlation inequalities.**

* `LatticeProb.infinitePi_harris`: the Harris inequality for increasing events
  of a product measure over any index set.
* `LatticeProb.infinitePi_locallyMonotone_fkg`: the FKG inequality for locally
  monotone events.
* `LatticeProb.measure_pi_disjointOccSet_le`: the van den Berg-Kesten
  inequality for increasing events of a finite product of Bernoulli measures.

**Concentration and moment inequalities.**

* `LatticeProb.bernstein`: Bernstein's inequality for a finite sum of
  independent bounded centred variables.
* `LatticeProb.freedman`: Freedman's inequality for a martingale with bounded
  increments and bounded predictable quadratic variation.
* `LatticeProb.fukNagaev_bound`: the Fuk-Nagaev inequality for independent
  centred summands with `p`-th moments, `p ≥ 2`.
* `LatticeProb.vonBahrEsseen`: the von Bahr-Esseen tail bound for
  `1 ≤ p ≤ 2`.
* `LatticeProb.poisson_tail`: the Poisson (Bennett) tail of a sum of
  independent summands with values in `[0, β]`.
* `LatticeProb.evariance_le_half_tsum_siteEnergy`: the Efron-Stein inequality
  over a countable index set.
* `LatticeProb.gaussian_lipschitz_concentration`: Gaussian concentration for a
  Lipschitz function of `n` independent standard Gaussians, from the cited
  Herbst bound.
* `LatticeProb.paley_zygmund_of_second_moment`, `LatticeProb.ottaviani`,
  `LatticeProb.DoobMaximal.measureReal_sup_partialSum_sq_le`,
  `LatticeProb.pinsker`: the Paley-Zygmund inequality, Ottaviani's maximal
  inequality, Doob's maximal inequality for bounded i.i.d. partial sums, and
  Pinsker's inequality.

**Gaussian processes and Brownian motion.**

* `LatticeProb.exists_continuous_modification`: the Kolmogorov-Chentsov
  theorem on `ℝ≥0`.
* `LatticeProb.exists_isBrownian`: Brownian motion on `ℝ^d` with generator
  `Δ / (2d)` exists; `LatticeProb.IsBrownianSpace.hasStrongMarkovRestart`: its
  strong Markov property; `LatticeProb.brownian_exit_tail`: the probability of
  leaving the ball of radius `A` before time `T` is at most
  `C exp(-c A² / T)`.
* `LatticeProb.Isonormal.ae_tendsto_partialSum`: almost sure convergence of the
  partial sums of the isonormal process.
* `LatticeProb.GaussTail.gaussianReal_real_Ioi_le`: the Mills ratio bound;
  `LatticeProb.klDiv_gaussianReal_shift`: the relative entropy of two
  Gaussians with a common variance.
* `LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner`: the
  Cramér-Wold device; `LatticeProb.ExtendedMapping.extended_continuous_mapping`:
  the extended continuous mapping theorem.

**Regular variation.**  `LatticeProb.potter_bounds`: Potter's bounds for a
monotone regularly varying function; `LatticeProb.karamata_integrated_tail`
and `LatticeProb.karamata_origin_integral`: Karamata's theorem for the
integrated tail and for the integral from the origin.

**Planar lattice topology.**  `LatticeProb.Lattice.Planar.separation`: the
Jordan separation lemma on the doubled square lattice.  If a simple closed
curve avoids every site and bond outside a finite set `V`, then two sites
outside `V`, joined off the curve to its right side and to its left side, are
not both in the unbounded component of the complement of `V`.

## Verified against a Mathlib-only statement

So that three principal theorems can be read without trusting the library,
they are restated using **only Mathlib**, with no library definitions, in
`Audit/LatticeProbAudit/<X>/Challenge.lean`.  Each challenge contains one
intentional statement-level `sorry`, which the corresponding `Solution.lean`
fills from the library.  The configurations in
`Audit/LatticeProbAudit/*/comparator.json` are for
[`leanprover/comparator`](https://github.com/leanprover/comparator), which
confirms that the two statements have identical elaborated types and that the
proof reduces to the three standard axioms (see
[`Audit/README.md`](Audit/README.md)).

The three pairs are `Kingman` (the subadditive ergodic theorem, both halves),
`GFF` (the killed Green function is positive semidefinite and is the
covariance of a centred Gaussian measure, with the killed Green function
rebuilt from Mathlib primitives) and `BinomialLocalCLT` (the binomial local
central limit theorem with its `1/m` error).  All three solutions build and
depend only on `propext`, `Classical.choice` and `Quot.sound`, and
`Audit/LatticeProbAudit/StatementRegression.lean` checks locally that each
solution statement is exactly the challenge statement and mentions no
constant of the library.  The comparator itself has not yet been run on them;
the workflow
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) runs it.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake.  The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.32.0`), so `elan`
installs the right Lean version automatically.

```bash
lake exe cache get   # the first time: fetch the Mathlib build cache
lake build           # compile the library
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact Mathlib
revision.

```bash
lake build LatticeProb.Meta.AxiomsAudit      # print the axioms of the principal theorems
lake build LatticeProbAudit                  # the comparator challenges and solutions
lake build LatticeProbAudit.StatementRegression
```

To use the library from another Lake project, require it at a fixed commit and
use the same Mathlib pin:

```lean
require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "<commit>"
```

`import LatticeProb` pulls in the whole library; each module can also be
imported alone.

| command | what it guarantees |
|---|---|
| `python3 tools/check_axioms.py` | runs Lean's `#print axioms` on every declaration of the library and fails if any closure contains `sorryAx` or an axiom other than `propext`, `Classical.choice`, `Quot.sound` |
| `python3 tools/check_warnings.py` | the build of `LatticeProb` emits no error, no warning and no `sorry` |
| `python3 tools/check_names.py FILE` | every `LatticeProb.*` name mentioned in a text file exists |

## Repository layout

```
LatticeProb/
  Site.lean, IID.lean   sites of ℤ^d, the nearest-neighbour graph, i.i.d. fields
  Walk/                 simple and lazy random walk on ℤ^d: kernels, Gaussian bounds,
                        Green functions and their gradients, the local CLT, the Markov
                        property, hitting probabilities, the range, exit times
  Graph/                the walk on a locally finite graph: heat kernel, Nash inequality,
                        on-diagonal bounds, exit times, the divisible sandpile and the
                        random-walk representation of its odometer
  Network/              electrical networks: energy, Dirichlet and Thomson principles,
                        Rayleigh monotonicity, Nash-Williams, the killed Green function,
                        escape probabilities, the Gaussian free field
  Prob/                 ergodic theorems, zero-one laws, correlation, concentration and
                        moment inequalities, Brownian motion, regular variation
  Gauss/                Gaussian measures, the isonormal process, white noise,
                        Gaussian tails
  Lattice/Planar/       curves on the square lattice and the separation lemma
  Analysis/, Topology/  negative-order Sobolev norms; polygonal subsets of the plane
  Support/              elementary lemmas used across the library
  External/             the five cited results, each a Prop taken as a hypothesis
  Meta/                 AxiomsAudit.lean
  *.lean (top level)    continuum objects shared with Parking-Sharpness: white noise,
                        heat kernels, optimal stopping values, weak limits
LatticeProb.lean        the root module (imports the whole library)
Audit/                  Mathlib-only comparator challenges and solutions
tools/                  the checkers listed under Building
NOTICE                  the files adapted from other repositories, and their licenses
```

## How this was built

The Lean code in this repository was written by AI models under the
supervision of the author.  Most of it was written by Claude Opus 5 in Claude
Code, as "generals" working in shifts from 2026-09-06 on, and a Claude Code
supervising session merged and checked every branch.  OpenAI's gpt-6-astra,
through Codex, wrote the ergodic decomposition, the Gaussian law determined by
its covariance and Pinsker's inequality, ported the planar lattice modules
from rotor-23 and migrated sixteen continuum modules from Parking-Sharpness.
GLM-5.3 proved the von Bahr-Esseen inequality, the Kolmogorov bounds on
product spaces and the Fourier form of the heat kernel, and
DeepSeek-v4.1-flash, driven by the same scripts, wrote modules on conditional
expectations in a parameter, white noise, the supremum tail, negative Sobolev
norms and the binomial kernel.  Claude Sonnet 5 wrote the binomial local
central limit theorem.  Mistral's Leanstral wrote the proofs of the Gaussian
free field module `LatticeProb/Network/GFF.lean`.  Claude Opus 5.5 wrote
`LatticeProb/Meta/AxiomsAudit.lean`, the comparator surface in `Audit/` and the
release documentation.  The models, tooling and review status are disclosed
in full in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  If you use this library,
please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

This library is built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4).  Three modules
of `LatticeProb/Prob/` are adapted from the percolation library of
[`anthropics/formal-math`](https://github.com/anthropics/formal-math), the
modules of `LatticeProb/Lattice/Planar/` from
[`rotor-23`](https://github.com/nitromannitol/rotor-23), and sixteen continuum
modules from
[`Parking-Sharpness`](https://github.com/nitromannitol/Parking-Sharpness);
[`NOTICE`](NOTICE) lists the files and the commits.  The comparator audit in
[`Audit/`](Audit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
