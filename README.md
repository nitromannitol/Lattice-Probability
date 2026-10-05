# Lattice-Probability

A machine-checked **Lean 4** library of discrete probability and lattice
potential theory, built on
[`mathlib`](https://github.com/leanprover-community/mathlib4).  It is the
shared base of the formalizations of Ahmed Bou-Rabee's papers.

[![CI](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Lattice-Probability/actions/workflows/comparator.yml)

## What is proved

This is a library, not the formalization of one paper.  It collects the
objects and theorems that several formalizations have in common, so that each
of them imports one proof instead of carrying its own: simple random walk on
`ℤ^d` and on locally finite graphs, its transition kernels and Green
functions, local central limit theorems, electrical networks and the killed
Green function, the discrete Gaussian free field, the classical integer
sandpile, ergodic theorems and zero-one laws, correlation and percolation
inequalities, concentration and moment inequalities, convex order, Gaussian
processes and Brownian motion, scaling-limit infrastructure, regular
variation, and the topology of curves on the square lattice.  A result that
carries no content specific to one paper lives here, and the paper
repositories import the shared proof.

The library is required, at a pinned commit, by the formalization
repositories
[`Divisible-Sandpile-Percolation`](https://github.com/nitromannitol/Divisible-Sandpile-Percolation),
[`Divisible-Sandpile-RWRS`](https://github.com/nitromannitol/Divisible-Sandpile-RWRS),
[`Parking-Sharpness`](https://github.com/nitromannitol/Parking-Sharpness),
[`Unique-Continuation-Planar`](https://github.com/nitromannitol/Unique-Continuation-Planar)
and [`ORRW-Lower-Bound`](https://github.com/nitromannitol/ORRW-Lower-Bound),
and by the formalizations in progress of *Dynamic dimensional reduction*,
*Exploding sandpiles*, the random abelian sandpile, discrete elliptic
regularity, and `manhattan-formalization`.

Every theorem of the library is proved.  A theorem that rests on a result
cited from the literature and not proved here is conditional on it and takes
it as an explicit hypothesis; those results are listed next.  The library has
no single source text: each principal theorem states its result in its
docstring with the citation, and the `alignment` section of
[`formalization.yaml`](formalization.yaml) matches the theorems that formalize
a cited result with their sources.

### Cited results taken as hypotheses

Five results from the literature are stated as propositions in
`LatticeProb/External/` and never proved here: the Gaussian logarithmic Sobolev
inequality and its Herbst bound, polygonal unicoherence, Janiszewski's theorem
for polygonal sets, and the Rellich-Kondrachov compact embedding in negative
Sobolev order.  A theorem that uses one of them takes it as an explicit
hypothesis, so its statement shows what it rests on.  Only the Herbst bound and
the Rellich-Kondrachov embedding are used, by
`LatticeProb.gaussian_lipschitz_concentration` and by the compactness results
of `LatticeProb/Analysis/Sobolev/`.

Four further propositions there are proved in the library:
`PotentialKernelAsymptotics`, the Green function and potential kernel
asymptotics that formalizations cite from Lawler–Limic
(`LatticeProb/External/PotentialKernelAsymptoticsProved.lean`),
`FeyMeesterRedigLeastAction`, the least action principle for legal topplings
cited from Fey–Meester–Redig
(`LatticeProb/External/FeyMeesterRedigLeastActionProved.lean`),
`CarneVaropoulos`, the Carne–Varopoulos bound
(`LatticeProb/External/CarneVaropoulosProved.lean`), and `GreenNorms`, the two
norms of the truncated Green function
(`LatticeProb/External/GreenNormsProved.lean`).

### Contents

The principal theorems, by area.  Each name is a Lean declaration.  Every
theorem named appears in
[`LatticeProb/Meta/AxiomsAudit.lean`](LatticeProb/Meta/AxiomsAudit.lean); the
propositions of `LatticeProb/External/` are definitions, and the `…_holds`
theorems that prove them appear there.

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
* `LatticeProb.greenNorms`: the two norms of the truncated Green function
  `g_n = ∑_{j<n} P^j(0, ·)` for `n ≥ 2`, `‖g_n‖₂ ≍ n^{3/4}, n^{1/2}, n^{1/4},
  √(log n), 1` in dimensions one to four and five upward and
  `max_x g_n(x) ≍ n^{1/2}, log n, 1` in dimensions one, two and three upward
  (Bou-Rabee–Panagiotis, Section 3.1); it proves the proposition
  `LatticeProb.External.GreenNorms` (`LatticeProb.External.greenNorms_holds`).
* `LatticeProb.exists_srwGreen_gradient` and
  `LatticeProb.exists_srwGreenInf_gradient`: the gradient bound
  `|G(y) - G(z)| ≤ C (1 + |y|)^{1-d}` for neighbours `y, z`, for the truncated
  Green function uniformly in the time horizon when `d ≥ 2`, and for the Green
  function when `d ≥ 3`.
* `LatticeProb.exists_srwGreenInf_le`: `G(0, z) ≤ C (1 + |z|)^{2-d}` for
  `d ≥ 4`; `LatticeProb.exists_tsum_srwGreenInf_sq_tail_le`: the tail
  `∑_{|z| ≥ r} G(0, z)² ≤ C r^{4-d}` for `d ≥ 5`.
* `LatticeProb.BallGreen.ballGreenBounds`: the seven ball-killed Green
  estimates in dimension four (`Sandpile.External.BallGreenBounds`): the
  pointwise and square bounds, the annular gradient bound, the cutoff field and
  its shifts, and the finite-time tail; it proves the proposition
  `LatticeProb.External.BallGreenBounds`
  (`LatticeProb.External.ballGreenBounds_holds`).
* `LatticeProb.Intersection.exists_lintegral_interCount_sq_le`: the second
  moment of the number `I = ∑_{i,j} 1{X_i = Y_j}` of intersections of two
  independent simple random walks from `x` and `y` on `ℤ^d`, `d ≥ 5`,
  `E_x E_y I² ≤ C (1 + |x - y|)^{4-d}` (Lawler, *Intersections of Random
  Walks*, proof of Theorem 3.3.2).
* `LatticeProb.srwHitProb_eq_green_ratio`: for `d ≥ 3` the probability that
  the walk from `x` ever hits the origin is `G(x) / G(0)`.
* `LatticeProb.exists_abs_srwGreenInf_sub_le`: the Green function asymptotics
  `|G(x) - 2/((d - 2) ω_d) |x|^{2-d}| ≤ C |x|^{-d}` for `d ≥ 3` and `|x| ≥ 1`,
  with `ω_d` the volume of the unit ball (Lawler–Limic, Theorem 4.3.1).
* `LatticeProb.potentialKernel`, the planar potential kernel
  `b(x) = lim_M [G_M(0) - G_M(x)]`: `LatticeProb.tendsto_potentialKernel`, the
  limit exists; `LatticeProb.potentialKernel_zero` and
  `LatticeProb.walkOp_potentialKernel_sub`, `b(0) = 0` and `(P - I) b = δ₀`;
  `LatticeProb.exists_abs_potentialKernel_sub_log_le`,
  `|b(x) - ((2/π) log |x| + κ)| ≤ C |x|^{-2}` for `|x| ≥ 1` (Lawler–Limic,
  Theorem 4.4.4).  Together they prove the proposition
  `LatticeProb.External.PotentialKernelAsymptotics d` for every `d`
  (`LatticeProb.External.potentialKernelAsymptotics_holds`).
* `LatticeProb.markov_stopping`: the strong Markov property at a bounded
  stopping time.
* `LatticeProb.exists_maxDisp_bound`: the maximal displacement up to time `n`
  exceeds `a` with probability at most `C exp(-c a² / n)`;
  `LatticeProb.srwTail_le`: Hoeffding's bound for the one-dimensional walk.
* `LatticeProb.integral_rangeCard_sq_le`: the range `R_t` satisfies
  `E|R_t|² ≤ 2 (E|R_t|)²`.
* `LatticeProb.T_originBox_le`: the mean exit time of the box of radius `r`,
  summed over the box, is at most `C (2r + 1)^{d+2}`.
* `LatticeProb.resistance_packing`: for `d ≥ 2`, summing over any injective
  enumeration of `M` sites the effective resistance from each site to the
  complement of its predecessors is at most `C M`, with `C` depending only on
  `d`; `LatticeProb.insertion_inequality`: on the same enumeration, the sum of
  the exit probability and the voltage at each step is at most
  `C M^{1 + 1/d}`.
* `LatticeProb.Graph.nash_ineq`: the Nash inequality of dimension one on an
  infinite connected graph; `LatticeProb.Graph.heat_diag_le`: the on-diagonal
  bound `p_m(x, x) ≤ 32 d / √m` when every degree is at most `d`, and
  `LatticeProb.Graph.spectralDimensionBound_of_boundedDegree`, the same as a
  spectral dimension bound.
* `LatticeProb.Graph.walkLaw_eval_le_carneVaropoulos`: the Carne–Varopoulos
  bound `P_x(X_n = y) ≤ 2 √(deg y / deg x) e^{-dist(x, y)²/(2n)}` for the
  simple random walk on a connected locally finite graph (Lyons–Peres,
  Theorem 13.4), and `LatticeProb.Graph.heat_le_carneVaropoulos`, the same for
  the heat kernel; they prove the proposition
  `LatticeProb.External.CarneVaropoulos` (`LatticeProb.External.carneVaropoulos_holds`).
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
* `LatticeProb.LocalCLT.exists_abs_srwHeat_add_succ_sub_le`: the paired local
  central limit theorem on `ℤ^d`, `|p_n(x) + p_{n+1}(x) - 2 (d/(2πn))^{d/2}
  e^{-d|x|²/(2n)}| ≤ C n^{-(d+2)/2}` for `n ≥ 1`, uniformly in `x`, and
  `LatticeProb.LocalCLT.exists_abs_srwHeat_sub_le`, its parity form at the sites
  of the parity of `n` (Lawler–Limic, Theorem 2.1.3); with the forms
  `LatticeProb.LocalCLT.exists_abs_heatKernel_four_add_succ_sub_le` (`d = 4`,
  error `C/n³`) and `LatticeProb.LocalCLT.exists_window_abs_heatKernel_sub_heatKernelBM_le`,
  `LatticeProb.LocalCLT.exists_window_abs_srwHeat_sub_gauss_lt` (uniform on
  parabolic windows) cited by the divisible-sandpile and parking formalizations.
* `LatticeProb.ContinuousTime.exists_abs_lineKernel_sub_lineGauss_le`: the
  local limit theorem for the continuous-time walk on `ℤ` with a
  Gaussian-weighted error, `|q_s(k) - g_s(k)| ≤ C s^{-3/2} exp(-k²/(10(s + |k|)))`
  for all `s > 0`, by shifting the Fourier contour to `Im θ = k/s`; and
  `LatticeProb.ContinuousTime.exists_abs_ctHeat_sub_ctGauss_le`, its product
  form on `ℤ^d`, `|q_t(x) - ḡ_t(x)| ≤ C t^{-(d+2)/2} exp(-c|x|²/(t + |x|))` for
  `t ≥ 1`.

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
* `LatticeProb.Network.maximum_neighbors`: the discrete maximum principle at
  equality, a harmonic vertex whose neighbours are all at most its own value
  has every neighbour exactly equal to it.
* `LatticeProb.Network.caccioppoli`: the discrete Caccioppoli inequality, a
  cutoff-weighted Dirichlet energy of a harmonic function is controlled by
  the Dirichlet energy of the cutoff itself, weighted by the function; this
  feeds `LatticeProb.Network.moser_estimate` and
  `LatticeProb.Network.moser_l2_step`, the first Moser-iteration step
  bounding a harmonic function on a finite set by the conductance-weighted
  mean square of its neighbours.

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
* `LatticeProb.akcoglu_krengel_mean`: the mean half of the multiparameter
  subadditive ergodic theorem of Akcoglu and Krengel, along cubes. A set
  function on boxes of `ℤ^d`, stationary under a measure-preserving action of
  the lattice, bounded by a multiple of the volume, and subadditive when a box
  splits into two boxes, has a volume-normalised mean that converges along the
  cubes `[0, n)^d`.
* `LatticeProb.gridAvg_univ_l2_tendsto`: the `L²` mean ergodic step of the
  Akcoglu–Krengel theorem: for a measure-preserving additive `ℤ^d` action and a
  bounded measurable `h`, the cube averages `gridAvg σ h univ n` converge in
  `L²` to a bounded measurable limit with the same integral.
* `LatticeProb.exists_ae_tendsto_shiftField_anchoredBox`: the field-space shift
  instantiation of the anchored-box a.e. ergodic theorem: for a shift-invariant
  field law, the anchored-box averages of the shifted field `shiftField x v`
  converge almost everywhere;
  `LatticeProb.exists_ae_tendsto_shiftField_anchoredBox_ergodic` adds the ergodic
  case, where the limit is a.e. constant.
* `LatticeProb.exists_ae_tendsto_anchoredBox_with_integral`: the anchored-box a.e.
  ergodic theorem with coordinate-dependent side lengths, from the per-coordinate
  box-tiling iteration (`boxGridSet`, `boxAvg`), with the a.e. limit carrying the
  same integral; `LatticeProb.comp_sigma_eq_of_comp_unit_eq` extends the limit's
  invariance from the generators `σ (unit j)` to the whole `ℤ^d`-action `σ z`, and
  `LatticeProb.ae_eq_const_of_forall_invariant`, together with
  `LatticeProb.exists_ae_tendsto_anchoredBox_ergodic`, gives the ergodic
  anchored-box theorem: under an ergodic action the invariant limit is a.e.
  constant.
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
* `LatticeProb.mcdiarmid`: McDiarmid's bounded-differences inequality, the
  upper tail of a function of independent coordinates with bounded
  one-coordinate oscillation `c i` is at most `exp(-2t² / ∑ i, c i²)`.
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
* `LatticeProb.ouSemigroupN`, `LatticeProb.ouGeneratorN`,
  `LatticeProb.ouSemigroupN_comp_eval`, `LatticeProb.ouGeneratorN_comp_eval`,
  `LatticeProb.ouHeatEquationN_comp_eval`, `LatticeProb.ouSemigroupN_prod`: the general-`n`
  Ornstein–Uhlenbeck (Mehler) semigroup and generator on `Fin n → ℝ`, with the
  coordinate evaluation identities, the factorisation on tensor products, and the
  named heat-equation input `OUHeatEquationN`.
* `LatticeProb.gaussian_lipschitz_concentration_l2_fin`: the same concentration
  on `Fin n → ℝ` from the l2 (Cameron–Martin) Lipschitz condition, with the
  constant `L √n` produced by `LatticeProb.lipschitzWith_pi_of_hasSum_sq` and
  the l2-versus-sup comparison
  `LatticeProb.sqrt_sum_sq_le_sqrt_card_mul_dist`.
* `LatticeProb.hasSum_sq_comb_sub`, `LatticeProb.abs_partialInt_sub_le`: the
  partial integral on a finite coordinate set preserves the ℓ²-Lipschitz
  constant, since splicing along a finite set leaves a difference supported on
  that set.
* `LatticeProb.ae_subset_iUnion_iInter_of_tendsto_ae`,
  `LatticeProb.measure_le_of_tendsto_ae_of_isOpen`,
  `LatticeProb.measure_le_of_tendsto_ae_of_lt`: the a.e. Fatou limit: an almost
  sure limit `X n → Y` inherits the tail bound of the `X n` on open sets and on
  strict tails.
* `LatticeProb.paley_zygmund_of_second_moment`, `LatticeProb.ottaviani`,
  `LatticeProb.DoobMaximal.measureReal_sup_partialSum_sq_le`,
  `LatticeProb.pinsker`: the Paley-Zygmund inequality, Ottaviani's maximal
  inequality, Doob's maximal inequality for bounded i.i.d. partial sums, and
  Pinsker's inequality.
* `LatticeProb.efron_stein`: the Efron-Stein inequality for a function of `M`
  independent coordinates that is Lipschitz coordinate by coordinate, the
  variance is at most the total one-coordinate resampling energy.
* `LatticeProb.exists_mgf_neg_bounds`: for a centred law with an exponential
  moment and a stretched-exponential lower tail of exponent `γ > 1`, the
  Laplace transform of the negated variable is finite everywhere and bounded
  by `exp(Cμ²)` for `μ ≤ 1` and by `exp(Cμ^{γ/(γ-1)})` for `μ ≥ 1`.
* `LatticeProb.small_ball_of_exp`: a uniform exponential-moment bound puts at
  least half the mass of a law in a window of radius `2K/θ` about the origin.
* `LatticeProb.integral_comparison_third_order`: if two laws share their
  first two moments and both have a sub-exponentially controlled third
  absolute moment `T` against a test function `f`, the two integrals of `f`
  differ by at most `JT/3`, for `J` a bound on `f`'s third derivative.
* `LatticeProb.tendsto_measureReal_weighted`: the weak law of large numbers
  for a weighted i.i.d. sum, with only a first moment, once the squared
  weights are negligible against the square of their total.
* `LatticeProb.weighted_iid_central_limit` and
  `LatticeProb.weighted_iid_central_limit_pick`: the weighted i.i.d. central
  limit theorem, for a triangular array of weights with vanishing sup norm
  and second moments converging to `Q`, the weighted row sum of independent
  copies of a centred `L²` law converges in distribution to the centred
  Gaussian of variance `σ² Q`; the second form reads the array at distinct
  sites of an i.i.d. field on the lattice.

**The bracket process and the Dambis–Dubins–Schwarz representation.**
`LatticeProb/Prob/BracketProcess.lean` is Stage 1 of the bracket process of a
continuous martingale: the dyadic realized quadratic variation
`realizedQVar M T n = ∑_{k<2ⁿ}(M((k+1)T/2ⁿ) - M(kT/2ⁿ))²`, its refinement
identity, and the cross-term splitting whose summands have conditional mean
zero, so the mean of `realizedQVar` is independent of the mesh.

* `LatticeProb.realizedQVar_eq_succ_add_cross`: `Q_n = Q_{n+1} + 2 * crossTerm_n`.
* `LatticeProb.condExp_cross_eq_zero` and
  `LatticeProb.condExp_dyadic_cross_eq_zero`: each cross-term summand has
  conditional mean zero, whence `LatticeProb.integral_crossTerm_eq_zero` and
  `LatticeProb.integral_realizedQVar_succ_eq`, the constant-mean property.

**Smooth maxima and softmax stability.**  `softMaximum β x = log(∑ exp(β xᵢ)) / β`
is the log-sum-exp smoothing of `max x`, with Gibbs weight `softWeight β x i`.

* `LatticeProb.softMaximum_derivative_bound` and
  `LatticeProb.softMinimum_derivative_bound`: for `1 ≤ k ≤ 3` the sum of
  absolute values of the `k`-th iterated coordinate derivative of the smooth
  maximum, respectively minimum, is at most `6|β|^{k-1}`, one bound covering
  the first-, second- and third-order case.
* `LatticeProb.SmoothBottleneckBound.softMaximum`: composing one more smooth
  maximum of functions already satisfying a uniform derivative bottleneck at
  layer `n` gives a function satisfying it at layer `n + 1`.
* `LatticeProb.expStable_softWeightComposition`: a softmax weight built from
  a field-nonexpansive family changes multiplicatively by at most a factor
  `exp(2|β| a)` under a uniform field perturbation of size `a`.

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
* `LatticeProb.multivariateGaussian_eq_map`,
  `LatticeProb.det_sqrt_mul_self`: the correlated multivariate Gaussian is the
  pushforward of the standard Gaussian under `√S`, equivalently the standard
  Gaussian times the density with the determinant factor
  `det (√S) = (det S)^{1/2}`.
* `LatticeProb.multivariateGaussian_eq_withDensity`: the density of `N(0, S)` for a
  positive definite `S`, `(2π)^{-n/2} (det S)^{-1/2} exp (-(x ⬝ᵥ S⁻¹ *ᵥ x)/2)`
  (Li–Shao route item 1), with
  `LatticeProb.multivariateGaussianDensityFormula_holds` recording it as the
  discharged `multivariateGaussianDensityFormula`.
* `LatticeProb.normalComparisonSmartPath`, `LatticeProb.bivariateGaussDensity_le`,
  `LatticeProb.integral_one_div_sqrt_one_sub_sq_mul_le`,
  `LatticeProb.integral_bivariateGaussDensity_le`: the elementary half of the
  Li–Shao normal-comparison bound for the multivariate Gaussian — the smart path
  from the product law to the covariance, the bivariate density comparison
  producing the exponential factor, the scale integral `≤ π/2`, and its
  integrated (smart-path) form; `LatticeProb.lintegral_Iic_cons`,
  `LatticeProb.lintegral_Iic_cons₂`, `LatticeProb.integral_Iic_cons`,
  `LatticeProb.integral_Iic_cons₂`,
  `LatticeProb.integral_integral_mixed_deriv` and
  `LatticeProb.integral_Iic_deriv_eq_of_tendsto` are the orthant box-Fubini and
  two-coordinate integration-by-parts substrate (route item 4).
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

**The classical integer sandpile.**  `LatticeProb.Sandpile` holds the
classical (integer, Abelian) sandpile on `ℤ^d` under parallel toppling,
distinct from the divisible sandpile of `LatticeProb.Graph`: a site holds an
integer number of chips and fires once it holds at least `2d`, sending one
chip to each neighbour.

* `LatticeProb.Sandpile.lap_eq_sum_second_diff`: the lattice Laplacian is the
  sum of the coordinatewise second differences.
* `LatticeProb.Sandpile.podo_mono_step`: the parallel toppling odometer is
  nondecreasing in time; `LatticeProb.Sandpile.fodo_topple_of_ge`: a site off
  a frozen set with at least `2d` chips topples at the next step.
* `LatticeProb.Sandpile.exists_adj_pos_of_nbrSumZ_pos`: a positive neighbour
  sum of a nonnegative function is carried by some one neighbour.
* `LatticeProb.Sandpile.wave_mono_time`: on a nonnegative background, the
  Diaconis-Fulton `n`-wave is nondecreasing along any stretch of time;
  `LatticeProb.Sandpile.lap_le_of_fixed`: a site where the wave equation
  holds is stable there.
* `LatticeProb.Sandpile.recurrent_const`: the constant background `η ≡ d` is
  recurrent, firing the outer boundary of any finite set `V` once each makes
  every site of `V` eventually topple.
* `LatticeProb.Sandpile.le_of_isLegalToppling`: the least action principle
  (Fey–Meester–Redig, Theorem 2.8), a legal toppling procedure never topples a
  site more often than a nonnegative odometer `w` with `s₀ + Δw` stable; it
  proves the proposition `LatticeProb.External.FeyMeesterRedigLeastAction`
  (`LatticeProb.External.feyMeesterRedigLeastAction_holds`).
* `LatticeProb.eventually_constant_of_monotone_bounded`: a monotone sequence
  of naturals bounded above is eventually constant;
  `LatticeProb.finset_common_stable`: pointwise eventual stabilization on a
  finite set gives one common stabilization time.
* `LatticeProb.sInf_coe_attained` and `LatticeProb.sInf_coe_top`: an
  `ℕ∞`-valued infimum of hitting times is attained at a witness natural when
  one exists, and is `⊤` otherwise.
* `LatticeProb.exists_nat_bound_of_isCompact` and
  `LatticeProb.nearestSite_smul_mem_box`: a compact subset of `ℝ^d` sits in a
  coordinate box of natural side length, and rounding a rescaled point of a
  bounded set to the nearest lattice site keeps it inside a corresponding
  lattice box.

**Scaling-limit infrastructure.**  `LatticeProb.Scaling` collects the
model-independent steps of a discrete-to-continuum scaling limit: running
maxima, Lipschitz limits, Cramér-Wold, Slutsky, and the McShane extension of a
functional off a nice class of paths.

* `LatticeProb.Scaling.RunningMax.continuous_runningMax` and
  `LatticeProb.Scaling.RunningMax.measurable_runningMax`: the running maximum
  of a jointly continuous field over a time window is jointly continuous, and
  is measurable in an auxiliary sample once the field is measurable at each
  fixed time.
* `LatticeProb.Scaling.BoundedFunctionalLift.abs_liftPhiOn_sub_le`: the
  McShane lift of a functional off a nice class of paths is Lipschitz for the
  unit-capped sup distance on every path, not only the nice ones;
  `LatticeProb.Scaling.BoundedFunctionalLift.liftPhiOn_eq_of_nice`: the lift
  recovers the original functional exactly on the nice paths.
* `LatticeProb.Scaling.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination_filter`:
  the Cramér-Wold device along a filter, convergence in distribution follows
  from convergence of the characteristic function of every fixed linear
  combination.
* `LatticeProb.Scaling.Slutsky.tendsto_add_of_tendsto_zero`: Slutsky's
  theorem, additive form, a sum of a convergent-in-distribution family and a
  family converging to zero in probability converges in distribution to the
  same limit.
* `LatticeProb.Scaling.LipschitzLimit.lipschitzWith_one_of_tendsto`: a
  pointwise limit of uniformly `1`-Lipschitz functions is `1`-Lipschitz.
* `LatticeProb.Scaling.LocallyUniformLimit.continuous_and_monotone_of_tendstoLocallyUniformly`:
  a locally uniform limit of continuous, time-monotone functions is
  continuous and monotone.
* `LatticeProb.Scaling.PositiveCutoff.exists_cutoff_eq_one`: on a compact set
  where a continuous function is everywhere strictly positive, the Lipschitz
  positivity cutoff built from it equals `1`.

**Convex order and the exponential reference law.**  `LatticeProb.ConvexOrder`
compares a mean-zero law with a fixed exponential reference law in convex
order, by symmetrizing and then comparing tails.

* `LatticeProb.ConvexOrder.convex_integral_le_refLaw`: any mean-zero law with
  an exponential moment bounded by `A` lies below a canonical scaled
  reference (Laplace-type) law in convex order, for every convex Lipschitz
  test function.
* `LatticeProb.ConvexOrder.convex_lipschitz_integral_le_finite_pi`: a
  one-dimensional convex-order comparison tensorizes, lifting to every
  convex Lipschitz function of a finite product.
* `LatticeProb.ConvexOrder.twoPointLaw_convex_le`: a mean-zero law whose
  positive part carries mass at least `p` dominates, in convex order, the
  symmetric two-point law at `±a` for every `0 < a ≤ p/2`.
* `LatticeProb.ConvexOrder.exists_twoPoint_comparison`: a near-family of
  mean-zero integer laws is bounded below, uniformly in its parameter near
  zero, by a fixed symmetric two-point law in convex order.

**Lattice kernels, Riemann sums and the binomial shift correlation.**

* `LatticeProb.Walk.tendsto_latticeSum_mul_rpow`: for `f` continuous with
  compact support, the discrete lattice sum `∑_y f(y/R)` on `ℤ^d`, scaled by
  the mesh volume `R^{-d}`, converges to `∫ f` as `R → ∞`.
* `LatticeProb.Walk.shift_energy`: the fair binomial law summed over the
  number of trials and shifted by an integer `q` satisfies
  `∑_l ∑_j (b_l(j - q) - b_l(j))² = 4|q|`.

**Recurrence of the two-dimensional simple random walk.**
`LatticeProb.simpleRandomWalkRecurrent`: Pólya's theorem, the simple random
walk on `ℤ²` is recurrent, its Green series diverges.

**Dissipative-skew generators and their resolvent semigroups.**  For a
bounded generator `G = S + A` on a complex Hilbert space, split into a
self-adjoint dissipative part `S` and a skew-adjoint part `A`.

* `LatticeProb.Analysis.DissipativeSkewPair.variational_bound`: for every
  `λ > 0`, every vector `V`, and every competitor `g`, the resolvent energy of
  `λI - G` at `V` is squeezed between `0` and `‖g‖₊² + ‖V - Ag‖₋²`, the energy
  norms of `H = λI - S`.
* `LatticeProb.Analysis.integral_inner_operatorSemigroup_eq_resolvent`: the
  Green-Kubo identity, the Laplace transform of the semigroup correlation
  `⟪u, T(t)u⟫` equals the inner product of `u` against the resolvent of `G`.

**The Nash inequality on `ℤ²`, and the rate-two Poisson clock.**

* `LatticeProb.NashZ2.nash`: the sharp two-dimensional Nash inequality
  `(∑ f²)² ≤ ½ (∑ f)² E(f)` for nonnegative summable `f : ℤ² → ℝ`, with `E`
  the Dirichlet energy of the rate-two random walk generator.
* `LatticeProb.hasSum_poissonWeight`: the rate-two Poisson weights
  `w_n(t) = e^{-2t}(2t)^n/n!` sum to one for every real `t`.
* `LatticeProb.hasDerivAt_poissonWeight`: the generator identity
  `w_n'(t) = 2(w_{n-1}(t) - w_n(t))`.
* `LatticeProb.tsum_abs_dPoissonWeight_le`: the `L¹` concentration bound
  `E|N_t/t - 2| ≤ √(2/t)`.

**Percolation.**  `LatticeProb.Percolation` develops Russo's formula and
pivotal-coordinate calculus for a finite product `{0,1}`-model, Bernoulli
bond percolation on `ℤ²`, and the combinatorics behind an RSW-style crossing
argument.

* `LatticeProb.Percolation.fpr_piv` and `LatticeProb.Percolation.fpr_change`:
  Russo's formula, the slope in one coordinate's parameter of the probability
  of an increasing event is the probability that coordinate is pivotal for
  the event.
* `LatticeProb.Percolation.fpr_le_of_map`: if a map increases weights by a
  factor at most `K` and has at most `M` preimages of every target
  configuration, it changes probabilities by at most a factor `KM`.
* `LatticeProb.Percolation.fpw_le_of_agree` and
  `LatticeProb.Percolation.fpw_le_of_par`: the weight ratio of two
  configurations agreeing outside a finite set `J`, respectively of one
  configuration under two parameter families agreeing outside `J`, is bounded
  by `ρ^{|J|}`.
* `LatticeProb.Percolation.bondLaw_half_le_of_flip`: flipping one bond open
  can only increase the probability of an event determined by that bond.
* `LatticeProb.Percolation.bondLaw_toReal_eq_fpr`: the finite model of
  Bernoulli bond percolation on a finite bond set is the finite-parameter
  probability of the pivotal calculus above.
* `LatticeProb.Percolation.card_planeRectangle_aspect_le_cube` and
  `LatticeProb.Percolation.card_double_square_le_cube`: a rectangle of
  bounded aspect ratio and height `r` has at most `r^3` sites, once `r` is
  large enough.
* `LatticeProb.Percolation.walk_prefix_hit_integer`: a walk on which an
  integer-valued function changes by at most one per step has an initial
  segment ending at every intermediate value of the function between its
  endpoints.
* `LatticeProb.Percolation.measure_boxPathEvent_le`: the union bound behind
  an RSW-style path-existence argument, if every fixed set of vertices is
  simultaneously good with probability at most `p`, the probability that
  some bounded-step path is entirely good is at most the path count times
  `p`.
* `LatticeProb.Percolation.walkBottleneck_append`: the bisection identity,
  the bottleneck of a concatenated walk is the minimum of the two pieces'
  bottlenecks; `LatticeProb.Percolation.finiteMaximum_mem`: a finite maximum
  over a nonempty index set is attained.

**Total variation distance.**  `LatticeProb.pi_one_coord_le`: changing the
law of one coordinate of a finite product changes the probability of any
event by at most the total variation distance of that coordinate.
`LatticeProb.pi_tv_le`: changing every coordinate changes a probability by at
most the sum of the coordinates' total variation distances.
`LatticeProb.infinitePi_restrict_tv_le`: the same bound for an event
determined by finitely many coordinates of an infinite product.

**Graph combinatorics.**

* `LatticeProb.Graph.exists_epath`: if every vertex outside `S ∪ {y}` is
  balanced in a finite directed edge set while `y ∉ S` has strictly more
  in-degree than out-degree, the edge set contains a path from `S` to `y`.
* `LatticeProb.Graph.konig`: König's lemma for a prefix-closed, finitely
  branching predicate on finite lists, if it has members of every length,
  it has an infinite sequence all of whose finite prefixes are members.
* `LatticeProb.Graph.two_mul_sum_card_filter_lt`: a counting identity for the
  cyclic rank of a transitively acting permutation, summed over the starting
  point, how often one fixed point precedes another in the induced cyclic
  order.

## Guarantees

- **No `sorry`** in the library.  Each of the three Mathlib-only comparator
  challenges under `LatticeProbAudit/` contains its single intentional
  statement-level `sorry`, which the corresponding solution file proves.
  `python3 tools/check_warnings.py` checks that the build of `LatticeProb`
  emits no error, no warning and no `sorry`.
- **No custom `axiom`.**  Every declaration of the library reduces to
  `mathlib`'s three standard foundational axioms, `propext`,
  `Classical.choice` and `Quot.sound`.  `python3 tools/check_axioms.py` checks
  this for all 5,112 declarations, and
  [`LatticeProb/Meta/AxiomsAudit.lean`](LatticeProb/Meta/AxiomsAudit.lean)
  prints the axioms of the principal theorems.  The results cited from the
  literature are hypotheses, not axioms.
- **Independent check of the statements.** Three principal theorems are
  restated using only Mathlib, with no library definitions, in
  [`LatticeProbAudit/Kingman/Challenge.lean`](LatticeProbAudit/Kingman/Challenge.lean),
  [`LatticeProbAudit/GFF/Challenge.lean`](LatticeProbAudit/GFF/Challenge.lean)
  and
  [`LatticeProbAudit/BinomialLocalCLT/Challenge.lean`](LatticeProbAudit/BinomialLocalCLT/Challenge.lean).
  The comparator workflow submits each challenge and its solution to
  [leanprover/comparator](https://github.com/leanprover/comparator), which
  checks that the two statements have identical elaborated types and that the
  proof reduces to the three standard axioms, through the Lean kernel and the
  independent nanoda kernel.  See [`LatticeProbAudit/README.md`](LatticeProbAudit/README.md).
- **Pinned toolchain.** Lean `v4.32.0` and `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, the only git dependency of the
  library; the dependencies of mathlib are pinned in
  [`lake-manifest.json`](lake-manifest.json) at plausible `e12c1910fe85`,
  LeanSearchClient `c5d5b8fe6e51`, importGraph `7e9612bf0b9e`, proofwidgets
  `6e311e2a844d`, aesop `a7dbf0c63b69`, Qq `38d591e778f1`, batteries
  `023ce7d62a05` and Cli `88679d088c97`.  The dependent repositories use the
  same pin.

The three pairs are `Kingman` (the subadditive ergodic theorem, both halves),
`GFF` (the killed Green function is positive semidefinite and is the
covariance of a centred Gaussian measure, with the killed Green function
rebuilt from Mathlib primitives) and `BinomialLocalCLT` (the binomial local
central limit theorem with its `1/m` error).  Each challenge contains one
intentional statement-level `sorry`, which the corresponding `Solution.lean`
fills from the library.  The configurations
`LatticeProbAudit/*/comparator.json` are for
[`leanprover/comparator`](https://github.com/leanprover/comparator).  All three
solutions build and depend only on `propext`, `Classical.choice` and
`Quot.sound`, and the comparator checks that each solution statement is
exactly the challenge statement.  Both
[`.github/workflows/build.yml`](.github/workflows/build.yml) and
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) trigger
on request only (`workflow_dispatch`), since the builds are Mathlib-scale; the
comparator is also run locally before each release, and its results are
recorded in [`LatticeProbAudit/COMPARATOR_RUNS.md`](LatticeProbAudit/COMPARATOR_RUNS.md).

## Size

About 111,000 lines of Lean in 484 modules (the root `LatticeProb.lean` and 483
modules under `LatticeProb/`), of which about 87,000 lines are code once
comments and blank lines are removed, with 5,112 declarations, on top of
mathlib.  The count excludes the comparator surface in `LatticeProbAudit/`.

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
bash LatticeProbAudit/check_standalone.sh --vocabulary   # the GFF vocabulary block, Challenge vs SolutionBasic
```

To run the comparator on one pair, build `LatticeProbAudit` and then, from the
repository root,

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator LatticeProbAudit/Kingman/comparator.json
```

The revisions of the comparator, `lean4export`, `landrun` and `nanoda` are
pinned in [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml)
and recorded in [`LatticeProbAudit/COMPARATOR_RUNS.md`](LatticeProbAudit/COMPARATOR_RUNS.md); see
[`LatticeProbAudit/README.md`](LatticeProbAudit/README.md).

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
                        property, hitting probabilities, the range, exit times, the
                        resistance packing and insertion inequalities, an abstract
                        finite-range kernel and the lattice Riemann-sum limit, the
                        binomial law's shift correlation, Pólya recurrence and the Nash
                        inequality on ℤ², the walk in continuous time and its local
                        limit theorem, the Green function and potential kernel
                        asymptotics
  Graph/                the walk on a locally finite graph: heat kernel, Nash inequality,
                        on-diagonal bounds, exit times, the divisible sandpile and the
                        random-walk representation of its odometer, the vertex boundary,
                        Eulerian paths, König's lemma, the cyclic rank of a permutation
  Sandpile/             the classical (integer, Abelian) sandpile on ℤ^d: parallel
                        toppling, the Diaconis-Fulton wave decomposition, recurrence,
                        the least action principle
  Network/              electrical networks: energy, Dirichlet and Thomson principles,
                        Rayleigh monotonicity, Nash-Williams, the killed Green function,
                        escape probabilities, the Gaussian free field, harmonic-function
                        algebra, the Caccioppoli inequality and the first Moser step
  Prob/                 ergodic theorems, zero-one laws, correlation and percolation
                        inequalities (Percolation/), concentration and moment
                        inequalities, convex order, Brownian motion, regular variation,
                        total variation distance, scaling-limit infrastructure (Scaling/)
  Gauss/                Gaussian measures, the isonormal process, white noise,
                        Gaussian tails
  Lattice/Planar/       curves on the square lattice and the separation lemma
  Lattice/NearestPoint.lean   rounding a point of ℝ^d to the nearest lattice site
  Order/                 eventual stabilization of a monotone sequence, ℕ∞-valued
                        hitting-time arithmetic
  Analysis/, Topology/   negative-order Sobolev norms; polygonal subsets of the plane;
                        dissipative-skew generators and their resolvent semigroups;
                        smooth maxima, softmax weights and their stability
  Support/               elementary lemmas used across the library
  External/              the five cited results, each a Prop taken as a hypothesis, and the
                        Green function asymptotics, the least action principle, the
                        Carne–Varopoulos bound and the norms of the truncated Green
                        function, each stated as a Prop and proved
  Meta/                  AxiomsAudit.lean
  *.lean (top level)     the particle-hole process on ℤ^d (ParticleHole, ParticleDriven,
                        Equivariance, Invariance, ReadIndex, Rank) and the continuum
                        objects shared with Parking-Sharpness: white noise, heat kernels,
                        optimal stopping values, weak limits
LatticeProb.lean         the root module (imports the whole library)
LatticeProbAudit/
  Kingman/, GFF/,        the Mathlib-only comparator pairs (each with Challenge.lean,
  BinomialLocalCLT/      Solution.lean and comparator.json; GFF/ also has SolutionBasic.lean)
  Support/               GFFBridge.lean, the bridge of the GFF solution to the library
  README.md, DESIGN.md   the comparator surface, what each challenge checks, and its design
  COMPARATOR_RUNS.md     the recorded comparator runs and the tool revisions
  check_standalone.sh    elaborates a challenge standalone; checks the vocabulary blocks
tools/                   check_axioms.py, check_warnings.py and check_names.py, listed
                         under Building
.github/workflows/       build.yml and comparator.yml, run on request
lakefile.lean, lake-manifest.json, lean-toolchain   the Lake project and its pins
CITATION.cff, CONTRIBUTING.md, formalization.yaml   citation, contribution notes, disclosure
LICENSE, NOTICE          the license, and the files adapted from other repositories
```

## How this was built

The Lean code was written by AI coding agents under the close supervision of the author; the models, tooling and cost are disclosed in [`formalization.yaml`](formalization.yaml).

## Authors, citation, acknowledgements

The Lean development is by **Ahmed Bou-Rabee**.  To cite it, use
[`CITATION.cff`](CITATION.cff).

This library is built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4).  Three modules
of `LatticeProb/Prob/` are adapted from the percolation library of
[`anthropics/formal-math`](https://github.com/anthropics/formal-math), the
modules of `LatticeProb/Lattice/Planar/` from
[`rotor-23`](https://github.com/nitromannitol/rotor-23), and sixteen continuum
modules from
[`Parking-Sharpness`](https://github.com/nitromannitol/Parking-Sharpness);
[`NOTICE`](NOTICE) lists the files and the commits.  The comparator audit in
[`LatticeProbAudit/`](LatticeProbAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
