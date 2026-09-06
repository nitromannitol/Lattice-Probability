/-
The general probability facts the papers cite, under this library's names.

Nothing here is proved: every declaration is an alias for a Mathlib theorem at
the revision this library is pinned to, so that a paper formalization can cite
`LatticeProb.kolmogorovZeroOne` and not have to know where Mathlib keeps it or
what it is called this month.  The docstring says what the statement is for; the
statement itself is Mathlib's, unchanged.

What Mathlib does not have, and this library therefore proves itself, is
elsewhere: the Harris inequality for product measures is in
`LatticeProb.Prob.Harris`, the ergodic zero-one law for coordinate shifts in
`LatticeProb.Prob.ZeroOne`, its lattice form in `LatticeProb.Prob.Translation`,
and the Hewitt-Savage zero-one law in `LatticeProb.Prob.HewittSavage`.  The
statements this library takes from the literature without proof are in
`LatticeProb.External`.
-/
import Mathlib

namespace LatticeProb

/-! ### Zero-one laws -/

/-- **Kolmogorov's zero-one law**: a tail event of an independent family has
probability `0` or `1`. -/
alias kolmogorovZeroOne :=
  ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop

/-- **Kolmogorov's zero-one law**, for a family indexed downwards. -/
alias kolmogorovZeroOne_atBot :=
  ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atBot

/-! ### Borel-Cantelli -/

/-- **The first Borel-Cantelli lemma**: if the measures of a sequence of sets are
summable then almost every point lies in only finitely many of them. -/
alias borelCantelli_first := MeasureTheory.measure_limsup_atTop_eq_zero

/-- The first Borel-Cantelli lemma in the form "almost surely, eventually
outside". -/
alias borelCantelli_first_eventually := MeasureTheory.ae_eventually_notMem

/-- **The second Borel-Cantelli lemma**: if the sets are independent and the sum
of their measures diverges then almost every point lies in infinitely many. -/
alias borelCantelli_second := ProbabilityTheory.measure_limsup_eq_one

/-- **Levy's generalized Borel-Cantelli lemma**: a point lies in infinitely many
of an adapted sequence of sets exactly when the conditional probabilities of the
next set, given the past, have divergent sum. -/
alias borelCantelli_levy := MeasureTheory.ae_mem_limsup_atTop_iff

/-! ### Laws of large numbers and the central limit theorem -/

/-- **The strong law of large numbers** for pairwise independent, identically
distributed, integrable random variables in a Banach space. -/
alias strongLaw_ae := ProbabilityTheory.strong_law_ae

/-- **The strong law of large numbers** for real random variables. -/
alias strongLaw_ae_real := ProbabilityTheory.strong_law_ae_real

/-- **The strong law of large numbers** in `L^p`. -/
alias strongLaw_Lp := ProbabilityTheory.strong_law_Lp

/-- **The central limit theorem**: the centred and rescaled partial sums of an
independent, identically distributed, square integrable family converge in
distribution to a centred Gaussian of the same variance. -/
alias centralLimitTheorem := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub

/-- **The central limit theorem** for a standardized family. -/
alias centralLimitTheorem_standardized :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum

/-! ### Concentration -/

/-- **The Azuma-Hoeffding inequality** for a sum of conditionally sub-Gaussian
increments. -/
alias azumaHoeffding := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF

/-- **Hoeffding's inequality**: the tail of a sum of independent sub-Gaussian
random variables. -/
alias hoeffding := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun

/-- **Hoeffding's lemma**: a centred random variable in `[a, b]` is sub-Gaussian
with parameter `((b - a) / 2) ^ 2`. -/
alias hoeffdingLemma := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero

/-! ### Martingales -/

/-- **The optional stopping theorem** for bounded stopping times: the expected
stopped value of a submartingale is monotone in the stopping time. -/
alias optionalStopping := MeasureTheory.Submartingale.expected_stoppedValue_mono

/-- Optional stopping characterizes submartingales: an adapted integrable
process is a submartingale exactly when its expected stopped value is monotone
in every pair of bounded stopping times. -/
alias optionalStopping_iff := MeasureTheory.submartingale_iff_expected_stoppedValue_mono

/-- The stopped process of a submartingale is a submartingale. -/
alias submartingale_stoppedProcess := MeasureTheory.Submartingale.stoppedProcess

/-- **Doob's maximal inequality** for a nonnegative submartingale. -/
alias doobMaximalInequality := MeasureTheory.maximal_ineq

/-- **Doob's martingale convergence theorem**: an `L^1` bounded submartingale
converges almost everywhere. -/
alias doobConvergence := MeasureTheory.Submartingale.ae_tendsto_limitProcess

/-- **Doob's `L^1` convergence theorem**: a uniformly integrable submartingale
converges in `L^1`. -/
alias doobConvergence_L1 := MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess

/-- **Levy's upward theorem**, almost everywhere. -/
alias levyUpward_ae := MeasureTheory.tendsto_ae_condExp

/-- **Levy's upward theorem**, in `L^1`. -/
alias levyUpward_L1 := MeasureTheory.tendsto_eLpNorm_condExp

/-! ### Product measures and Ionescu-Tulcea -/

/-- **The Ionescu-Tulcea theorem**: the trajectory kernel of a sequence of Markov
kernels. -/
alias ionescuTulcea := ProbabilityTheory.Kernel.traj

/-- The finite-dimensional marginals of the Ionescu-Tulcea trajectory kernel are
the partial trajectory kernels. -/
alias ionescuTulcea_marginal := ProbabilityTheory.Kernel.traj_map_frestrictLe

/-- The infinite product of probability measures on an arbitrary index type. -/
alias infiniteProduct := MeasureTheory.Measure.infinitePi

/-- The finite-dimensional marginals of the infinite product are the finite
products. -/
alias infiniteProduct_marginal := MeasureTheory.Measure.infinitePi_map_restrict

/-- The infinite product is the projective limit of the finite products. -/
alias infiniteProduct_isProjectiveLimit := MeasureTheory.Measure.isProjectiveLimit_infinitePi

/-- The infinite product measure of a cylinder is the product of the factors. -/
alias infiniteProduct_apply_pi := MeasureTheory.Measure.infinitePi_pi

/-- A measure whose cylinder values are the products of the factors is the
infinite product. -/
alias eq_infiniteProduct := MeasureTheory.Measure.eq_infinitePi

/-- Over a finite index type the infinite product is the ordinary product. -/
alias infiniteProduct_eq_pi := MeasureTheory.Measure.infinitePi_eq_pi

/-- A family is independent exactly when its joint law is an infinite product. -/
alias iIndepFun_iff_infiniteProduct :=
  ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map

/-! ### Brownian motion -/

/-- A process whose finite-dimensional laws are those of Brownian motion. -/
alias IsPreBrownian := ProbabilityTheory.IsPreBrownianReal

/-- A pre-Brownian process with almost surely continuous paths. -/
alias IsBrownian := ProbabilityTheory.IsBrownianReal

/-- A process all of whose finite-dimensional laws are Gaussian. -/
alias IsGaussianProcess := ProbabilityTheory.IsGaussianProcess

/-- A centred Gaussian process with covariance `min s t` is pre-Brownian. -/
alias isPreBrownian_of_covariance :=
  ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance

/-- A process with independent increments and the right one-dimensional laws is
pre-Brownian. -/
alias isPreBrownian_of_indepIncrements :=
  ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw

end LatticeProb
