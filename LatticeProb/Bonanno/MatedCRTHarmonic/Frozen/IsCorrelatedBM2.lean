/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   commit 31e7483. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCoord
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTLrCov
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTTwoSidedMin

/-!
# `IsCorrelatedBM2`

Centred Gaussian coordinate process with covariance `lrCov γ i j · twoSidedMin s t` (.1). This file declares the predicate only:
no existence or uniqueness theorem for such a process is declared here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **The Brownian pair of [18] §1.1** : `μ` is the law of a two-sided two-dimensional Brownian
motion `(L, R)` with `Var(L_t) = Var(R_t) = |t|`, `Cov(L_t, R_t) = −|t| cos(πγ²/4)`: the coordinate process
`(i, t) ↦ lrCoord i t` is a centred Gaussian process with covariance `lrCov γ i j · twoSidedMin s t` (so the forward
and backward halves are independent correlated Brownian motions, as in MatingOfTrees' `IsTwoSidedCorrelatedBM`).
Paths are continuous by the choice of `Path2`; `L_0 = R_0 = 0` holds almost surely (variance `0`). -/
structure IsCorrelatedBM2 (γ : ℝ) (μ : Measure Path2) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  isGaussianProcess : IsGaussianProcess (fun p : Fin 2 × ℝ => lrCoord p.1 p.2) μ
  integral_eq_zero : ∀ i t, ∫ ω, lrCoord i t ω ∂μ = 0
  covariance_eq : ∀ i j s t, cov[lrCoord i s, lrCoord j t; μ] = lrCov γ i j * twoSidedMin s t

end MatedCRT

end MatedCRTHarmonic
