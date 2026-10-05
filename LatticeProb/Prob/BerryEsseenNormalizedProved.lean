/-
# The normalised Berry-Esseen theorem

`BerryEsseenNormalized.lean` derives the Berry-Esseen bound for a sum of independent centred
summands of total variance one from Esseen's smoothing inequality for the standard Gaussian,
taken there as the hypothesis `EsseenGaussianInequality`.  `EsseenSmoothing.lean` proves that
inequality (for every Gaussian variance).  This file puts the two together.

* `esseenGaussianInequality_holds`: the hypothesis is a theorem.
* `berryEsseen_normalized`: for independent centred laws `ν i` with finite third absolute moments
  and `∑ Var = 1`, the distribution function of the sum differs from the standard normal one by at
  most `100 ∑ ∫ |z|³ dν i`.
-/
import Mathlib
import LatticeProb.Prob.BerryEsseenNormalized
import LatticeProb.Prob.EsseenSmoothing

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- Esseen's smoothing inequality for the standard Gaussian. -/
theorem esseenGaussianInequality_holds : EsseenGaussianInequality := by
  intro μ _ hμ T hT x
  simpa using esseen_smoothing_gaussian (v := 1) hμ one_pos hT x

/-- **Normalised Berry-Esseen**: a sum of independent centred variables with finite third absolute
moments and total variance one is within `100 ∑ ∫ |z|³ dν i` of the standard normal law in
Kolmogorov distance. -/
theorem berryEsseen_normalized {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hmean : ∀ i, ∫ z, z ∂(ν i) = 0)
    (h3 : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (ν i))
    (hvar : ∑ i, variance id (ν i) = 1) (x : ℝ) :
    |(sumLaw ν (Set.Iic x)).toReal - (gaussianReal 0 1 (Set.Iic x)).toReal|
      ≤ 100 * ∑ i, ∫ z, |z| ^ 3 ∂(ν i) :=
  berryEsseen_normalized_of_esseen esseenGaussianInequality_holds ν hmean h3 hvar x

end LatticeProb
