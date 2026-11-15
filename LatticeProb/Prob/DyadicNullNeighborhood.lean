import LatticeProb.Prob.VanishingUniformNullNeighborhood

/-! # Dyadic neighborhoods of common null sets -/

set_option autoImplicit false

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- Dyadic neighborhoods of a common closed null set have uniformly small mass
for finitely many continuous compact families of probability measures. -/
theorem eventually_uniform_dyadic_thickening_lt_of_finite_compact_null
    {X J : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype J]
    (P : J → Type*) [∀ j, TopologicalSpace (P j)] [∀ j, CompactSpace (P j)]
    (ν : ∀ j, P j → ProbabilityMeasure X) (hν : ∀ j, Continuous (ν j))
    (F : Set X) (hF : IsClosed F) (hnull : ∀ j p, (ν j p : Measure X) F = 0)
    (S : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j p,
      (ν j p : Measure X) (thickening ((2 * S / (2 : ℝ) ^ n) / 2) F) < ε := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hr : Tendsto (fun n : ℕ => (2 * S / (2 : ℝ) ^ n) / 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => S * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hpow.const_mul S
    convert ht using 1
    ext n
    rw [div_pow]
    ring
  exact eventually_uniform_thickening_lt_of_finite_compact_null P ν hν F hF hnull
    atTop _ hr hε

end LatticeProb
