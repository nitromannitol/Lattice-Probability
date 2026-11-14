import Mathlib

/-! # Smooth approximations of a `W^{2,p}` function

`IsW2pApprox μ p U u uε ε G` records a function `u` on an open set `U` with smooth
approximations `uε n`, each smooth on the inner parallel set `{x | closedBall x (ε n) ⊆ U}`,
converging to `u` uniformly on compact subsets of `U`, whose Hessians converge in `L^p(μ)`
on compact subsets of `U` to a measurable `G`.
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- Smooth approximations `uε n` of `u` on `U` with Hessians converging to `G` in `L^p` on compact
subsets of `U`. -/
def IsW2pApprox {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (p : ℝ≥0∞) (U : Set E) (u : E → ℝ)
    (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  IsOpen U ∧ (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
  (∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U}) ∧
  (∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C) ∧
  Measurable G ∧
  (∀ C : Set E, IsCompact C → C ⊆ U →
    Tendsto (fun n => eLpNorm (C.indicator fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x) p μ)
      atTop (𝓝 0))

end LatticeProb.PegdenSmart
