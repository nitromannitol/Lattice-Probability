import Mathlib
import LatticeProb.Analysis.W2pApprox

/-! # Limit of the gradients of `W^{2,p}` approximations

Let `uε n` be smooth approximations of `u` on an open set `U` in the sense of `IsW2pApprox`. If the
gradients `fderiv ℝ (uε n)` are uniformly Cauchy on every compact subset of `U`, then they converge
uniformly on compact subsets of `U` to a function `V` continuous on `U`, and `u` has derivative
`V x` at every `x ∈ U`.

The limit `V` is the pointwise limit of the gradients. Near a point `x` of `U`, the approximations
are eventually smooth on a ball around `x`, so `V` is continuous there as a uniform limit of
continuous functions, and the derivative of `u` at `x` follows from
`hasFDerivAt_of_tendstoUniformlyOnFilter`.

## Main statement

* `LatticeProb.PegdenSmart.gradientLimit_of_uniformCauchy`
-/

open MeasureTheory Metric Filter Topology Asymptotics Set
open scoped InnerProductSpace ContDiff ENNReal NNReal

namespace LatticeProb.PegdenSmart

/-- If the gradients of `W^{2,p}` approximations are uniformly Cauchy on compact subsets of `U`,
then they converge uniformly on compact subsets of `U` to a continuous `V`, and `u` has
derivative `V` on `U`. -/
theorem gradientLimit_of_uniformCauchy
    (h5 : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
        IsW2pApprox μ p U u uε ε G →
        ∀ C : Set E, IsCompact C → C ⊆ U → UniformCauchySeqOn (fun n => fderiv ℝ (uε n)) atTop C) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
      (p : ℝ≥0∞), (Module.finrank ℝ E : ℝ≥0∞) < p → p ≠ ⊤ →
      ∀ (U : Set E) (u : E → ℝ) (uε : ℕ → E → ℝ) (ε : ℕ → ℝ) (G : E → E →L[ℝ] E →L[ℝ] ℝ),
        IsW2pApprox μ p U u uε ε G →
        ∃ V : E → E →L[ℝ] ℝ, ContinuousOn V U ∧
          (∀ C : Set E, IsCompact C → C ⊆ U →
            TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop C) ∧
          ∀ x ∈ U, HasFDerivAt u (V x) x := by
  intro E _ _ _ _ _ _ μ _ p hp hpt U u uε ε G h
  have hcau := h5 E μ p hp hpt U u uε ε G h
  obtain ⟨hU, -, hε, hsmooth, hunif, -, -⟩ := h
  obtain ⟨V, hlim⟩ : ∃ V : E → E →L[ℝ] ℝ, ∀ x ∈ U,
      Tendsto (fun n => fderiv ℝ (uε n) x) atTop (𝓝 (V x)) :=
    ⟨fun x => limUnder atTop fun n => fderiv ℝ (uε n) x, fun x hx =>
      ((hcau {x} isCompact_singleton (singleton_subset_iff.2 hx)).cauchySeq
        (mem_singleton x)).tendsto_limUnder⟩
  have hVunif : ∀ C : Set E, IsCompact C → C ⊆ U →
      TendstoUniformlyOn (fun n => fderiv ℝ (uε n)) V atTop C := fun C hC hCU =>
    (hcau C hC hCU).tendstoUniformlyOn_of_tendsto fun x hx => hlim x (hCU hx)
  have hloc : ∀ x ∈ U, ∃ r > 0, closedBall x r ⊆ U ∧
      ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (uε n) (ball x r) := by
    intro x hx
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
    refine ⟨R / 2, half_pos hR, (closedBall_subset_ball (half_lt_self hR)).trans hRU, ?_⟩
    filter_upwards [hε.eventually (eventually_lt_nhds (half_pos hR))] with n hn
    refine (hsmooth n).mono fun y hy z hz => hRU ?_
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  refine ⟨V, fun x hx => ?_, hVunif, fun x hx => ?_⟩
  · obtain ⟨r, hr, hrU, hev⟩ := hloc x hx
    have hcont : ContinuousOn V (ball x r) :=
      ((hVunif _ (isCompact_closedBall x r) hrU).mono ball_subset_closedBall).continuousOn
        (hev.mono fun n hn => hn.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).frequently
    exact (hcont.continuousAt (ball_mem_nhds x hr)).continuousWithinAt
  · obtain ⟨r, hr, hrU, hev⟩ := hloc x hx
    have hball : ∀ᶠ y in 𝓝 x, y ∈ ball x r := isOpen_ball.eventually_mem (mem_ball_self hr)
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := atTop) (f := uε)
      (f' := fun n => fderiv ℝ (uε n)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.1
        ((hVunif _ (isCompact_closedBall x r) hrU).mono ball_subset_closedBall)).mono_right
          (le_principal_iff.2 (ball_mem_nhds x hr))
    · filter_upwards [hev.prod_mk hball] with q hq
      exact ((hq.1.contDiffAt (isOpen_ball.mem_nhds hq.2)).differentiableAt
        (by simp)).hasFDerivAt
    · filter_upwards [hball] with y hy
      exact (hunif _ (isCompact_closedBall x r) hrU).tendsto_at (ball_subset_closedBall hy)

end LatticeProb.PegdenSmart
