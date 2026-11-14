import LatticeProb.Analysis.WeakLaplaceW2p

/-!
# Measurable weak Hessians of `W^{2,p}` limits of smooth approximate solutions

This file restates `weakHessian_of_hessianLp` with the measurability of the limit Hessian `G`
added to its conclusion (`weakHessianW2p_meas`). Let `U` be an open subset of a finite-dimensional
real inner product space with an additive Haar measure `μ`, let `1 ≤ p < ∞`, and assume the
interior `L^p` Hessian bound. If `uε n` is smooth on `{x | closedBall x (ε n) ⊆ U}` with
`Δ (uε n) = sε n` there, `ε n → 0`, `uε n → u` uniformly on compact subsets of `U` and `sε n → s`
in `L^p` on compact subsets of `U`, then there is a measurable `G` such that the Hessians
`D² (uε n)` converge to `G` in `L^p` on compact subsets of `U`, and `G` is the weak Hessian of `u`
in `U`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped InnerProductSpace ContDiff ENNReal
open Laplacian

namespace LatticeProb.PegdenSmart

/-- **Measurable `W^{2,p}` limit and weak Hessian of smooth approximate solutions of `Δ u = s`**,
given the interior `L^p` Hessian bound for the exponent `p` as a hypothesis. If `uε n` is smooth on
`{x | closedBall x (ε n) ⊆ U}` with `Δ (uε n) = sε n` there, `ε n → 0`, `uε n → u` uniformly on
compact subsets of `U` and `sε n → s` in `L^p` on compact subsets of `U`, then the Hessians
`D² (uε n)` converge in `L^p` on compact subsets of `U` to some measurable `G`, and
`∫ u ∂_v ∂_w φ = ∫ G(v, w) φ` for every smooth `φ` with compact support in `U`. -/
theorem weakHessianW2p_meas : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
    (∀ (a : E) (r : ℝ), 0 < r → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : E → ℝ, ContDiffOn ℝ ∞ w (ball a r) →
      eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ w) x‖) p (μ.restrict (ball a (r / 2))) ≤
        C * (eLpNorm (Δ w) p (μ.restrict (ball a r)) + eLpNorm w ⊤ (μ.restrict (ball a r)))) →
    ∀ (U : Set E) (u s : E → ℝ) (uε sε : ℕ → E → ℝ) (ε : ℕ → ℝ),
    IsOpen U → (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
    (∀ n, ContDiffOn ℝ ∞ (uε n) {x | closedBall x (ε n) ⊆ U}) →
    (∀ n, ∀ x ∈ {x | closedBall x (ε n) ⊆ U}, Δ (uε n) x = sε n x) →
    (∀ C : Set E, IsCompact C → C ⊆ U → TendstoUniformlyOn uε u atTop C) →
    (∀ C : Set E, IsCompact C → C ⊆ U →
      Tendsto (fun n => eLpNorm (C.indicator fun x => sε n x - s x) p μ) atTop (𝓝 0)) →
    ∃ G : E → (E →L[ℝ] E →L[ℝ] ℝ), Measurable G ∧
      (∀ C : Set E, IsCompact C → C ⊆ U →
        Tendsto (fun n => eLpNorm (C.indicator fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x) p μ)
          atTop (𝓝 0)) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v w : E,
        ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v w ∂μ = ∫ x, G x v w * φ x ∂μ) := by
  intro E _ _ _ _ _ μ _ p hp hp_top hQ2 U u s uε sε ε hU _ hε hsmooth hΔ hunif hsε
  obtain ⟨G, hGm, hG⟩ := exists_measurable_tendsto_eLpNorm_norm_hessian_sub hp hU hε hsmooth
    fun C hC hCU =>
      tendsto_eLpNorm_indicator_norm_hessian_sub hp hQ2 hU hε hsmooth hΔ hunif hsε hC hCU
  have : ContinuousSub (E →L[ℝ] E →L[ℝ] ℝ) :=
    IsTopologicalAddGroup.to_continuousSub (G := E →L[ℝ] E →L[ℝ] ℝ)
  refine ⟨G, hGm, fun C hC hCU => (hG C hC hCU).congr fun n => by
    exact eLpNorm_indicator_norm_eq (f := fun x => fderiv ℝ (fderiv ℝ (uε n)) x - G x)
      hC.isClosed.measurableSet
      ((measurable_fderiv ℝ (fderiv ℝ (uε n))).sub hGm).aestronglyMeasurable,
    fun φ hφ hφc hφU v w =>
      integral_mul_fderiv_fderiv_eq_of_tendsto hp hp_top hU hε hsmooth hunif hGm hG hφ hφc hφU v w⟩

end LatticeProb.PegdenSmart
