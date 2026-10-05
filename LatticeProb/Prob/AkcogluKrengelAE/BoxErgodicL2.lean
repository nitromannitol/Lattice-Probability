/-
# The `L²` mean ergodic step for the multiparameter cube averages

The library's anchored-cube theorem `LatticeProb.exists_ae_tendsto_gridAvg_univ_with_integral`
(`BoundedErgodic.lean:561`) gives, for a measure-preserving additive `ℤ^d` action `σ` and a bounded
measurable `h`, an a.e. limit `G` of the cube averages `gridAvg σ h univ n` with `∫G = ∫h`.

This file adds the **mean (`L²`) convergence** of those averages, the `L²` mean ergodic step of the
multiparameter pointwise ergodic theorem: `∫ |gridAvg σ h univ n - G|² → 0`.  It is a dominated
convergence corollary of the a.e. theorem, with dominating constant `(2M)²`.
-/
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodic

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The `L²` mean ergodic step.**  For a measure-preserving additive action `σ` of `ℤ^d` on a
probability space and a bounded measurable `h`, there is a bounded measurable limit `G` with
`∫ G = ∫ h` such that the cube averages converge to `G` in `L²`,
`∫ |gridAvg σ h univ n - G|² → 0`. -/
theorem gridAvg_univ_l2_tendsto {d : ℕ} {σ : Site d → Ω → Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hσ : ∀ z, MeasurePreserving (σ z) μ μ) (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M) :
    ∃ G : Ω → ℝ, Measurable G ∧ (∀ x, |G x| ≤ M) ∧ ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ ∧
      Tendsto (fun n : ℕ => ∫ ω, (gridAvg σ h Finset.univ n ω - G ω) ^ 2 ∂μ)
        atTop (𝓝 0) := by
  obtain ⟨G, hGm, hGb, hGint, hG⟩ :=
    exists_ae_tendsto_gridAvg_univ_with_integral hσ hσadd hh hM hb
  refine ⟨G, hGm, hGb, hGint, ?_⟩
  have hF_aesm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => (gridAvg σ h Finset.univ n ω - G ω) ^ 2) μ := by
    intro n
    exact (((measurable_gridAvg hσ hh Finset.univ n).sub hGm).pow_const 2).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ‖(gridAvg σ h Finset.univ n ω - G ω) ^ 2‖ ≤ (2 * M) ^ 2 := by
    intro n
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := abs_gridAvg_le σ h hM hb Finset.univ n ω
    have h2 := hGb ω
    have h3 : |gridAvg σ h Finset.univ n ω - G ω| ≤ 2 * M := by
      calc |gridAvg σ h Finset.univ n ω - G ω|
          ≤ |gridAvg σ h Finset.univ n ω| + |G ω| := abs_sub _ _
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring
    exact sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
  have hconv : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (gridAvg σ h Finset.univ n ω - G ω) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hG] with ω hω
    have h0 : Tendsto (fun n : ℕ => gridAvg σ h Finset.univ n ω - G ω) atTop (𝓝 0) := by
      simpa using hω.sub_const (G ω)
    simpa using h0.pow 2
  have hmain := tendsto_integral_of_dominated_convergence (fun _ : Ω => (2 * M) ^ 2)
    hF_aesm (integrable_const _) hbound hconv
  simpa using hmain

end LatticeProb
