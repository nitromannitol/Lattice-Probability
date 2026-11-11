import Mathlib

/-!
# Almost sure convergence from summable mean increments

A sequence of random variables `Y k` with values in a complete space whose consecutive increments have summable
expectations, `∑ₖ E[dist (Y k) (Y (k+1))] < ∞`, converges almost surely: by Tonelli the series of the increments has
finite expectation, so it is finite almost surely, and the sequence is then Cauchy. This is the first Borel-Cantelli
type step used to pass from an `L¹` rate along a geometric sequence of scales to almost sure convergence.

## Main statements

* `LatticeProb.SummableIncrements.ae_cauchySeq_of_tsum_lintegral_edist_ne_top`: a.e. Cauchy.
* `LatticeProb.SummableIncrements.ae_exists_tendsto_of_tsum_lintegral_edist_ne_top`: a.e. convergent, in a complete
  space.
* `LatticeProb.SummableIncrements.ae_exists_tendsto_of_lintegral_edist_le`: the same with a summable bound.
* `LatticeProb.SummableIncrements.ae_exists_tendsto_of_summable_integral_abs_sub` and
  `ae_exists_tendsto_of_integral_abs_sub_le`: real random variables with integrable increments.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace LatticeProb.SummableIncrements

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {E : Type*}

/-- If the expected consecutive distances of a sequence of random variables are summable, the sequence is almost
everywhere Cauchy. -/
theorem ae_cauchySeq_of_tsum_lintegral_edist_ne_top [PseudoEMetricSpace E] {Y : ℕ → Ω → E}
    (hm : ∀ k, AEMeasurable (fun ω => edist (Y k ω) (Y (k + 1) ω)) μ)
    (h : ∑' k, ∫⁻ ω, edist (Y k ω) (Y (k + 1) ω) ∂μ ≠ ∞) :
    ∀ᵐ ω ∂μ, CauchySeq fun k => Y k ω := by
  have h1 : ∫⁻ ω, ∑' k, edist (Y k ω) (Y (k + 1) ω) ∂μ ≠ ∞ := by
    rw [lintegral_tsum hm]
    exact h
  have h2 : AEMeasurable (fun ω => ∑' k, edist (Y k ω) (Y (k + 1) ω)) μ := AEMeasurable.tsum hm
  filter_upwards [ae_lt_top' h2 h1] with ω hω
  exact cauchySeq_of_edist_le_of_tsum_ne_top _ (fun n => le_rfl) hω.ne

/-- If the expected consecutive distances of a sequence of random variables with values in a complete space are
summable, the sequence converges almost everywhere. -/
theorem ae_exists_tendsto_of_tsum_lintegral_edist_ne_top [PseudoEMetricSpace E] [CompleteSpace E] {Y : ℕ → Ω → E}
    (hm : ∀ k, AEMeasurable (fun ω => edist (Y k ω) (Y (k + 1) ω)) μ)
    (h : ∑' k, ∫⁻ ω, edist (Y k ω) (Y (k + 1) ω) ∂μ ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun k => Y k ω) atTop (𝓝 l) := by
  filter_upwards [ae_cauchySeq_of_tsum_lintegral_edist_ne_top hm h] with ω hω
  exact cauchySeq_tendsto_of_complete hω

/-- Almost everywhere convergence when the expected consecutive distances are bounded by a summable sequence. -/
theorem ae_exists_tendsto_of_lintegral_edist_le [PseudoEMetricSpace E] [CompleteSpace E] {Y : ℕ → Ω → E}
    (hm : ∀ k, AEMeasurable (fun ω => edist (Y k ω) (Y (k + 1) ω)) μ) {b : ℕ → ℝ≥0∞}
    (hb : ∀ k, ∫⁻ ω, edist (Y k ω) (Y (k + 1) ω) ∂μ ≤ b k) (hsum : ∑' k, b k ≠ ∞) :
    ∀ᵐ ω ∂μ, ∃ l, Tendsto (fun k => Y k ω) atTop (𝓝 l) :=
  ae_exists_tendsto_of_tsum_lintegral_edist_ne_top hm
    (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hb))

/-- A sequence of real random variables whose increments are integrable with summable `L¹` norms converges almost
everywhere. -/
theorem ae_exists_tendsto_of_summable_integral_abs_sub {Y : ℕ → Ω → ℝ}
    (hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) μ)
    (hsum : Summable fun k => ∫ ω, |Y (k + 1) ω - Y k ω| ∂μ) :
    ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun k => Y k ω) atTop (𝓝 l) := by
  have hed : ∀ k ω, edist (Y k ω) (Y (k + 1) ω) = ENNReal.ofReal |Y (k + 1) ω - Y k ω| := by
    intro k ω
    rw [edist_dist, Real.dist_eq, abs_sub_comm]
  have hlin : ∀ k, ∫⁻ ω, edist (Y k ω) (Y (k + 1) ω) ∂μ = ENNReal.ofReal (∫ ω, |Y (k + 1) ω - Y k ω| ∂μ) := by
    intro k
    simp_rw [hed]
    exact (ofReal_integral_eq_lintegral_ofReal (hint k).abs (ae_of_all _ fun ω => abs_nonneg _)).symm
  refine ae_exists_tendsto_of_tsum_lintegral_edist_ne_top (fun k => ?_) ?_
  · simp_rw [hed]
    exact (hint k).aestronglyMeasurable.aemeasurable.abs.ennreal_ofReal
  · simp_rw [hlin]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun ω => abs_nonneg _) hsum]
    exact ENNReal.ofReal_ne_top

/-- A sequence of real random variables whose increments are integrable with `L¹` norms bounded by a summable
sequence converges almost everywhere. -/
theorem ae_exists_tendsto_of_integral_abs_sub_le {Y : ℕ → Ω → ℝ}
    (hint : ∀ k, Integrable (fun ω => Y (k + 1) ω - Y k ω) μ) {b : ℕ → ℝ}
    (hb : ∀ k, ∫ ω, |Y (k + 1) ω - Y k ω| ∂μ ≤ b k) (hsum : Summable b) :
    ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun k => Y k ω) atTop (𝓝 l) :=
  ae_exists_tendsto_of_summable_integral_abs_sub hint
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _) hb hsum)

end LatticeProb.SummableIncrements
