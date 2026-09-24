/- First-moment and addition criteria for vanishing errors.

Moved from Parking-Sharpness.
-/
import Mathlib
open MeasureTheory Filter Topology
namespace LatticeProb.Scaling.VanishingMass

/-- Uniformly bounded expected mass times an arbitrarily small coefficient vanishes in probability. -/
theorem tendsto_measure_gt_zero {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {L : Filter ι} {e m : ι → Ω → ℝ}
    (hnonneg : ∀ᶠ i in L, ∀ ω, 0 ≤ m i ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ᶠ i in L, Integrable (m i) μ ∧ (∫ ω, m i ω ∂μ) ≤ C)
    (herror : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in L, ∀ ω, |e i ω| ≤ δ * m i ω)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => (μ {ω | a < |e i ω|}).toReal) L (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := a * η / (2 * (C + 1))
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := div_pos (mul_pos ha hη) hden
  have hδeq : δ * (2 * (C + 1)) = a * η := div_mul_cancel₀ _ hden.ne'
  filter_upwards [hnonneg, hmass, herror δ hδ] with i hn hm he
  have hsub : μ {ω | a < |e i ω|} ≤ μ {ω | a ≤ δ * m i ω} :=
    measure_mono fun ω hω => (le_of_lt hω).trans (he ω)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => mul_nonneg hδ.le (hn ω)) (hm.1.const_mul δ) a
  rw [integral_const_mul] at hMarkov
  have htail : a * (μ {ω | a < |e i ω|}).toReal ≤ δ * C := by
    calc
      a * (μ {ω | a < |e i ω|}).toReal ≤ a * (μ {ω | a ≤ δ * m i ω}).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hsub) ha.le
      _ ≤ δ * ∫ ω, m i ω ∂μ := hMarkov
      _ ≤ δ * C := mul_le_mul_of_nonneg_left hm.2 hδ.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  nlinarith

/-- The sum of two errors vanishing in probability also vanishes in probability. -/
theorem tendsto_measure_add_gt_zero {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {L : Filter ι} {e f : ι → Ω → ℝ}
    (he : ∀ a : ℝ, 0 < a → Tendsto (fun i => (μ {ω | a < |e i ω|}).toReal) L (𝓝 0))
    (hf : ∀ a : ℝ, 0 < a → Tendsto (fun i => (μ {ω | a < |f i ω|}).toReal) L (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => (μ {ω | a < |e i ω + f i ω|}).toReal) L (𝓝 0) := by
  have hlim := (he (a / 2) (half_pos ha)).add (hf (a / 2) (half_pos ha))
  rw [zero_add] at hlim
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hlim
  intro i
  have hsub : {ω | a < |e i ω + f i ω|} ⊆ {ω | a / 2 < |e i ω|} ∪ {ω | a / 2 < |f i ω|} := by
    intro ω hω
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at h
    have := abs_add_le (e i ω) (f i ω)
    change a < |e i ω + f i ω| at hω
    linarith
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
end LatticeProb.Scaling.VanishingMass
