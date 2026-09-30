/- Vanishing in probability from deterministic error bounds and uniform first moments.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory Filter Topology

namespace LatticeProb.Scaling.VanishingMassError

/-- A first-moment bound controls a tail event dominated by nonnegative mass. -/
theorem measure_gt_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f Y : Ω → ℝ} {δ a : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 < a) (hY : ∀ ω, 0 ≤ Y ω) (hI : Integrable Y μ)
    (hdom : ∀ ω, |f ω| ≤ δ * Y ω) :
    (μ {ω | a < |f ω|}).toReal ≤ δ * (∫ ω, Y ω ∂μ) / a := by
  have hsub : μ {ω | a < |f ω|} ≤ μ {ω | a ≤ δ * Y ω} :=
    measure_mono fun ω hω => hω.le.trans (hdom ω)
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) hsub
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => mul_nonneg hδ (hY ω)) (hI.const_mul δ) a
  rw [integral_const_mul] at hMarkov
  rw [le_div_iff₀ ha]
  exact (mul_le_mul_of_nonneg_right hm ha.le).trans (by
    simpa only [measureReal_def, mul_comm a] using hMarkov)

/-- An arbitrarily small multiple of mass with uniformly bounded first moment
vanishes in probability. The error itself need not be measurable. -/
theorem tendsto_measure_gt_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {L : Filter ι} {f Y : ι → Ω → ℝ}
    {C : ℝ} (hC : 0 ≤ C)
    (hY : ∀ᶠ i in L, ∀ ω, 0 ≤ Y i ω)
    (hI : ∀ᶠ i in L, Integrable (Y i) μ)
    (hbound : ∀ᶠ i in L, ∫ ω, Y i ω ∂μ ≤ C)
    (hdom : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in L, ∀ ω, |f i ω| ≤ δ * Y i ω)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => (μ {ω | a < |f i ω|}).toReal) L (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ := ε * a / (2 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hY, hI, hbound, hdom δ hδ] with i hYi hIi hBi hdi
  have htail := measure_gt_le_of_abs_le μ hδ.le ha hYi hIi hdi
  have hb : δ * (∫ ω, Y i ω ∂μ) / a ≤ δ * C / a :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBi hδ.le) ha.le
  have hc : δ * C / a < ε := by
    dsimp [δ]
    rw [div_lt_iff₀ ha]
    have hden : 0 < 2 * (C + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [mul_pos hε ha]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  exact htail.trans_lt (hb.trans_lt hc)

/-- The sum of two errors vanishing in probability also vanishes in probability. -/
theorem tendsto_measure_add_gt_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {L : Filter ι} {f g : ι → Ω → ℝ}
    (hf : ∀ a : ℝ, 0 < a → Tendsto (fun i => (μ {ω | a < |f i ω|}).toReal) L (𝓝 0))
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun i => (μ {ω | a < |g i ω|}).toReal) L (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun i => (μ {ω | a < |f i ω + g i ω|}).toReal) L (𝓝 0) := by
  have hb : ∀ i, (μ {ω | a < |f i ω + g i ω|}).toReal ≤
      (μ {ω | a / 2 < |f i ω|}).toReal + (μ {ω | a / 2 < |g i ω|}).toReal := by
    intro i
    have hs : {ω | a < |f i ω + g i ω|} ⊆
        {ω | a / 2 < |f i ω|} ∪ {ω | a / 2 < |g i ω|} := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn
      have ht := abs_add_le (f i ω) (g i ω)
      dsimp only [Set.mem_setOf_eq] at hω
      linarith [hn.1, hn.2]
    have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)
      ((measure_mono hs).trans (measure_union_le _ _))
    simpa only [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] using ht
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
    (by simpa only [add_zero] using (hf (a / 2) (by positivity)).add (hg (a / 2) (by positivity)))

end LatticeProb.Scaling.VanishingMassError
