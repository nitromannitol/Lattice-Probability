import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! # A pairwise test for essential constancy -/

set_option autoImplicit false

open MeasureTheory Filter

namespace LatticeProb

/-- A measurable function is almost everywhere constant exactly when its
pairwise bounded-distance integral vanishes. -/
theorem lintegral_bounded_dist_eq_zero_iff_ae_constant
    {α E : Type*} [MeasurableSpace α] [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure α) [SFinite μ]
    (hμ : μ ≠ 0) (f : α → E) (hf : Measurable f) :
    (∫⁻ z : α × α, ENNReal.ofReal (min 1 (dist (f z.1) (f z.2))) ∂(μ.prod μ)) = 0 ↔
      ∃ c : E, ∀ᵐ x ∂μ, f x = c := by
  have hd : Measurable (fun z : α × α => min 1 (dist (f z.1) (f z.2))) :=
    measurable_const.min ((hf.comp measurable_fst).dist (hf.comp measurable_snd))
  have hzero (z : α × α) :
      ENNReal.ofReal (min 1 (dist (f z.1) (f z.2))) = 0 ↔ f z.1 = f z.2 := by
    rw [ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      have : dist (f z.1) (f z.2) ≤ 0 := by
        rcases min_le_iff.mp h with h | h
        · norm_num at h
        · exact h
      exact dist_eq_zero.mp (le_antisymm this dist_nonneg)
    · intro h
      simp [h]
  rw [lintegral_eq_zero_iff hd.ennreal_ofReal]
  change (∀ᵐ z ∂(μ.prod μ), ENNReal.ofReal (min 1 (dist (f z.1) (f z.2))) = 0) ↔ _
  simp_rw [hzero]
  constructor
  · intro h
    have : (ae μ).NeBot := ae_neBot.mpr hμ
    obtain ⟨x, hx⟩ := (Measure.ae_ae_of_ae_prod h).exists
    exact ⟨f x, hx.mono fun _ hxy => hxy.symm⟩
  · rintro ⟨c, hc⟩
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · filter_upwards [hc] with x hx
      filter_upwards [hc] with y hy
      exact hx.trans hy.symm
    · have hm : MeasurableSet {z : α × α | min 1 (dist (f z.1) (f z.2)) = 0} :=
        measurableSet_eq_fun hd measurable_const
      convert hm using 1
      ext z
      change f z.1 = f z.2 ↔ min 1 (dist (f z.1) (f z.2)) = 0
      rw [← hzero z, ENNReal.ofReal_eq_zero]
      exact ⟨fun h => le_antisymm h (le_min (by norm_num) dist_nonneg), fun h => h.le⟩

end LatticeProb
