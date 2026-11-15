import LatticeProb.LQG.LocalAreaFullTrace

/-! # Skipped time in a locally identified quantum area -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Metric
open LQGMetric MatedCRTHarmonic LatticeProb.Gauss

namespace LatticeProb.LQG

/-- The times outside the specified open intervals whose image is in the unit
    disk are null, under a local area identity and the stated trace and endpoint
    assumptions. -/
theorem ae_local_skipped_time_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → DistC} (hX : LQGMetric.IsWholePlaneGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hcircle : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂volume,
      hcirc ω (dyadicScale k) z = circleAvg (X ω) (dyadicScale k) z)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {g : Ω → C(ℝ, ℂ)} (hgm : Measurable g) (hind : IndepFun g X P)
    (hnull : ∀ᵐ ω ∂P, volume (range (g ω)) = 0)
    {ν : Ω → Measure ℂ}
    (hloc : ∀ᵐ ω ∂P, (ν ω).restrict (ball (0 : ℂ) 1) =
      (CellScaling.lqgArea γ (GMSCase.addLogSing α (X ω))).restrict (ball 0 1))
    (f : Ω → C(ℝ, ℂ)) (a b : ℝ) (σ τ : Ω → ℝ → ℝ)
    (hmap : ∀ᵐ ω ∂P, volume.map (f ω) = ν ω)
    (hends : ∀ᵐ ω ∂P, ∀ t ∈ Icc a b, σ ω t ≤ t ∧ t ≤ τ ω t ∧
      f ω (σ ω t) = g ω t ∧ f ω (τ ω t) = g ω t) :
    ∀ᵐ ω ∂P, volume ((Icc a b \ ⋃ t ∈ Icc a b, Ioo (σ ω t) (τ ω t)) ∩
      (f ω) ⁻¹' ball (0 : ℂ) 1) = 0 := by
  have htrace := ae_localArea_range_eq_zero_of_indep_field hX hh hcircle
    hγ0 hγ2 hα hgm hind hnull hloc
  filter_upwards [htrace, hmap, hends] with ω htr hm he
  have hmeas : MeasurableSet ((g ω '' Icc a b) ∩ ball (0 : ℂ) 1) :=
    (isCompact_Icc.image (g ω).continuous).isClosed.measurableSet.inter isOpen_ball.measurableSet
  have hzero : ν ω ((g ω '' Icc a b) ∩ ball (0 : ℂ) 1) = 0 :=
    measure_mono_null (inter_subset_inter_left _ (image_subset_range _ _)) htr
  have hpre : volume ((f ω) ⁻¹' ((g ω '' Icc a b) ∩ ball (0 : ℂ) 1)) = 0 := by
    rw [← Measure.map_apply (f ω).continuous.measurable hmeas, hm]
    exact hzero
  apply measure_mono_null _ hpre
  intro t ht
  have hnot : t ∉ Ioo (σ ω t) (τ ω t) := by
    intro hin
    exact ht.1.2 (mem_iUnion.2 ⟨t, mem_iUnion.2 ⟨ht.1.1, hin⟩⟩)
  obtain ⟨hst, hte, hs, he'⟩ := he t ht.1.1
  have heq : f ω t = g ω t := by
    by_cases hst' : σ ω t = t
    · simpa only [hst'] using hs
    · have hlt : σ ω t < t := lt_of_le_of_ne hst hst'
      have hte' : t = τ ω t := le_antisymm hte (le_of_not_gt (fun h => hnot ⟨hlt, h⟩))
      simpa only [← hte'] using he'
  exact ⟨⟨t, ht.1.1, heq.symm⟩, ht.2⟩

end LatticeProb.LQG
