import LatticeProb.Prob.CorrelatedBMIncrementGaussian

/-! # Null level sets of correlated Brownian coordinates -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Almost surely every level set of each coordinate has zero Lebesgue measure. -/
theorem ae_volume_coordinate_levels_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ y : ℝ,
      volume {t : ℝ | lrCoord i t ω = y} = 0 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply ae_all_iff.mpr
  intro i
  have hcont (ω : Path2) : Continuous (fun t => lrCoord i t ω) := by
    by_cases hi : i = 0
    · subst i
      simpa [lrCoord, Function.comp_def] using continuous_fst.comp ω.continuous
    · simpa [lrCoord, hi, Function.comp_def] using continuous_snd.comp ω.continuous
  have hm : Measurable (Function.uncurry fun (t : ℝ) (ω : Path2) => lrCoord i t ω) := by
    exact measurable_uncurry_of_continuous_of_measurable hcont
      (fun t => by
        unfold lrCoord
        split_ifs
        · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
        · exact measurable_snd.comp (ContinuousMap.measurable_eval t))
  have hmeas : MeasurableSet {p : (ℝ × ℝ) × Path2 |
      lrCoord i p.1.1 p.2 ≠ lrCoord i p.1.2 p.2} := by
    have h₁ : Measurable (fun p : (ℝ × ℝ) × Path2 => lrCoord i p.1.1 p.2) :=
      hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h₂ : Measurable (fun p : (ℝ × ℝ) × Path2 => lrCoord i p.1.2 p.2) :=
      hm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (measurableSet_eq_fun h₁ h₂).compl
  have hpairs : ∀ᵐ p ∂((volume : Measure ℝ).prod volume), ∀ᵐ ω ∂μ,
      lrCoord i p.1 ω ≠ lrCoord i p.2 ω := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · apply ae_of_all
      intro t
      filter_upwards [Measure.ae_ne volume t] with s hst
      have hv : (|t - s|).toNNReal ≠ 0 := by
        apply ne_of_gt
        exact Real.toNNReal_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hst.symm))
      have hz : μ {ω | coneIncr i t s ω = 0} = 0 := by
        have hmap := map_coneIncr_eq_gaussianReal hμ i t s
        have hz' : gaussianReal 0 (|t - s|).toNNReal {0} = 0 :=
          gaussianReal_absolutelyContinuous _ hv (measure_singleton 0)
        rw [← hmap, Measure.map_apply (measurable_coneIncr i t s) (measurableSet_singleton 0)] at hz'
        exact hz'
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with ω hω
      intro heq
      apply hω
      simp [coneIncr, heq]
    · have hsec : Measurable (fun p : ℝ × ℝ =>
          μ {ω | lrCoord i p.1 ω = lrCoord i p.2 ω}) := by
        simpa only [Set.preimage, Set.mem_compl_iff, mem_ofPred_eq, not_ne_iff] using
          (measurable_measure_prodMk_left (ν := μ) hmeas.compl)
      have hzero : MeasurableSet {p : ℝ × ℝ |
          μ {ω | lrCoord i p.1 ω = lrCoord i p.2 ω} = 0} :=
        measurableSet_eq_fun hsec measurable_const
      simp only [measure_eq_zero_iff_ae_notMem] at hzero
      change MeasurableSet {p : ℝ × ℝ | ∀ᵐ ω ∂μ,
        lrCoord i p.1 ω ≠ lrCoord i p.2 ω} at hzero
      exact hzero
  have hpath := (Measure.ae_ae_comm hmeas).1 hpairs
  filter_upwards [hpath] with ω hω
  have hω' := Measure.ae_ae_of_ae_prod hω
  intro y
  by_contra hn
  apply hn
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hω'] with t ht
  intro hty
  apply hn
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ht] with s hs
  intro hsy
  exact hs (hty.trans hsy.symm)

end LatticeProb.CorrelatedBM
