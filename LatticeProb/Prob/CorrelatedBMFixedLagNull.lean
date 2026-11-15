import LatticeProb.Prob.CorrelatedBMIncrementGaussian

/-! # Null zero sets of fixed Brownian increments -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- Each fixed nonzero lag has a Lebesgue-null set of equal coordinate values,
for almost every path of a two-sided correlated Brownian pair. -/
theorem ae_volume_increment_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) {d : ℝ} (hd : d ≠ 0) :
    ∀ᵐ ω ∂μ, volume {t : ℝ | lrCoord i t ω = lrCoord i (t + d) ω} = 0 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
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
  have hmeas : MeasurableSet {p : ℝ × Path2 | lrCoord i p.1 p.2 ≠ lrCoord i (p.1 + d) p.2} := by
    have hm' : Measurable (fun p : ℝ × Path2 => lrCoord i (p.1 + d) p.2) :=
      hm.comp ((measurable_fst.add measurable_const).prodMk measurable_snd)
    exact (measurableSet_eq_fun hm hm').compl
  have hsections : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ ω ∂μ,
      lrCoord i t ω ≠ lrCoord i (t + d) ω := by
    apply ae_of_all
    intro t
    have hv : (|t - (t + d)|).toNNReal ≠ 0 := by
      apply ne_of_gt
      exact Real.toNNReal_pos.mpr (abs_pos.mpr (by intro h; apply hd; linarith))
    have hz : μ {ω | coneIncr i t (t + d) ω = 0} = 0 := by
      have hmap := map_coneIncr_eq_gaussianReal hμ i t (t + d)
      have hz' : gaussianReal 0 (|t - (t + d)|).toNNReal {0} = 0 :=
        gaussianReal_absolutelyContinuous _ hv (measure_singleton 0)
      rw [← hmap, Measure.map_apply (measurable_coneIncr i t (t + d)) (measurableSet_singleton 0)] at hz'
      exact hz'
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with ω hω
    intro heq
    apply hω
    simp [coneIncr, heq]
  filter_upwards [(Measure.ae_ae_comm hmeas).1 hsections] with ω hω
  exact measure_eq_zero_iff_ae_notMem.mpr hω

/-- At a fixed positive mesh, the nonzero integer grid lags satisfy the
increment nullity condition simultaneously. -/
theorem ae_volume_grid_increments_eq_zero {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ i : Fin 2, ∀ n : ℤ, n ≠ 0 →
      volume {t : ℝ | lrCoord i t ω = lrCoord i (t + ε * n) ω} = 0 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro n
  by_cases hn : n = 0
  · exact ae_of_all _ (by simp [hn])
  · have hd : ε * (n : ℝ) ≠ 0 := mul_ne_zero (ne_of_gt hε) (by exact_mod_cast hn)
    filter_upwards [ae_volume_increment_eq_zero hμ i hd] with ω hω _
    exact hω

end LatticeProb.CorrelatedBM
