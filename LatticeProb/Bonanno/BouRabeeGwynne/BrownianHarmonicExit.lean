/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianHarmonicExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianStoppedLimit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteExit
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExitStoppingTime
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedBrownianMeasurable

/-!
# Harmonic expectation at the actual Brownian exit

Bounded stopping is proved by dyadic Taylor sums. The actual almost-sure finite
exit then permits truncation bounds to tend to infinity. All laws below are
the actual canonical continuous Brownian law and its stopped-curve pushforward.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

lemma standardBrownianLaw_eval_zero_ae {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) :
    ∀ᵐ ω ∂μ, ω 0 = 0 := by
  have h : ∀ᵐ ω ∂μ, ∀ i : Fin d, ω 0 i = 0 :=
    ae_all_iff.mpr (fun i ↦ (hμ.2.1 i).eval_zero_ae_eq_zero)
  filter_upwards [h] with ω hω
  ext i
  exact hω i

theorem standardBrownianLaw_integral_exit_harmonic_compactSupport {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (hh : IsHarmonicOn f U) (z : Euc d) :
    (∫ ω, f (z + ω (continuousExitTime U z ω).toNNReal) ∂μ) = f z := by
  letI : IsProbabilityMeasure μ := hμ.1
  let τ : BrownianPath d → ℝ≥0∞ := continuousExitTime U z
  have hτ : IsStoppingTime (brownianNaturalFiltration d) τ := isStoppingTime_continuousExitTime hU z
  let σ : ℕ → BrownianPath d → ℝ≥0 := fun n ω ↦ (min (τ ω) (n : ℝ≥0∞)).toNNReal
  have hσeq (n : ℕ) : (fun ω ↦ (σ n ω : ℝ≥0∞)) = fun ω ↦ min (τ ω) (n : ℝ≥0∞) := by
    funext ω
    exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
  have hσstop (n : ℕ) : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ (σ n ω : ℝ≥0∞)) := by
    rw [hσeq]
    exact hτ.min_const (n : ℝ≥0)
  have hσbound (n : ℕ) (ω : BrownianPath d) : σ n ω ≤ (n : ℝ≥0) := by
    rw [← ENNReal.coe_le_coe, congrFun (hσeq n) ω]
    exact min_le_right _ _
  have hstay (n : ℕ) (ω : BrownianPath d) (t : ℝ≥0) (ht : t < σ n ω) : z + ω t ∈ U := by
    apply mem_of_lt_continuousExitTime
    have hle : (σ n ω : ℝ≥0∞) ≤ τ ω := by rw [congrFun (hσeq n) ω]; exact min_le_left _ _
    exact (ENNReal.coe_lt_coe.mpr ht).trans_le hle
  have hmean (n : ℕ) : (∫ ω, f (z + ω (σ n ω)) - f (z + ω 0) ∂μ) = 0 :=
    standardBrownianLaw_bounded_stopped_harmonic_difference hμ hf hsupp hh
      (hσstop n) (n : ℝ≥0) (hσbound n) z (hstay n)
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hmzero : Measurable (fun ω : BrownianPath d ↦ f (z + ω 0)) :=
    hf.continuous.measurable.comp (measurable_const.add (continuous_eval_const (0 : ℝ≥0)).measurable)
  have hmseq (n : ℕ) : Measurable (fun ω : BrownianPath d ↦ f (z + ω (σ n ω))) :=
    hf.continuous.measurable.comp (measurable_const.add
      (measurable_brownian_random_evaluation (measurable_nnreal_brownian_stopping (hσstop n))))
  have hdom (n : ℕ) : ∀ᵐ ω ∂μ, ‖f (z + ω (σ n ω)) - f (z + ω 0)‖ ≤ 2 * M := by
    filter_upwards [] with ω
    exact (norm_sub_le _ _).trans (by linarith [hM (z + ω (σ n ω)), hM (z + ω 0)])
  have hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞ := standardBrownianLaw_ae_finiteExit hd hμ hUb z
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f (z + ω (σ n ω)) - f (z + ω 0)) atTop
      (𝓝 (f (z + ω (τ ω).toNNReal) - f (z + ω 0))) := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ ω).toNNReal : ℝ)
    have heq : (fun n ↦ f (z + ω (σ n ω)) - f (z + ω 0)) =ᶠ[atTop]
        fun _ : ℕ ↦ f (z + ω (τ ω).toNNReal) - f (z + ω 0) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : τ ω ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hω]
        have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hreal : ((τ ω).toNNReal : ℝ) ≤ ((n : ℝ≥0) : ℝ) := by
          simpa only [NNReal.coe_natCast] using hN.le.trans hNn
        exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hreal)
      simp only [σ, min_eq_left hle]
    exact tendsto_const_nhds.congr' heq.symm
  have hint := tendsto_integral_of_dominated_convergence (fun _ : BrownianPath d ↦ 2 * M)
    (fun n ↦ ((hmseq n).sub hmzero).aestronglyMeasurable) (integrable_const _) hdom hlim
  have hdiff : (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ) = 0 :=
    tendsto_nhds_unique hint (by simpa only [Pi.sub_apply, hmean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)))
  have hmexit : Measurable (fun ω : BrownianPath d ↦ f (z + ω (τ ω).toNNReal)) :=
    hf.continuous.measurable.comp (measurable_const.add
      (measurable_brownian_random_evaluation (ENNReal.measurable_toNNReal.comp hτ.measurable')))
  have hiexit : Integrable (fun ω : BrownianPath d ↦ f (z + ω (τ ω).toNNReal)) μ :=
    (integrable_const M).mono' hmexit.aestronglyMeasurable (Eventually.of_forall (fun ω ↦ hM _))
  have hizero : Integrable (fun ω : BrownianPath d ↦ f (z + ω 0)) μ :=
    (integrable_const M).mono' hmzero.aestronglyMeasurable (Eventually.of_forall (fun ω ↦ hM _))
  have hbase : (∫ ω, f (z + ω 0) ∂μ) = f z := by
    have heq : (fun ω : BrownianPath d ↦ f (z + ω 0)) =ᵐ[μ] fun _ ↦ f z :=
      (standardBrownianLaw_eval_zero_ae hμ).mono (fun ω hω ↦ by
        change f (z + ω 0) = f z
        rw [hω, add_zero])
    rw [integral_congr_ae heq]
    simp
  have heq := integral_sub hiexit hizero
  change (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ) =
    (∫ ω, f (z + ω (τ ω).toNNReal) ∂μ) - (∫ ω, f (z + ω 0) ∂μ) at heq
  rw [hdiff, hbase] at heq
  exact sub_eq_zero.mp heq.symm

/-- The same identity stated directly for the actual stopped-curve endpoint law. -/
theorem standardBrownianLaw_integral_stopped_endPoint_harmonic_compactSupport
    {d : ℕ} (hd : 1 ≤ d) {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (hh : IsHarmonicOn f U) (z : Euc d) :
    (∫ x, f x ∂((stoppedBrownianLaw U z μ).map CurveSpace.endPoint)) = f z := by
  rw [stoppedBrownianLaw, Measure.map_map CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hU z)]
  rw [integral_map (CurveSpace.continuous_endPoint.measurable.comp
    (measurable_stoppedBrownianCurve hU z)).aemeasurable hf.continuous.aestronglyMeasurable]
  simpa only [Function.comp_def, stoppedBrownianCurve_endPoint] using
    standardBrownianLaw_integral_exit_harmonic_compactSupport hd hμ hU hUb hf hsupp hh z

end BouRabeeGwynne
