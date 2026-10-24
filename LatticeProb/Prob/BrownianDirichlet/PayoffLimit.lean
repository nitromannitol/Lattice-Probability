import LatticeProb.Prob.BrownianDirichlet.Extensions
import LatticeProb.Prob.BrownianDirichlet.JointMeasurability
import LatticeProb.Prob.BrownianPathCoords
import LatticeProb.Prob.BrownianPathHarmonicExit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Discounted payoff limits

The terminal payoff at exit truncated by an integer vanishes by a uniform discount
estimate. Dominated convergence gives the running payoff limit in strict survival
form. Both arguments include paths whose exit time is infinite.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LatticeProb

variable {d : ℕ} {B : Set (Euc d)} {σ μd : ℝ} {x : Euc d}

/-- At a finite scaled exit, a zero-start path hits the frontier. -/
theorem scaledExit_mem_frontier (hB : IsOpen B) (hx : x ∈ B)
    {ω : BrownianPath d} (hω : ω 0 = 0) (hfin : scaledExit B σ x ω ≠ ∞) :
    x + σ • ω (scaledExit B σ x ω).toNNReal ∈ frontier B := by
  apply continuousExitTime_mem_frontier hB (ω := scalePath σ ω) _ hfin
  simpa only [scalePath_apply, hω, smul_zero, add_zero] using hx

/-- A zero-start path stopped at truncated exit remains in the closed domain. -/
theorem truncated_scaledExit_mem_closure (hB : IsOpen B) (hx : x ∈ B)
    (n : ℕ) {ω : BrownianPath d} (hω : ω 0 = 0) :
    x + σ • ω (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal ∈ closure B := by
  by_cases ht : scaledExit B σ x ω ≤ (n : ℝ≥0∞)
  · rw [min_eq_left ht]
    exact frontier_subset_closure (scaledExit_mem_frontier hB hx hω
      (ne_top_of_le_ne_top (by simp) ht))
  · have ht' := lt_of_not_ge ht
    rw [min_eq_right ht'.le, ENNReal.toNNReal_natCast]
    exact subset_closure (mem_of_lt_scaledExit ht')

/-- The truncated terminal payoff has a uniform exponentially decaying bound. -/
theorem norm_terminal_payoff_le {v : Euc d → ℝ} {K : ℝ}
    (hB : IsOpen B) (hx : x ∈ B) (hK : 0 ≤ K)
    (hv : ∀ y ∈ closure B, |v y| ≤ K)
    (hzero : ∀ y ∈ frontier B, v y = 0)
    (n : ℕ) {ω : BrownianPath d} (hω : ω 0 = 0) :
    ‖Real.exp (-μd * ((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ)) *
      v (x + σ • ω (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal)‖ ≤
      K * Real.exp (-μd * n) := by
  by_cases ht : scaledExit B σ x ω ≤ (n : ℝ≥0∞)
  · rw [min_eq_left ht, hzero _ (scaledExit_mem_frontier hB hx hω
      (ne_top_of_le_ne_top (by simp) ht)), mul_zero, norm_zero]
    exact mul_nonneg hK (Real.exp_pos _).le
  · have ht' : (n : ℝ≥0∞) < scaledExit B σ x ω := lt_of_not_ge ht
    rw [min_eq_right ht'.le]
    simp only [ENNReal.toNNReal_natCast, NNReal.coe_natCast, norm_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left
      (hv _ (subset_closure (mem_of_lt_scaledExit ht'))) (Real.exp_pos _).le).trans_eq
      (mul_comm _ _)

/-- The terminal payoff is integrable using the continuous zero extension. -/
theorem integrable_terminal_payoff {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (hB : IsOpen B) (hbounded : Bornology.IsBounded B)
    (hx : x ∈ B) {v : Euc d → ℝ} (hv : ContinuousOn v (closure B))
    (hzero : ∀ y ∈ frontier B, v y = 0) (n : ℕ) :
    Integrable (fun ω ↦
      Real.exp (-μd * ((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ)) *
        v (x + σ • ω (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal)) μ := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  let S : BrownianPath d → ℝ≥0 := fun ω ↦
    (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal
  have hS : Measurable S := ((measurable_scaledExit hB σ x).min measurable_const).ennreal_toNNReal
  have hX : Measurable (fun ω : BrownianPath d ↦ x + σ • ω (S ω)) :=
    measurable_const.add ((measurable_brownian_random_evaluation hS).const_smul σ)
  have he : Measurable (fun ω ↦ Real.exp (-μd * (S ω : ℝ))) :=
    (measurable_const.mul hS.coe_nnreal_real).exp
  have hm := he.mul ((continuous_closure_indicator_of_zero_frontier hv hzero).measurable.comp hX)
  have hae : AEStronglyMeasurable (fun ω ↦ Real.exp (-μd * (S ω : ℝ)) *
      v (x + σ • ω (S ω))) μ := by
    apply hm.aestronglyMeasurable.congr
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
    change Real.exp (-μd * (S ω : ℝ)) * (closure B).indicator v
      (x + σ • ω (S ω)) = Real.exp (-μd * (S ω : ℝ)) * v (x + σ • ω (S ω))
    rw [indicator_of_mem (truncated_scaledExit_mem_closure hB hx n hω (σ := σ))]
  obtain ⟨K, hK⟩ := isBounded_image_closure hbounded hv
  have hKpos := (abs_nonneg (v x)).trans (hK x (subset_closure hx))
  exact (integrable_const (K * Real.exp (-μd * n))).mono' hae
    ((standardBrownianLaw_eval_zero_ae hμ).mono fun ω hω ↦
      norm_terminal_payoff_le hB hx hKpos hK hzero n hω)

/-- Positive discount removes the terminal term, without a finite-exit assumption. -/
theorem tendsto_terminal_payoff {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (hB : IsOpen B) (hbounded : Bornology.IsBounded B)
    (hx : x ∈ B) (hμd : 0 < μd) {v : Euc d → ℝ}
    (hv : ContinuousOn v (closure B)) (hzero : ∀ y ∈ frontier B, v y = 0) :
    Tendsto (fun n : ℕ ↦ ∫ ω,
      Real.exp (-μd * ((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ)) *
        v (x + σ • ω (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal) ∂μ)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨K, hK⟩ := isBounded_image_closure hbounded hv
  have hKpos : 0 ≤ K := (abs_nonneg (v x)).trans (hK x (subset_closure hx))
  have hbound (n : ℕ) := norm_integral_le_of_norm_le_const
    ((standardBrownianLaw_eval_zero_ae hμ).mono fun ω hω ↦
      norm_terminal_payoff_le hB hx hKpos hK hzero n hω (μd := μd) (σ := σ))
  simp only [probReal_univ, mul_one] at hbound
  apply squeeze_zero_norm hbound
  have htime : Tendsto (fun n : ℕ ↦ μd * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hμd
  simpa only [Function.comp_def, neg_mul, mul_zero] using
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp htime).const_mul K

/-- A truncated time integral equals its strict survival form; endpoints have zero measure. -/
theorem running_payoff_eq_killed_cutoff (g : Euc d → ℝ) (n : ℕ)
    (ω : BrownianPath d) :
    (∫ t in (0 : ℝ)..((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ),
      Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) =
    ∫ t in Ioi (0 : ℝ), if t < (n : ℝ) ∧ ENNReal.ofReal t < scaledExit B σ x ω
      then Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0 := by
  let S := (min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal
  have hfin : min (scaledExit B σ x ω) (n : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hcut (t : ℝ) (ht : 0 < t) :
      t < (S : ℝ) ↔ t < (n : ℝ) ∧ ENNReal.ofReal t < scaledExit B σ x ω := by
    rw [← ENNReal.ofReal_lt_coe_iff ht.le, ENNReal.coe_toNNReal hfin, lt_min_iff]
    rw [← ENNReal.coe_natCast, ENNReal.ofReal_lt_coe_iff ht.le]
    exact and_comm
  rw [intervalIntegral.integral_of_le (by exact S.coe_nonneg),
    integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ t in Ioi (0 : ℝ), (Iio (S : ℝ)).indicator
        (fun t ↦ Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) t := by
      rw [setIntegral_indicator measurableSet_Iio]
      rfl
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [indicator, mem_Iio, hcut t ht]

/-- Discounted survival evaluation is measurable even for data specified only on the closure. -/
theorem measurable_discounted_killed_integrand (hB : IsOpen B)
    {g : Euc d → ℝ} (hg : ContinuousOn g (closure B)) :
    Measurable (fun p : ℝ × BrownianPath d ↦
      if ENNReal.ofReal p.1 < scaledExit B σ x p.2 then
        Real.exp (-μd * p.1) * g (x + σ • p.2 p.1.toNNReal) else 0) := by
  have hk := (measurable_killed_integrand hB σ
    (measurable_indicator_of_continuousOn hB hg)).comp
      (measurable_fst.real_toNNReal.prodMk ((measurable_const (a := x)).prodMk measurable_snd))
  have he : Measurable (fun p : ℝ × BrownianPath d ↦ Real.exp (-μd * p.1)) :=
    (measurable_const.mul measurable_fst).exp
  convert he.mul hk using 1
  funext p
  change (if (p.1.toNNReal : ℝ≥0∞) < scaledExit B σ x p.2 then
    Real.exp (-μd * p.1) * g (x + σ • p.2 p.1.toNNReal) else 0) =
    Real.exp (-μd * p.1) *
      (if (p.1.toNNReal : ℝ≥0∞) < scaledExit B σ x p.2 then
        B.indicator g (x + σ • p.2 p.1.toNNReal) else 0)
  rw [mul_ite, mul_zero]
  split_ifs with ht
  · rw [indicator_of_mem (mem_of_lt_scaledExit ht)]
  · rfl

/-- The discounted killed time integrand is integrable for each continuous path. -/
theorem integrable_discounted_killed_integrand (hB : IsOpen B)
    (hμd : 0 < μd) {g : Euc d → ℝ} (hg : ContinuousOn g (closure B))
    {M : ℝ} (hM : ∀ y ∈ closure B, |g y| ≤ M) (hMpos : 0 ≤ M)
    (ω : BrownianPath d) :
    IntegrableOn (fun t : ℝ ↦ if ENNReal.ofReal t < scaledExit B σ x ω then
      Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0) (Ioi 0) := by
  have hm := (measurable_discounted_killed_integrand hB hg (σ := σ) (x := x)
    (μd := μd)).comp (measurable_id.prodMk (measurable_const (a := ω)))
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hμd) 0).const_mul M).mono'
    hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  change ‖(if ENNReal.ofReal t < scaledExit B σ x ω then
    Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0)‖ ≤
      M * Real.exp (-μd * t)
  split_ifs with ht
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (hM _ (subset_closure (mem_of_lt_scaledExit ht))) (Real.exp_pos _).le).trans_eq
      (mul_comm _ _)
  · simpa only [norm_zero] using mul_nonneg hMpos (Real.exp_pos (-μd * t)).le

/-- The full pathwise running payoff has the discount bound `M / μd`. -/
theorem norm_running_payoff_le (hμd : 0 < μd) {g : Euc d → ℝ} {M : ℝ}
    (hM : ∀ y ∈ closure B, |g y| ≤ M) (hMpos : 0 ≤ M)
    (ω : BrownianPath d) :
    ‖∫ t in Ioi (0 : ℝ), if ENNReal.ofReal t < scaledExit B σ x ω then
      Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0‖ ≤ M / μd := by
  have hb := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hμd) 0).const_mul M
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), M * Real.exp (-μd * t) := by
      apply norm_integral_le_of_norm_le hb
      apply ae_of_all
      intro t
      split_ifs with ht
      · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left
          (hM _ (subset_closure (mem_of_lt_scaledExit ht))) (Real.exp_pos _).le).trans_eq
          (mul_comm _ _)
      · simpa only [norm_zero] using mul_nonneg hMpos (Real.exp_pos (-μd * t)).le
    _ = M / μd := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hμd)]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

/-- The full running payoff is integrable under the Brownian probability law. -/
theorem integrable_running_payoff {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (hB : IsOpen B) (hbounded : Bornology.IsBounded B)
    (hμd : 0 < μd) {g : Euc d → ℝ} (hg : ContinuousOn g (closure B)) :
    Integrable (fun ω ↦ ∫ t in Ioi (0 : ℝ),
      if ENNReal.ofReal t < scaledExit B σ x ω then
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M, hM⟩ := isBounded_image_closure hbounded hg
  have hbound : ∀ y ∈ closure B, |g y| ≤ max M 0 :=
    fun y hy ↦ (hM y hy).trans (le_max_left M 0)
  have hm := (measurable_discounted_killed_integrand hB hg (σ := σ) (x := x)
    (μd := μd)).stronglyMeasurable
  exact (integrable_const (max M 0 / μd)).mono'
    hm.integral_prod_left.aestronglyMeasurable
    (ae_of_all _ (fun ω ↦ norm_running_payoff_le hμd hbound (le_max_right M 0) ω))

/-- The running payoff converges to the discounted integral strictly before exit. -/
theorem tendsto_running_payoff {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) (hB : IsOpen B) (hbounded : Bornology.IsBounded B)
    (hμd : 0 < μd) {g : Euc d → ℝ} (hg : ContinuousOn g (closure B)) :
    Tendsto (fun n : ℕ ↦ ∫ ω,
      (∫ t in (0 : ℝ)..((min (scaledExit B σ x ω) (n : ℝ≥0∞)).toNNReal : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ t in Ioi (0 : ℝ),
        if ENNReal.ofReal t < scaledExit B σ x ω then
          Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) else 0) ∂μ)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  obtain ⟨M, hM⟩ := isBounded_image_closure hbounded hg
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  let F : ℝ × BrownianPath d → ℝ := fun p ↦
    if ENNReal.ofReal p.1 < scaledExit B σ x p.2 then
      Real.exp (-μd * p.1) * g (x + σ • p.2 p.1.toNNReal) else 0
  have hF : Measurable F := measurable_discounted_killed_integrand hB hg
  let H : ℕ → ℝ × BrownianPath d → ℝ := fun n p ↦ if p.1 < n then F p else 0
  have hH (n : ℕ) : Measurable (H n) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_const) hF measurable_const
  have hb : IntegrableOn (fun t : ℝ ↦ K * Real.exp (-μd * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hμd) 0).const_mul K
  have hbound (t : ℝ) (ω : BrownianPath d) : ‖F (t, ω)‖ ≤ K * Real.exp (-μd * t) := by
    dsimp only [F]
    split_ifs with ht
    · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      have hm := (hM _ (subset_closure (mem_of_lt_scaledExit ht))).trans (le_max_left M 0)
      exact (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le).trans_eq (mul_comm _ _)
    · exact (norm_zero : ‖(0 : ℝ)‖ = 0).le.trans
        (mul_nonneg hK (Real.exp_pos _).le)
  have hboundH (n : ℕ) (t : ℝ) (ω : BrownianPath d) :
      ‖H n (t, ω)‖ ≤ K * Real.exp (-μd * t) := by
    dsimp only [H]
    split_ifs
    · exact hbound t ω
    · simpa only [norm_zero] using mul_nonneg hK (Real.exp_pos (-μd * t)).le
  have hpath (ω : BrownianPath d) :
      Tendsto (fun n ↦ ∫ t in Ioi (0 : ℝ), H n (t, ω)) atTop
        (𝓝 (∫ t in Ioi (0 : ℝ), F (t, ω))) := by
    apply tendsto_integral_of_dominated_convergence (fun t ↦ K * Real.exp (-μd * t))
    · intro n
      exact ((hH n).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact hb
    · intro n
      exact ae_of_all _ (fun t ↦ hboundH n t ω)
    · apply ae_of_all
      intro t
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop t)] with n hn
      exact (if_pos hn).symm
  have hout : Tendsto (fun n ↦ ∫ ω, (∫ t in Ioi (0 : ℝ), H n (t, ω)) ∂μ) atTop
      (𝓝 (∫ ω, (∫ t in Ioi (0 : ℝ), F (t, ω)) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ ↦ ∫ t in Ioi (0 : ℝ), K * Real.exp (-μd * t))
    · intro n
      exact (hH n).stronglyMeasurable.integral_prod_left.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun ω ↦ norm_integral_le_of_norm_le hb
        (ae_of_all _ (fun t ↦ hboundH n t ω)))
    · exact ae_of_all _ hpath
  convert hout using 1
  funext n
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  dsimp only
  rw [running_payoff_eq_killed_cutoff]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only [H, F]
  exact ite_and _ _ _ _

end LatticeProb
