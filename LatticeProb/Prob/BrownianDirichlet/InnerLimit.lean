import LatticeProb.Prob.BrownianDirichlet.LocalizedStopping
import LatticeProb.Prob.BrownianDirichlet.Exhaustion
import LatticeProb.Prob.BrownianDirichlet.Extensions
import Mathlib.Topology.TietzeExtension

/-!
# Discounted stopping on the outer ball

Exhaustion by concentric inner balls transfers the localized stopped identity to
an outer ball at a fixed finite time horizon. Continuity on the closed ball
supplies convergence and uniform bounds for dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

/-- At or before finite exit, a zero-start continuous path lies in the closed domain. -/
lemma mem_closure_of_le_scaledExit {d : ℕ} {B : Set (Euc d)} (hB : IsOpen B)
    {σ : ℝ} {x : Euc d} (hx : x ∈ B) {ω : BrownianPath d} (hω : ω 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ scaledExit B σ x ω) :
    x + σ • ω t ∈ closure B := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact subset_closure (mem_of_lt_scaledExit hlt)
  · have hfin : scaledExit B σ x ω ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have ht' : t = (scaledExit B σ x ω).toNNReal := by
      rw [← heq, ENNReal.toNNReal_coe]
    rw [ht']
    apply frontier_subset_closure
    apply continuousExitTime_mem_frontier hB _ hfin
    simpa only [scalePath_apply, hω, smul_zero, add_zero] using hx

/-- Continuous data on a closed set admit an ambient continuous extension. -/
lemma exists_continuous_extension_closed {d : ℕ} {B : Set (Euc d)}
    {f : Euc d → ℝ} (hf : ContinuousOn f (closure B)) :
    ∃ F : C(Euc d, ℝ), EqOn F f (closure B) := by
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq isClosed_closure
    (⟨fun y : closure B ↦ f y, hf.restrict⟩ : C(closure B, ℝ))
  refine ⟨F, fun y hy ↦ ?_⟩
  exact congrArg (fun q : C(closure B, ℝ) ↦ q ⟨y, hy⟩) hF

/-- Continuous ambient data give a measurable discounted payoff at measurable times. -/
lemma measurable_continuous_stopped_payoff {d : ℕ} (f g : C(Euc d, ℝ))
    (σ μd : ℝ) (x : Euc d) {S : BrownianPath d → ℝ≥0} (hS : Measurable S) :
    Measurable (fun ω ↦ Real.exp (-μd * (S ω : ℝ)) * f (x + σ • ω (S ω)) +
      ∫ t in (0 : ℝ)..(S ω : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) := by
  have hi : StronglyMeasurable (fun p : BrownianPath d × ℝ ↦
      {q : BrownianPath d × ℝ | 0 < q.2 ∧ q.2 ≤ (S q.1 : ℝ)}.indicator
        (fun q ↦ Real.exp (-μd * q.2) * g (x + σ • q.1 q.2.toNNReal)) p) := by
    apply StronglyMeasurable.indicator
    · exact (by fun_prop : Continuous (fun q : BrownianPath d × ℝ ↦
        Real.exp (-μd * q.2) * g (x + σ • q.1 q.2.toNNReal))).stronglyMeasurable
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (NNReal.continuous_coe.measurable.comp
          (hS.comp measurable_fst)))
  have heq (ω : BrownianPath d) :
      (∫ t, {q : BrownianPath d × ℝ | 0 < q.2 ∧ q.2 ≤ (S q.1 : ℝ)}.indicator
        (fun q ↦ Real.exp (-μd * q.2) * g (x + σ • q.1 q.2.toNNReal)) (ω, t)) =
      ∫ t in (0 : ℝ)..(S ω : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) := by
    rw [intervalIntegral.integral_of_le (S ω).coe_nonneg]
    change (∫ t, (Ioc 0 (S ω : ℝ)).indicator
      (fun t ↦ Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) t) = _
    exact integral_indicator measurableSet_Ioc
  have hm := (hi.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  simp_rw [heq] at hm
  exact ((Real.measurable_exp.comp
    (measurable_const.mul (NNReal.continuous_coe.measurable.comp hS))).mul
      (f.continuous.measurable.comp
        (measurable_const.add ((measurable_brownian_random_evaluation hS).const_smul σ)))).add hm

/-- Continuous ambient data give a continuous payoff along each fixed path. -/
lemma continuous_stopped_payoff_time {d : ℕ} (f g : C(Euc d, ℝ))
    (σ μd : ℝ) (x : Euc d) (ω : BrownianPath d) :
    Continuous (fun s : ℝ≥0 ↦ Real.exp (-μd * (s : ℝ)) * f (x + σ • ω s) +
      ∫ t in (0 : ℝ)..(s : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) := by
  have hi : Continuous (fun t : ℝ ↦
      Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) := by fun_prop
  exact (by fun_prop : Continuous (fun s : ℝ≥0 ↦
    Real.exp (-μd * (s : ℝ)) * f (x + σ • ω s))).add
      ((intervalIntegral.continuous_primitive (fun a b ↦ hi.intervalIntegrable a b) 0).comp
        NNReal.continuous_coe)

/-- A classical solution satisfies discounted stopping on the ball at a finite horizon. -/
theorem stopped_identity_ball {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {c : Euc d} {R a₀ μd : ℝ}
    (hR : 0 < R) (ha : 0 < a₀) (hμd : 0 < μd) {v g : Euc d → ℝ}
    (hv : ContDiffOn ℝ 2 v (Metric.ball c R))
    (hpde : ∀ y ∈ Metric.ball c R,
      μd * v y - a₀ * Laplacian.laplacian v y = g y)
    (hvc : ContinuousOn v (closure (Metric.ball c R)))
    (hgc : ContinuousOn g (closure (Metric.ball c R)))
    {x : Euc d} (hx : x ∈ Metric.ball c R) (N : ℝ≥0) :
    let σ := Real.sqrt (2 * a₀)
    let S := fun ω ↦ (min (scaledExit (Metric.ball c R) σ x ω)
      (N : ℝ≥0∞)).toNNReal
    v x = ∫ ω, Real.exp (-μd * (S ω : ℝ)) * v (x + σ • ω (S ω)) +
      (∫ t in (0 : ℝ)..(S ω : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) ∂μ := by
  intro σ S
  letI : IsProbabilityMeasure μ := hμ.1
  let B := Metric.ball c R
  let T := fun (A : Set (Euc d)) (ω : BrownianPath d) ↦
    (min (scaledExit A σ x ω) (N : ℝ≥0∞)).toNNReal
  have hcoe (A : Set (Euc d)) (ω) :
      (T A ω : ℝ≥0∞) = min (scaledExit A σ x ω) (N : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  have hN (A : Set (Euc d)) (ω) : T A ω ≤ N := by
    rw [← ENNReal.coe_le_coe, hcoe]
    exact min_le_right _ _
  have hmeas (A : Set (Euc d)) (hA : IsOpen A) : Measurable (T A) :=
    ENNReal.measurable_toNNReal.comp
      ((measurable_scaledExit hA σ x).min measurable_const)
  obtain ⟨f, hf⟩ := exists_continuous_extension_closed hvc
  obtain ⟨q, hq⟩ := exists_continuous_extension_closed hgc
  let F := fun (ω : BrownianPath d) (s : ℝ≥0) ↦
    Real.exp (-μd * (s : ℝ)) * f (x + σ • ω s) +
      ∫ t in (0 : ℝ)..(s : ℝ),
        Real.exp (-μd * t) * q (x + σ • ω t.toNNReal)
  have hpos (ω : BrownianPath d) (hω : ω 0 = 0) {s : ℝ≥0}
      (hs : (s : ℝ≥0∞) ≤ scaledExit B σ x ω) :
      x + σ • ω s ∈ closure B :=
    mem_closure_of_le_scaledExit Metric.isOpen_ball hx hω hs
  have heq (ω : BrownianPath d) (hω : ω 0 = 0) {s : ℝ≥0}
      (hs : (s : ℝ≥0∞) ≤ scaledExit B σ x ω) :
      F ω s = Real.exp (-μd * (s : ℝ)) * v (x + σ • ω s) +
        ∫ t in (0 : ℝ)..(s : ℝ),
          Real.exp (-μd * t) * g (x + σ • ω t.toNNReal) := by
    dsimp [F]
    rw [hf (hpos ω hω hs)]
    congr 1
    apply intervalIntegral.integral_congr_Ioo_of_le s.coe_nonneg
    intro t ht
    dsimp only
    rw [hq (hpos ω hω ((ENNReal.coe_le_coe.mpr
      ((Real.toNNReal_le_iff_le_coe).2 ht.2.le)).trans hs))]
  have hTB (ω) : (T B ω : ℝ≥0∞) ≤ scaledExit B σ x ω := by
    rw [hcoe]
    exact min_le_left _ _
  have hTk (k : ℕ) (ω) :
      (T (Metric.ball c (innerRadius R k)) ω : ℝ≥0∞) ≤ scaledExit B σ x ω := by
    rw [hcoe]
    exact (min_le_left _ _).trans (scaledExit_innerBall_le hR k)
  obtain ⟨K, hK⟩ := isBounded_image_closure Metric.isBounded_ball hvc
  obtain ⟨M, hM⟩ := isBounded_image_closure Metric.isBounded_ball hgc
  have hM0 : 0 ≤ M := (abs_nonneg (g x)).trans (hM x (subset_closure hx))
  have he (t : ℝ) (ht : 0 ≤ t) : |Real.exp (-μd * t)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμd.le) ht
  have hbound (ω : BrownianPath d) (hω : ω 0 = 0) {s : ℝ≥0}
      (hs : (s : ℝ≥0∞) ≤ scaledExit B σ x ω) (hsN : s ≤ N) :
      ‖F ω s‖ ≤ K + M * (N : ℝ) := by
    have hterminal : |Real.exp (-μd * (s : ℝ)) * f (x + σ • ω s)| ≤ K := by
      rw [abs_mul, hf (hpos ω hω hs)]
      exact (mul_le_mul_of_nonneg_right (he s s.coe_nonneg) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hK _ (hpos ω hω hs))
    have hrunning : ‖∫ t in (0 : ℝ)..(s : ℝ),
        Real.exp (-μd * t) * q (x + σ • ω t.toNNReal)‖ ≤ M * (s : ℝ) := by
      simpa only [sub_zero, abs_of_nonneg s.coe_nonneg] using
        (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (s : ℝ))
          (C := M) (f := fun t ↦ Real.exp (-μd * t) *
            q (x + σ • ω t.toNNReal)) (fun t ht ↦ by
            rw [uIoc_of_le s.coe_nonneg] at ht
            have htpos := hpos ω hω ((ENNReal.coe_le_coe.mpr
              ((Real.toNNReal_le_iff_le_coe).2 ht.2)).trans hs)
            rw [Real.norm_eq_abs, abs_mul, hq htpos]
            exact (mul_le_mul_of_nonneg_right (he t ht.1.le) (abs_nonneg _)).trans
              (by simpa only [one_mul] using hM _ htpos)))
    exact (norm_add_le _ _).trans (add_le_add hterminal
      (hrunning.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsN) hM0)))
  have hbnd (k : ℕ) : ∀ᵐ ω ∂μ,
      ‖F ω (T (Metric.ball c (innerRadius R k)) ω)‖ ≤ K + M * (N : ℝ) := by
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
    exact hbound ω hω (hTk k ω) (hN _ ω)
  have hconv : ∀ᵐ ω ∂μ, Tendsto
      (fun k ↦ F ω (T (Metric.ball c (innerRadius R k)) ω)) atTop
        (𝓝 (F ω (T B ω))) := by
    filter_upwards [] with ω
    exact (continuous_stopped_payoff_time f q σ μd x ω).continuousAt.tendsto.comp
      (tendsto_toNNReal_min_scaledExit_innerBall hR N)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ) (fun _ : BrownianPath d ↦ K + M * (N : ℝ))
    (F := fun k ω ↦ F ω (T (Metric.ball c (innerRadius R k)) ω))
    (f := fun ω ↦ F ω (T B ω))
    (fun k ↦ (measurable_continuous_stopped_payoff f q σ μd x
      (hmeas _ Metric.isOpen_ball)).aestronglyMeasurable)
    (integrable_const _) hbnd hconv
  have hevent : ∀ᶠ k in atTop,
      (∫ ω, F ω (T (Metric.ball c (innerRadius R k)) ω) ∂μ) = v x := by
    have hxin : ∀ᶠ k in atTop, x ∈ Metric.ball c (innerRadius R k) :=
      (tendsto_innerRadius R).eventually (lt_mem_nhds hx)
    filter_upwards [hxin] with k hk
    have hi := localized_stopped_identity hμ hR ha hμd hv hpde k hk N
    apply Eq.trans _ hi.symm
    apply integral_congr_ae
    filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
    exact heq ω hω (hTk k ω)
  have hvalue : (∫ ω, F ω (T B ω) ∂μ) = v x :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hevent.mono fun _ hk ↦ hk.symm))
  refine hvalue.symm.trans (integral_congr_ae ?_)
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
  exact heq ω hω (hTB ω)

/-- An actual Brownian law realizes the nonzero constant-solution identity at unit cutoff. -/
theorem exists_brownian_constant_stopped_identity_ball :
    ∃ μ : Measure (BrownianPath 1), IsStandardBrownianLaw μ ∧
      let S := fun ω ↦ (min (scaledExit (Metric.ball (0 : Euc 1) 1)
        (Real.sqrt 2) 0 ω) (1 : ℝ≥0∞)).toNNReal
      (∫ ω, Real.exp (-(S ω : ℝ)) +
        (∫ t in (0 : ℝ)..(S ω : ℝ), Real.exp (-t)) ∂μ) = 1 := by
  obtain ⟨μ, hμ⟩ := BrownianPathCoordsExample.exists_isStandardBrownianLaw_one
  refine ⟨μ, hμ, ?_⟩
  have h := stopped_identity_ball hμ (c := (0 : Euc 1))
    (R := 1) (a₀ := 1) (μd := 1) zero_lt_one zero_lt_one zero_lt_one
    (v := fun _ ↦ 1) (g := fun _ ↦ 1) contDiff_const.contDiffOn
    (fun y _ ↦ by
      simp only [InnerProductSpace.laplacian_const, Pi.zero_apply, mul_one, mul_zero, sub_zero])
    continuousOn_const continuousOn_const (x := 0) (by simp) (1 : ℝ≥0)
  simpa only [mul_one, one_mul, neg_one_mul, ENNReal.coe_one] using h.symm

end LatticeProb
