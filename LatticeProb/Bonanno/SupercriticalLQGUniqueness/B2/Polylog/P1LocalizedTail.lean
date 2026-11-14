/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedTail at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedPolar

 
























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 

 
lemma max_log_le_abs {A r : ℝ} (hA : 0 ≤ A) :
    max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 ≤
      (A + 1) * |Real.log r| + 1 := by
  rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one, one_div, Real.log_inv]
  have h1 : A * -Real.log r ≤ A * |Real.log r| :=
    mul_le_mul_of_nonneg_left (neg_le_abs _) hA
  have h2 : Real.log r ≤ |Real.log r| := le_abs_self _
  have h3 : 0 ≤ |Real.log r| := abs_nonneg _
  refine max_le (max_le ?_ ?_) ?_ <;> nlinarith

 
lemma abs_le_logBound {A C r x : ℝ} (hA : 0 ≤ A)
    (hx : |x| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1) :
    |x| ≤ |C| * ((A + 1) * |Real.log r| + 1) := by
  have hm1 : (1 : ℝ) ≤ max (max (A * Real.log (1 / r))
      (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := le_max_right _ _
  calc |x| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hx
    _ ≤ |C| * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_log_le_abs hA) (abs_nonneg C)

 
lemma integral_Ioi_mul_exp_neg_mul_sq (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ r in Ioi a, r * Real.exp (-c * r ^ 2) = Real.exp (-c * a ^ 2) / (2 * c) := by
  have hd : ∀ x ∈ Ici a, HasDerivAt (fun r => -(Real.exp (-c * r ^ 2) / (2 * c)))
      (x * Real.exp (-c * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -c * r ^ 2) (-c * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-c))
    have h2 := (h1.exp.div_const (2 * c)).neg
    have hc0 : c ≠ 0 := hc.ne'
    have e : -(Real.exp (-c * x ^ 2) * (-c * (2 * x)) / (2 * c)) = x * Real.exp (-c * x ^ 2) := by
      field_simp
    rw [e] at h2
    exact h2
  have hint : IntegrableOn (fun x => x * Real.exp (-c * x ^ 2)) (Ioi a) :=
    (integrable_mul_exp_neg_mul_sq hc).integrableOn
  have hlim : Tendsto (fun r : ℝ => -(Real.exp (-c * r ^ 2) / (2 * c))) atTop (𝓝 (-(0 / (2 * c)))) := by
    have h0 : Tendsto (fun r : ℝ => -c * r ^ 2) atTop atBot :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith)
    exact ((Real.tendsto_exp_atBot.comp h0).div_const _).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
  ring

 
lemma mul_exp_half_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    r * Real.exp (-(1 / (2 * ε ^ 2)) * r ^ 2) ≤ ε := by
  set u := r / ε
  have hu : 0 ≤ u := div_nonneg hr hε.le
  have he : -(1 / (2 * ε ^ 2)) * r ^ 2 = -(u ^ 2 / 2) := by
    simp only [u]; field_simp
  rw [he]
  have hk : u ≤ Real.exp (u ^ 2 / 2) := by
    have := Real.add_one_le_exp (u ^ 2 / 2)
    nlinarith [sq_nonneg (u - 1)]
  have hr' : r = ε * u := by simp only [u]; field_simp
  rw [hr', Real.exp_neg]
  calc ε * u * (Real.exp (u ^ 2 / 2))⁻¹ ≤ ε * Real.exp (u ^ 2 / 2) * (Real.exp (u ^ 2 / 2))⁻¹ := by
        gcongr
    _ = ε := by field_simp

 
lemma abs_log_le_of_ge {a r : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hr : a ≤ r) :
    |Real.log r| ≤ Real.log (1 / a) + r := by
  have hr0 : 0 < r := lt_of_lt_of_le ha hr
  have hla : 0 ≤ Real.log (1 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  rcases le_or_gt r 1 with h1 | h1
  · rw [abs_of_nonpos (Real.log_nonpos hr0.le h1), one_div, Real.log_inv]
    linarith [Real.log_le_log ha hr]
  · rw [abs_of_pos (Real.log_pos h1)]
    have := Real.log_le_sub_one_of_pos hr0
    linarith

 
lemma mul_abs_log_le {ρ r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ1 : ρ ≤ 1) :
    r * |Real.log r| ≤ r * Real.log (1 / ρ) + ρ := by
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  rw [abs_of_nonpos (Real.log_nonpos hr.le (hrρ.trans hρ1))]
  have e : -Real.log r = Real.log (1 / ρ) + Real.log (ρ / r) := by
    rw [Real.log_div hρ.ne' hr.ne', one_div, Real.log_inv]; ring
  rw [e, mul_add]
  have : r * Real.log (ρ / r) ≤ ρ := by
    have h := Real.log_le_sub_one_of_pos (div_pos hρ hr)
    have : r * (ρ / r - 1) = ρ - r := by field_simp
    nlinarith
  linarith

 

 
theorem abs_polarInt_tail_le {ε a A C : ℝ} (hε : 0 < ε) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {F w : ℝ → ℝ}
    (hF : ∀ r, 0 < r → |F r| ≤ C * ((A + 1) * |Real.log r| + 1))
    (hw : ∀ r, |w r| ≤ 1) (hw0 : ∀ r, 0 < r → r < a → w r = 0) :
    |2 / ε ^ 2 * ∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤
      C * (((A + 1) * Real.log (1 / a) + 1) * Real.exp (-a ^ 2 / ε ^ 2) + 2 * (A + 1) * ε) := by
  set β := (A + 1) * Real.log (1 / a) + 1
  have hla : 0 ≤ Real.log (1 / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hβ : 0 ≤ β := by positivity
  set c1 : ℝ := 1 / ε ^ 2
  set c2 : ℝ := 1 / (2 * ε ^ 2)
  have hc1 : 0 < c1 := by positivity
  have hc2 : 0 < c2 := by positivity
  set G : ℝ → ℝ := fun r => C * (β * (r * Real.exp (-c1 * r ^ 2)) +
    (A + 1) * ε * (r * Real.exp (-c2 * r ^ 2)))
  have hsplit : ∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) =
      ∫ r in Ici a, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun r hr => lt_of_lt_of_le ha hr) fun r hr => ?_
    rw [hw0 r hr.1 (not_le.1 hr.2), mul_zero, zero_mul]
  have hGi : IntegrableOn G (Ici a) := by
    refine (((integrable_mul_exp_neg_mul_sq hc1).const_mul β).add
      ((integrable_mul_exp_neg_mul_sq hc2).const_mul _)).const_mul C |>.integrableOn
  have hbd : ∀ r ∈ Ici a, ‖r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)‖ ≤ G r := by
    intro r hr
    have hr : a ≤ r := hr
    have hr0 : 0 < r := lt_of_lt_of_le ha hr
    have hlog := abs_log_le_of_ge ha ha1 hr
    have hFr : |F r| ≤ C * (β + (A + 1) * r) := by
      refine (hF r hr0).trans (mul_le_mul_of_nonneg_left ?_ hC)
      simp only [β]; nlinarith
    have he1 : Real.exp (-r ^ 2 / ε ^ 2) = Real.exp (-c1 * r ^ 2) := by
      congr 1; simp only [c1]; ring
    have hq : r * Real.exp (-c1 * r ^ 2) * r ≤ ε * (r * Real.exp (-c2 * r ^ 2)) := by
      have hsplit2 : Real.exp (-c1 * r ^ 2) = Real.exp (-c2 * r ^ 2) * Real.exp (-c2 * r ^ 2) := by
        rw [← Real.exp_add]; congr 1; simp only [c1, c2]; field_simp; ring
      have hk := mul_exp_half_le hε hr0.le
      rw [hsplit2]
      have hpos : 0 ≤ r * Real.exp (-c2 * r ^ 2) := by positivity
      calc r * (Real.exp (-c2 * r ^ 2) * Real.exp (-c2 * r ^ 2)) * r
          = (r * Real.exp (-c2 * r ^ 2)) * (r * Real.exp (-c2 * r ^ 2)) := by ring
        _ ≤ ε * (r * Real.exp (-c2 * r ^ 2)) := mul_le_mul_of_nonneg_right hk hpos
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos (Real.exp_pos _), he1]
    have hE : 0 ≤ r * Real.exp (-c1 * r ^ 2) := by positivity
    calc r * |F r| * |w r| * Real.exp (-c1 * r ^ 2)
        ≤ r * (C * (β + (A + 1) * r)) * 1 * Real.exp (-c1 * r ^ 2) := by
          gcongr
          exact hw r
      _ = C * (β * (r * Real.exp (-c1 * r ^ 2)) + (A + 1) * (r * Real.exp (-c1 * r ^ 2) * r)) := by
          ring
      _ ≤ C * (β * (r * Real.exp (-c1 * r ^ 2)) + (A + 1) * (ε * (r * Real.exp (-c2 * r ^ 2)))) := by
          gcongr
      _ = G r := by simp only [G]; ring
  have hint : |∫ r in Ici a, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤ ∫ r in Ici a, G r := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hGi ((ae_restrict_iff' measurableSet_Ici).2
      (Eventually.of_forall hbd))
  have hGv : ∫ r in Ici a, G r = C * (β * (Real.exp (-c1 * a ^ 2) / (2 * c1)) +
      (A + 1) * ε * (Real.exp (-c2 * a ^ 2) / (2 * c2))) := by
    rw [integral_Ici_eq_integral_Ioi]
    simp only [G]
    rw [integral_const_mul, integral_add ((integrable_mul_exp_neg_mul_sq hc1).integrableOn.const_mul β)
      ((integrable_mul_exp_neg_mul_sq hc2).integrableOn.const_mul _), integral_const_mul,
      integral_const_mul, integral_Ioi_mul_exp_neg_mul_sq a hc1, integral_Ioi_mul_exp_neg_mul_sq a hc2]
  rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε ^ 2)]
  refine (mul_le_mul_of_nonneg_left hint (by positivity)).trans ?_
  rw [hGv]
  have e1 : Real.exp (-c1 * a ^ 2) = Real.exp (-a ^ 2 / ε ^ 2) := by
    congr 1; simp only [c1]; ring
  have he2 : Real.exp (-c2 * a ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ c2 * a ^ 2 := by positivity
    linarith)
  rw [e1]
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have k1 : 2 / ε ^ 2 * (Real.exp (-a ^ 2 / ε ^ 2) / (2 * c1)) = Real.exp (-a ^ 2 / ε ^ 2) := by
    simp only [c1]; field_simp
  have k2 : 2 / ε ^ 2 * (Real.exp (-c2 * a ^ 2) / (2 * c2)) = 2 * Real.exp (-c2 * a ^ 2) := by
    simp only [c2]; field_simp
  calc 2 / ε ^ 2 * (C * (β * (Real.exp (-a ^ 2 / ε ^ 2) / (2 * c1)) +
        (A + 1) * ε * (Real.exp (-c2 * a ^ 2) / (2 * c2))))
      = C * (β * (2 / ε ^ 2 * (Real.exp (-a ^ 2 / ε ^ 2) / (2 * c1))) +
          (A + 1) * ε * (2 / ε ^ 2 * (Real.exp (-c2 * a ^ 2) / (2 * c2)))) := by ring
    _ = C * (β * Real.exp (-a ^ 2 / ε ^ 2) + (A + 1) * ε * (2 * Real.exp (-c2 * a ^ 2))) := by
        rw [k1, k2]
    _ ≤ C * (β * Real.exp (-a ^ 2 / ε ^ 2) + (A + 1) * ε * (2 * 1)) := by gcongr
    _ = _ := by ring

 

 

theorem abs_polarInt_head_le {ε ρ A C : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {F w : ℝ → ℝ}
    (hF : ∀ r, 0 < r → |F r| ≤ C * ((A + 1) * |Real.log r| + 1))
    (hw : ∀ r, |w r| ≤ 1) (hwρ : ∀ r, ρ ≤ r → w r = 0) :
    |2 / ε ^ 2 * ∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤
      2 / ε ^ 2 * (C * ((A + 1) * (ρ ^ 2 / 2 * Real.log (1 / ρ) + ρ ^ 2) + ρ ^ 2 / 2)) := by
  set L := Real.log (1 / ρ)
  have hL : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  set G : ℝ → ℝ := fun r => C * ((A + 1) * (r * L + ρ) + r)
  have hsplit : ∫ r in Ioi 0, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) =
      ∫ r in Ioc 0 ρ, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun r hr => hr.1) fun r hr => ?_
    have : ρ ≤ r := by
      by_contra hc
      exact hr.2 ⟨hr.1, (not_le.1 hc).le⟩
    rw [hwρ r this, mul_zero, zero_mul]
  have hGi : IntegrableOn G (Ioc 0 ρ) :=
    (by fun_prop : Continuous G).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbd : ∀ r ∈ Ioc 0 ρ, ‖r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)‖ ≤ G r := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hml := mul_abs_log_le hr0 hr.2 hρ1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos (Real.exp_pos _)]
    have hE : Real.exp (-r ^ 2 / ε ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by
      have : 0 ≤ r ^ 2 / ε ^ 2 := by positivity
      rw [neg_div]; linarith)
    calc r * |F r| * |w r| * Real.exp (-r ^ 2 / ε ^ 2)
        ≤ r * (C * ((A + 1) * |Real.log r| + 1)) * 1 * 1 := by
          gcongr
          · exact hF r hr0
          · exact hw r
      _ = C * ((A + 1) * (r * |Real.log r|) + r) := by ring
      _ ≤ G r := by simp only [G]; gcongr
  have hint : |∫ r in Ioc 0 ρ, r * F r * w r * Real.exp (-r ^ 2 / ε ^ 2)| ≤ ∫ r in Ioc 0 ρ, G r := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hGi ((ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall hbd))
  have hGv : ∫ r in Ioc 0 ρ, G r = C * ((A + 1) * (ρ ^ 2 / 2 * L + ρ ^ 2) + ρ ^ 2 / 2) := by
    rw [← intervalIntegral.integral_of_le hρ.le]
    simp only [G]
    rw [intervalIntegral.integral_const_mul]
    have e : (fun r : ℝ => (A + 1) * (r * L + ρ) + r) = fun r => ((A + 1) * L + 1) * r + (A + 1) * ρ := by
      funext r; ring
    rw [e, intervalIntegral.integral_add ((by fun_prop : Continuous fun r : ℝ => ((A + 1) * L + 1) * r).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_id,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hsplit, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / ε ^ 2)]
  rw [← hGv]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

 

 

lemma heatKernel_le_of_ge {s a : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (z w : ℂ) (hw : a ≤ ‖z - w‖) :
    heatKernel s z w ≤ 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) z w := by
  unfold heatKernel
  have ht : a ^ 2 ≤ ‖z - w‖ ^ 2 := pow_le_pow_left₀ ha hw 2
  set t := ‖z - w‖ ^ 2
  have e1 : -t / (2 * s) = -t / (2 * (2 * s)) + -t / (4 * s) := by
    field_simp; ring
  have e2 : -t / (4 * s) ≤ -(a ^ 2 / (4 * s)) := by
    rw [neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right ht (by positivity)
  have hpre : (2 * Real.pi * s)⁻¹ = 2 * (2 * Real.pi * (2 * s))⁻¹ := by
    field_simp
  rw [e1, Real.exp_add, hpre]
  have hp : 0 ≤ (2 * Real.pi * (2 * s))⁻¹ := by positivity
  calc 2 * (2 * Real.pi * (2 * s))⁻¹ * (Real.exp (-t / (2 * (2 * s))) * Real.exp (-t / (4 * s)))
      ≤ 2 * (2 * Real.pi * (2 * s))⁻¹ * (Real.exp (-t / (2 * (2 * s))) *
          Real.exp (-(a ^ 2 / (4 * s)))) := by gcongr
    _ = _ := by ring

 

theorem one_sub_plZ_le (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    1 - plZ q ε hε ≤ 2 * Real.exp (-(plRad q ε ^ 2 / (8 * ε ^ 2))) := by
  set s := ε ^ 2 / 2
  have hs : 0 < s := by have := hε.1; positivity
  set a := plRad q ε / 2
  have ha : 0 ≤ a := (div_pos (plRad_pos q hε) two_pos).le
  have hk : a ^ 2 / (4 * s) = plRad q ε ^ 2 / (8 * ε ^ 2) := by
    simp only [a, s]; field_simp; ring
  have hi1 : Integrable (fun w => heatKernel s 0 w) := integrable_heatKernel _ hs 0
  have hi2 : Integrable (fun w => plTest q ε hε 0 w) :=
    (plTest q ε hε 0).continuous.integrable_of_hasCompactSupport (plTest q ε hε 0).hasCompactSupport
  have hi3 : Integrable (fun w => 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) 0 w) :=
    (integrable_heatKernel _ (by positivity) 0).const_mul _
  have e1 : 1 - plZ q ε hε = ∫ w, (heatKernel s 0 w - plTest q ε hε 0 w) := by
    rw [integral_sub hi1 hi2, integral_heatKernel s hs 0, plZ]
  rw [e1, ← hk]
  calc ∫ w, (heatKernel s 0 w - plTest q ε hε 0 w)
      ≤ ∫ w, 2 * Real.exp (-(a ^ 2 / (4 * s))) * heatKernel (2 * s) 0 w := by
        refine integral_mono (hi1.sub hi2) hi3 fun w => ?_
        simp only
        rw [plTest_apply]
        have hp := heatKernel_nonneg s hs.le 0 w
        by_cases hw : ‖w‖ ≤ a
        · rw [plBump_eq_one q ε hε (by rw [zero_sub, norm_neg]; exact hw), one_mul, sub_self]
          have := heatKernel_nonneg (2 * s) (by positivity) 0 w
          positivity
        · push Not at hw
          have hk2 := heatKernel_le_of_ge hs ha 0 w (by rw [zero_sub, norm_neg]; exact hw.le)
          have := plBump_nonneg q ε hε (0 - w)
          nlinarith
    _ = 2 * Real.exp (-(a ^ 2 / (4 * s))) := by
        rw [integral_const_mul, integral_heatKernel _ (by positivity) 0, mul_one]

end SupercriticalLQGUniqueness.B2.Polylog
