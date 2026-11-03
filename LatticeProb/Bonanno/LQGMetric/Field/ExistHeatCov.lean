/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.ExistHeatCov at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyVar
import LatticeProb.Bonanno.LQGDimension.LFPP.HeatKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Prod

/-!
# Heat-kernel representation of the log-covariance (task P2-EXIST)

`logCov_eq_integral_heat`: for bounded, compactly supported, measurable `φ, ψ` with `∫ ψ = 0`,
`logCov φ ψ = ∫_0^∞ π ∫∫ φ(u) ψ(v) p_t(u, v) du dv dt`, `p_t(u,v) = (2πt)⁻¹ e^{−|u−v|²/(2t)}`.

This is the covariance identity behind the white-noise construction of the whole-plane GFF,
`h = √π ∫∫ p_{t/2}(·, y) W(dy, dt)` (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021,
`tightness.tex` l. 143–145 and (2.2); Berestycki–Powell, arXiv:2404.16642, ch. 1): since
`p_{t/2} * p_{t/2} = p_t`, the white-noise covariance of the pairings is
`π ∫_0^∞ ∫∫ φ ψ p_t dt`, and `π ∫_0^∞ p_t(u,v) dt = −log|u − v| + const` (Frullani).

Proof: the Frullani identity is reused from LQGDimension
(`LQGDimension.HeatKernel.heatRep_of_integrable_log`, LD/LFPP/HeatKernel.lean), applied to the
finite measures `(φ ⊗ ψ)^± du dv` (equal masses, since `∫ ψ = 0`), followed by the substitution
`t = 2τ²`. Local integrability of `log|·|` is reused from `HeatMollifyVar` (QZ
`K3.locallyIntegrable_log_norm`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace LQGMetric
namespace GFFExist

/-- `‖p.1 − p.2‖` on `ℂ × ℂ` -/
abbrev dist2 (p : ℂ × ℂ) : ℝ := ‖p.1 - p.2‖

lemma ae_dist2_pos : ∀ᵐ p : ℂ × ℂ ∂volume, 0 < dist2 p := by
  have hs : MeasurableSet {p : ℂ × ℂ | 0 < dist2 p} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [show (volume : Measure (ℂ × ℂ)) = volume.prod volume from rfl]
  refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 (Eventually.of_forall fun u => ?_)
  have h0 : volume ({u} : Set ℂ) = 0 := measure_singleton u
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) h0
  simp only [mem_setOf_eq, dist2, norm_pos_iff, sub_ne_zero, not_not] at hv
  simp [hv]

/-- **Signed Frullani identity.** For integrable `f` on `ℂ × ℂ` with `∫ f = 0` and
`f · log‖p.1 − p.2‖` integrable:
`∫_0^∞ (∫ f e^{−D²/(4τ²)})/τ dτ = −∫ f log D`. -/
theorem heatRep_signed {f : ℂ × ℂ → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    (hf0 : ∫ p, f p = 0) (hlog : Integrable (fun p => f p * Real.log (dist2 p))) :
    ∫ τ in Ioi 0, (∫ p, f p * Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2))) / τ =
      -∫ p, f p * Real.log (dist2 p) := by
  set fp : ℂ × ℂ → ℝ≥0 := fun p => (f p).toNNReal with hfp
  set fn : ℂ × ℂ → ℝ≥0 := fun p => (-f p).toNNReal with hfn
  have hfpm : Measurable fp := hfm.real_toNNReal
  have hfnm : Measurable fn := hfm.neg.real_toNNReal
  set μp : Measure (ℂ × ℂ) := volume.withDensity fun p => (fp p : ℝ≥0∞) with hμp
  set μn : Measure (ℂ × ℂ) := volume.withDensity fun p => (fn p : ℝ≥0∞) with hμn
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hfi.2
  have : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  have hDm : Measurable dist2 := by unfold dist2; fun_prop
  have hpos_p : ∀ᵐ p ∂μp, 0 < dist2 p := withDensity_absolutelyContinuous _ _ ae_dist2_pos
  have hpos_n : ∀ᵐ p ∂μn, 0 < dist2 p := withDensity_absolutelyContinuous _ _ ae_dist2_pos
  -- integrals against `μp`, `μn`
  have hcoe_p : ∀ p, ((fp p : ℝ≥0) : ℝ) = max (f p) 0 := fun p => Real.coe_toNNReal' _
  have hcoe_n : ∀ p, ((fn p : ℝ≥0) : ℝ) = max (-f p) 0 := fun p => Real.coe_toNNReal' _
  have hint_p : ∀ g : ℂ × ℂ → ℝ, ∫ p, g p ∂μp = ∫ p, max (f p) 0 * g p := by
    intro g
    rw [hμp, integral_withDensity_eq_integral_smul hfpm]
    simp only [NNReal.smul_def, smul_eq_mul, hcoe_p]
  have hint_n : ∀ g : ℂ × ℂ → ℝ, ∫ p, g p ∂μn = ∫ p, max (-f p) 0 * g p := by
    intro g
    rw [hμn, integral_withDensity_eq_integral_smul hfnm]
    simp only [NNReal.smul_def, smul_eq_mul, hcoe_n]
  have hmax : ∀ p, max (f p) 0 - max (-f p) 0 = f p := fun p => by
    rcases le_total 0 (f p) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hbd_p : ∀ p, |max (f p) 0| ≤ |f p| := fun p => by
    rcases le_total 0 (f p) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h]; simp
  have hbd_n : ∀ p, |max (-f p) 0| ≤ |f p| := fun p => by
    rcases le_total 0 (f p) with h | h
    · rw [max_eq_right (by linarith)]; simp
    · rw [max_eq_left (by linarith), abs_neg]
  have hip : Integrable (fun p => max (f p) 0) :=
    hfi.mono (hfm.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hbd_p p)
  have hin : Integrable (fun p => max (-f p) 0) :=
    hfi.mono (hfm.neg.max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hbd_n p)
  -- `log D` is integrable against `μp`, `μn`
  have hlog_p : Integrable (fun p => Real.log (dist2 p)) μp := by
    rw [hμp, integrable_withDensity_iff_integrable_smul hfpm]
    refine hlog.mono (by
      simp only [NNReal.smul_def, smul_eq_mul, hcoe_p]
      exact ((hfm.max measurable_const).mul (Real.measurable_log.comp hDm)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, hcoe_p, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbd_p p) (abs_nonneg _)
  have hlog_n : Integrable (fun p => Real.log (dist2 p)) μn := by
    rw [hμn, integrable_withDensity_iff_integrable_smul hfnm]
    refine hlog.mono (by
      simp only [NNReal.smul_def, smul_eq_mul, hcoe_n]
      exact ((hfm.neg.max measurable_const).mul (Real.measurable_log.comp hDm)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, hcoe_n, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbd_n p) (abs_nonneg _)
  obtain ⟨hIp, hEp⟩ := LQGDimension.HeatKernel.heatRep_of_integrable_log μp dist2 hDm hpos_p hlog_p
  obtain ⟨hIn, hEn⟩ := LQGDimension.HeatKernel.heatRep_of_integrable_log μn dist2 hDm hpos_n hlog_n
  -- equal masses
  have hmass : μp.real univ = μn.real univ := by
    have e1 := hint_p (fun _ => 1)
    have e2 := hint_n (fun _ => 1)
    simp only [integral_const, smul_eq_mul, mul_one] at e1 e2
    rw [e1, e2, ← sub_eq_zero, ← integral_sub hip hin]
    simpa [hmax] using hf0
  -- the difference of the two representations
  have hexp_int : ∀ τ : ℝ, ∀ g : ℂ × ℂ → ℝ, Integrable g →
      Integrable (fun p => g p * Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2))) := by
    intro τ g hg
    refine hg.mul_of_top_left ?_
    refine memLp_top_of_bound (by fun_prop) 1 (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (dist2 p)]) (by positivity)
  have hdiff : ∀ τ : ℝ, (∫ p, Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2)) ∂μp -
        μp.real univ * Real.exp (-1 / (4 * τ ^ 2))) / τ -
      (∫ p, Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2)) ∂μn -
        μn.real univ * Real.exp (-1 / (4 * τ ^ 2))) / τ =
      (∫ p, f p * Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2))) / τ := by
    intro τ
    rw [hint_p, hint_n, hmass, ← sub_div]
    congr 1
    rw [sub_sub_sub_cancel_right, ← integral_sub (hexp_int τ _ hip) (hexp_int τ _ hin)]
    congr 1; funext p
    rw [← sub_mul, hmax]
  have hL : ∫ τ in Ioi 0, (∫ p, f p * Real.exp (-dist2 p ^ 2 / (4 * τ ^ 2))) / τ =
      (-∫ p, Real.log (dist2 p) ∂μp) - (-∫ p, Real.log (dist2 p) ∂μn) := by
    rw [← hEp, ← hEn, ← integral_sub hIp hIn]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    exact (hdiff τ).symm
  have I1 : Integrable (fun p => max (f p) 0 * Real.log (dist2 p)) :=
    hlog.mono ((hfm.max measurable_const).mul (Real.measurable_log.comp hDm)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbd_p p) (abs_nonneg _))
  have I2 : Integrable (fun p => max (-f p) 0 * Real.log (dist2 p)) :=
    hlog.mono ((hfm.neg.max measurable_const).mul (Real.measurable_log.comp hDm)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbd_n p) (abs_nonneg _))
  rw [hL, hint_p, hint_n, show ∀ A B : ℝ, -A - -B = -(A - B) from fun A B => by ring,
    ← integral_sub I1 I2]
  congr 2; funext p
  rw [← sub_mul, hmax]

/-- The substitution `t = 2τ²`: `∫_0^∞ G(t)/(2t) dt = ∫_0^∞ G(2τ²)/τ dτ`. -/
lemma integral_Ioi_subst (G : ℝ → ℝ) :
    ∫ t in Ioi 0, G t / (2 * t) = ∫ τ in Ioi 0, G (2 * τ ^ 2) / τ := by
  have h1 := integral_comp_rpow_Ioi (fun t => G t / (2 * t)) (p := 2) two_ne_zero
  have h1' : ∫ x in Ioi 0, (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • (G (x ^ (2 : ℝ)) / (2 * x ^ (2 : ℝ))) =
      ∫ x in Ioi 0, G (x ^ 2) / x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    simp only [smul_eq_mul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two]
    field_simp
  rw [← h1, h1']
  have h2 := integral_comp_mul_left_Ioi (fun x => G (x ^ 2) / x) 0 (b := Real.sqrt 2)
    (Real.sqrt_pos.mpr two_pos)
  rw [mul_zero] at h2
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
  have h3 : ∫ τ in Ioi 0, G (2 * τ ^ 2) / τ =
      Real.sqrt 2 * ∫ x in Ioi 0, G ((Real.sqrt 2 * x) ^ 2) / (Real.sqrt 2 * x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : x ≠ 0 := (mem_Ioi.mp hx).ne'
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    field_simp
  rw [h3, h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

lemma logBallFun_sub_comm (x y : ℂ) : logBallFun (y - x) = logBallFun (x - y) := by
  unfold logBallFun
  simp only [indicator, mem_closedBall_zero_iff, norm_sub_rev]

lemma integrable_of_bound_ball {φ : ℂ → ℝ} {R M : ℝ} (hφm : Measurable φ)
    (hφ : ∀ x, |φ x| ≤ M) (hφR : ∀ x, R < ‖x‖ → φ x = 0) : Integrable φ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφ 0)
  refine Integrable.mono' ((integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (s := closedBall (0 : ℂ) R) (C := M) measure_closedBall_lt_top.ne))
    hφm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · rw [indicator_of_mem hx, Real.norm_eq_abs]; exact hφ x
  · have hx' : R < ‖x‖ := by simpa using hx
    rw [indicator_of_notMem hx, hφR x hx', norm_zero]

/-- **Heat-kernel representation of `logCov`.** For bounded measurable `φ, ψ` vanishing outside
`B̄_R(0)`, with `∫ ψ = 0`: `logCov φ ψ = ∫_0^∞ π ∫∫ φ(u) ψ(v) p_t(u, v) d(u,v) dt`. -/
theorem logCov_eq_integral_heat {φ ψ : ℂ → ℝ} {R M N : ℝ} (hR : 0 ≤ R) (hφm : Measurable φ)
    (hψm : Measurable ψ) (hφ : ∀ x, |φ x| ≤ M) (hψ : ∀ y, |ψ y| ≤ N)
    (hφR : ∀ x, R < ‖x‖ → φ x = 0) (hψR : ∀ y, R < ‖y‖ → ψ y = 0) (hψ0 : ∫ y, ψ y = 0) :
    ∫ t in Ioi 0, Real.pi * ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * heatKernel t p.1 p.2 = logCov φ ψ := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hφ 0)
  have hN : 0 ≤ N := (abs_nonneg _).trans (hψ 0)
  set f : ℂ × ℂ → ℝ := fun p => φ p.1 * ψ p.2 with hf
  have hfm : Measurable f := (hφm.comp measurable_fst).mul (hψm.comp measurable_snd)
  have hφi := integrable_of_bound_ball hφm hφ hφR
  have hψi := integrable_of_bound_ball hψm hψ hψR
  have hfi : Integrable f := hφi.mul_prod hψi
  have hf0 : ∫ p, f p = 0 := by
    rw [show (volume : Measure (ℂ × ℂ)) = volume.prod volume from rfl, integral_prod_mul, hψ0,
      mul_zero]
  set B : Set ℂ := closedBall (0 : ℂ) R with hB
  have hDm : Measurable dist2 := by unfold dist2; fun_prop
  -- integrability of `f · log D`
  have hdom1 : Integrable ((B ×ˢ B).indicator fun _ : ℂ × ℂ => M * N * (2 * R)) :=
    (integrable_indicator_iff (measurableSet_closedBall.prod measurableSet_closedBall)).2
      (integrableOn_const (by
        rw [show (volume : Measure (ℂ × ℂ)) = volume.prod volume from rfl, Measure.prod_prod]
        exact ENNReal.mul_ne_top measure_closedBall_lt_top.ne measure_closedBall_lt_top.ne))
  have hdom2 : Integrable fun p : ℂ × ℂ => M * N * (B.indicator (fun _ => (1 : ℝ)) p.1 *
      logBallFun (p.1 - p.2)) := by
    refine Integrable.const_mul ?_ _
    have hg : Integrable (fun q : ℂ × ℂ => B.indicator (fun _ => (1 : ℝ)) q.1 * logBallFun q.2)
        (volume.prod volume) :=
      ((integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)).mul_prod integrable_logBallFun
    have := (measurePreserving_prod_sub (volume : Measure ℂ) (volume : Measure ℂ)).integrable_comp_of_integrable hg
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply]
    rw [logBallFun_sub_comm]
  have hlog : Integrable (fun p => f p * Real.log (dist2 p)) := by
    refine (hdom1.add hdom2).mono' (hfm.mul (Real.measurable_log.comp hDm)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, Pi.add_apply]
    by_cases hp : p.1 ∈ B ∧ p.2 ∈ B
    · have h1 : ‖p.1‖ ≤ R := by simpa [hB] using hp.1
      have h2 : ‖p.2‖ ≤ R := by simpa [hB] using hp.2
      rw [indicator_of_mem (mem_prod.mpr hp), indicator_of_mem hp.1, one_mul]
      have hl := abs_log_norm_le (p.1 - p.2)
      have hd : ‖p.1 - p.2‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
      have h3 := logBallFun_nonneg (p.1 - p.2)
      simp only [hf, abs_mul, dist2]
      calc |φ p.1| * |ψ p.2| * |Real.log ‖p.1 - p.2‖|
          ≤ M * N * (2 * R + logBallFun (p.1 - p.2)) :=
            mul_le_mul (mul_le_mul (hφ _) (hψ _) (abs_nonneg _) hM) (by linarith) (abs_nonneg _)
              (mul_nonneg hM hN)
        _ = _ := by ring
    · have h0 : f p = 0 := by
        simp only [hf]
        rcases not_and_or.mp hp with h | h
        · rw [hφR _ (by simpa [hB] using h), zero_mul]
        · rw [hψR _ (by simpa [hB] using h), mul_zero]
      rw [h0, zero_mul, abs_zero]
      refine add_nonneg (indicator_nonneg (fun _ _ => by positivity) _) ?_
      exact mul_nonneg (mul_nonneg hM hN) (mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
        (logBallFun_nonneg _))
  have key := heatRep_signed hfm hfi hf0 hlog
  -- left side: substitution `t = 2τ²`
  have hLHS : ∫ t in Ioi 0, Real.pi * ∫ p : ℂ × ℂ, φ p.1 * ψ p.2 * heatKernel t p.1 p.2 =
      ∫ t in Ioi 0, (∫ p, f p * Real.exp (-dist2 p ^ 2 / (2 * t))) / (2 * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
    simp only [heatKernel]
    have : ∀ p : ℂ × ℂ, φ p.1 * ψ p.2 * ((2 * Real.pi * t)⁻¹ *
        Real.exp (-‖p.1 - p.2‖ ^ 2 / (2 * t))) =
        (2 * Real.pi * t)⁻¹ * (f p * Real.exp (-dist2 p ^ 2 / (2 * t))) := fun p => by
      simp only [hf, dist2]; ring
    simp_rw [this]
    rw [integral_const_mul]
    field_simp
  rw [hLHS, integral_Ioi_subst (fun t => ∫ p, f p * Real.exp (-dist2 p ^ 2 / (2 * t)))]
  have h4 : ∀ τ : ℝ, (2 * (2 * τ ^ 2)) = 4 * τ ^ 2 := fun τ => by ring
  simp_rw [h4]
  rw [key, ← integral_neg]
  unfold logCov
  have hint : Integrable (fun p => -(f p * Real.log (dist2 p))) (volume.prod volume) := hlog.neg
  rw [show (volume : Measure (ℂ × ℂ)) = volume.prod volume from rfl, integral_prod _ hint]
  congr 1; funext x; congr 1; funext y
  simp only [hf, dist2]; ring

end GFFExist
end LQGMetric
