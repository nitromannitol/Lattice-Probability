import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import LatticeProb.Analysis.DistributionalLaplacian
import LatticeProb.Bonanno.LQGMetric.Field.WholePlaneCov
import LatticeProb.Analysis.RotationalAverage
import LatticeProb.Analysis.LogPotentialCircle

/-!
# Logarithmic integrability of test functions on the plane

For a test function `φ` on `ℂ` (smooth with compact support) the logarithmic singularity at the origin is
integrable against `φ`: `x ↦ φ x * log ‖x‖` and `x ↦ |φ x| * (2 log max(‖x‖, 1) - log ‖x‖)` are integrable,
and `y ↦ φ y * wholePlaneCov x y` is integrable for every `x`. The proof bounds `|log t|` on `(0, R]` by the
integrable power `2 (1 + R) t^{-1/2}`, so that the singularity is dominated on a ball
(Duplantier-Sheffield, *Liouville quantum gravity
and KPZ*, Invent. Math. 185 (2011), arXiv:0808.1560, Section 3.1).
-/

noncomputable section

namespace LatticeProb.TestFunctionLogIntegrable

open MeasureTheory Filter Topology Set Metric

/-- `|log t| ≤ 2 (1 + R) t^{-1/2}` on `(0, R]` (elementary: `log u ≤ u - 1`). -/
lemma abs_log_le_rpow_neg_half {t R : ℝ} (ht : 0 < t) (htR : t ≤ R) :
    |Real.log t| ≤ 2 * (1 + R) * t ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hrp : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
  rw [hrp, abs_le]
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht.le]; ring
  have hup : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs
  have hlo : Real.log (Real.sqrt t)⁻¹ ≤ (Real.sqrt t)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at hlo
  have hsR : Real.sqrt t ≤ R * (Real.sqrt t)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hs]
    nlinarith
  have hinv_pos : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 hs
  constructor
  · nlinarith
  · nlinarith

/-- `x ↦ φ x * log ‖x‖` is integrable for a test function `φ` (logarithmic singularity at `0`). -/
lemma integrable_test_mul_log_norm {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => φ x * Real.log ‖x‖) := by
  obtain ⟨hc, hcs, -⟩ := hφ
  obtain ⟨R, hR⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1 hcs.isCompact.isBounded
  obtain ⟨M, hM⟩ := hc.continuous.bounded_above_of_compact_support hcs
  have hsub : tsupport φ ⊆ ball (0 : ℂ) (R + 1) := hR.trans (closedBall_subset_ball (by linarith))
  have hsupp : Function.support (fun x : ℂ => φ x * Real.log ‖x‖) ⊆ ball (0 : ℂ) (R + 1) := by
    intro x hx
    apply hsub
    apply subset_tsupport
    intro h0
    apply hx
    simp [h0]
  have hd : 1 ≤ Module.finrank ℝ ℂ := by simp
  have hα : (1 / 2 : ℝ) < (Module.finrank ℝ ℂ : ℝ) := by simp; norm_num
  have hmeas : AEStronglyMeasurable (fun x : ℂ => φ x * Real.log ‖x‖) volume :=
    (hc.continuous.measurable.mul (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  have hdecay : ∀ᵐ x ∂(volume.restrict (ball (0 : ℂ) (R + 1))),
      ‖φ x * Real.log ‖x‖‖ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by
    refine ae_of_all _ fun x => ?_
    rcases eq_or_ne ‖x‖ 0 with h0 | h0
    · have : x = 0 := norm_eq_zero.1 h0
      subst this
      simp
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      by_cases hx : ‖x‖ ≤ R + 1
      · rw [norm_mul, Real.norm_eq_abs]
        have h1 := abs_log_le_rpow_neg_half hxpos hx
        have h2 : ‖φ x‖ ≤ M := hM x
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        have h3 : 0 ≤ ‖x‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        calc ‖φ x‖ * |Real.log ‖x‖| ≤ M * (2 * (1 + (R + 1)) * ‖x‖ ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul h2 h1 (abs_nonneg _) ((norm_nonneg _).trans h2)
          _ = (M * (2 * (1 + (R + 1)))) * ‖x‖ ^ (-(1 / 2 : ℝ)) := by ring
          _ ≤ (M * (2 * (1 + |R + 1|))) * ‖x‖ ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (by linarith [le_abs_self (R + 1)]) hM0) h3
      · have hout : x ∉ tsupport φ := fun hxt => hx (by
          have := hR hxt
          rw [mem_closedBall, dist_zero_right] at this
          linarith)
        have : φ x = 0 := image_eq_zero_of_notMem_tsupport hout
        have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
        simp only [this, zero_mul, norm_zero]
        exact mul_nonneg (mul_nonneg hM0 (by positivity)) (Real.rpow_nonneg (norm_nonneg _) _)
  have hloc : IntegrableOn (fun x : ℂ => φ x * Real.log ‖x‖) (ball (0 : ℂ) (R + 1)) :=
    integrableOn_ball_of_norm_le_rpow hd hα hdecay hmeas
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hloc

/-- The diagonal circle-circle covariance `2 log max(|x|,1) - log |x|` is nonnegative. -/
lemma diag_nonneg (x : ℂ) : 0 ≤ 2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖ := by
  rcases le_total ‖x‖ 1 with h | h
  · rw [max_eq_right h, Real.log_one]
    have : Real.log ‖x‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) h
    linarith
  · rw [max_eq_left h]
    have : 0 ≤ Real.log ‖x‖ := Real.log_nonneg h
    linarith

/-- `|φ(x)| (2 log max(|x|,1) - log |x|)` is integrable for a test function `φ`. -/
lemma integrable_abs_test_mul_diag {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Integrable (fun x : ℂ => |φ x| * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) := by
  have hcont : Continuous (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) := by
    refine hφ.1.continuous.mul (Continuous.log (continuous_norm.max continuous_const) fun x => ?_)
    exact (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  have h1 : Integrable (fun x : ℂ => φ x * Real.log (max ‖x‖ 1)) :=
    hcont.integrable_of_hasCompactSupport (hφ.2.1.mul_right)
  have h2 := (h1.const_mul 2).sub (integrable_test_mul_log_norm hφ)
  have h3 : Integrable (fun x : ℂ => φ x * (2 * Real.log (max ‖x‖ 1) - Real.log ‖x‖)) :=
    h2.congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  refine (h3.abs).congr (ae_of_all _ fun x => ?_)
  simp only
  rw [abs_mul, abs_of_nonneg (diag_nonneg x)]

/-- Against a test function the logarithmic kernel is integrable: `y ↦ ψ y · wholePlaneCov x y` is integrable. -/
lemma integrable_test_mul_wholePlaneCov {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) (x : ℂ) :
    Integrable (fun y : ℂ => ψ y * wholePlaneCov x y) := by
  have hψc : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hlogM : Integrable (fun y : ℂ => ψ y * Real.log (max ‖y‖ 1)) := by
    refine Continuous.integrable_of_hasCompactSupport (hψ.1.continuous.mul
      (Continuous.log (continuous_norm.max continuous_const) fun y => (max_norm_pos y).ne')) ?_
    exact hψ.2.1.mul_right
  have hlog : Integrable (fun y : ℂ => ψ y * Real.log ‖x - y‖) := by
    have hψx : IsTestFunction Set.univ (fun v : ℂ => ψ (x - v)) :=
      ⟨hψ.1.comp (contDiff_const.sub contDiff_id), hψ.2.1.comp_homeomorph (Homeomorph.subLeft x),
        Set.subset_univ _⟩
    have h := (integrable_test_mul_log_norm hψx).comp_sub_left x
    refine h.congr (ae_of_all _ fun y => ?_)
    simp
  have hsum : Integrable (fun y : ℂ => Real.log (max ‖x‖ 1) * ψ y + ψ y * Real.log (max ‖y‖ 1)
      - ψ y * Real.log ‖x - y‖) :=
    ((hψc.const_mul _).add hlogM).sub hlog
  have hne : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  refine hsum.congr ?_
  filter_upwards [hne] with y hy
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  unfold wholePlaneCov
  rw [Real.log_div (mul_pos (max_norm_pos x) (max_norm_pos y)).ne' (norm_ne_zero_iff.mpr hxy),
    Real.log_mul (max_norm_pos x).ne' (max_norm_pos y).ne']
  ring

/-- Rotational averaging of the logarithmic kernel: for a radial test function `ψ` and every `x`,
`∫ ψ(y) wholePlaneCov(x,y) dy = ∫ ψ(y) (log max(|x|,1) + log max(|y|,1) - log max(|x|,|y|)) dy`. -/
lemma integral_test_mul_wholePlaneCov {ψ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ)
    (hψr : ∀ (θ : ℝ) (x : ℂ), ψ (LatticeProb.RotationalAverage.rot θ x) = ψ x) (x : ℂ) :
    ∫ y, ψ y * wholePlaneCov x y = ∫ y, ψ y *
      (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
  have hm : Measurable (fun y : ℂ => wholePlaneCov x y) := by
    unfold wholePlaneCov
    fun_prop
  have h := LatticeProb.RotationalAverage.integral_avgRot_mul (Φ := fun y => wholePlaneCov x y) (g := ψ) hm
    hψ.1.continuous.measurable hψr
    (by simpa only [mul_comm] using integrable_test_mul_wholePlaneCov hψ x)
  have hne0 : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ 0 := by
    rw [ae_iff]
    simp
  calc ∫ y, ψ y * wholePlaneCov x y = ∫ y, wholePlaneCov x y * ψ y := by
        simp only [mul_comm]
    _ = ∫ y, LatticeProb.RotationalAverage.avgRot (fun w => wholePlaneCov x w) y * ψ y := h.symm
    _ = ∫ y, ψ y * (Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log (max ‖x‖ ‖y‖)) := by
        refine integral_congr_ae ?_
        filter_upwards [hne0] with y hy
        rw [LatticeProb.RotationalAverage.avgRot_eq_circleAverage,
          LatticeProb.LogPotentialCircle.circleAverage_wholePlaneCov (norm_pos_iff.mpr hy), mul_comm,
          max_comm ‖y‖ ‖x‖]

end LatticeProb.TestFunctionLogIntegrable

@[deprecated LatticeProb.TestFunctionLogIntegrable.integrable_test_mul_wholePlaneCov (since := "2026-11-11")]
alias LatticeProb.integrable_test_mul_wholePlaneCov :=
  LatticeProb.TestFunctionLogIntegrable.integrable_test_mul_wholePlaneCov

end
