/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicLowBandBox at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicCompareCoupling
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P28Sup
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.GaussianTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_low_band_box_signed_tail
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (x₀ : ℂ) (b : ℝ) (hb : 0 < b)
    (a : ℝ) (ha12 : 1 / 2 ≤ a) (ha1 : a ≤ 1)
    (sgn : ℝ) (hsgn : sgn ^ 2 = 1)
    (u : ℝ) (hu : 0 ≤ u) :
    P.real {ω | ferniqueCF * Real.sqrt ((8 * b) * b) + u ≤
      ⨆ v : ferniqueBox x₀ b, sgn * phiVer W P a 1 v ω} ≤
      Real.exp (-u ^ 2 / 2) := by
  have := hW.isProbabilityMeasure
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha12
  have hY := isPhiVersion_phiVer hW ha0 ha1
  let Y : ℂ → Ω → ℝ := fun v ω => sgn * phiVer W P a 1 v ω
  have hG : IsGaussianProcess Y P := by
    have h := (isGaussianProcess_phi_comp hW a 1 (fun v : ℂ => v)).congr
      (fun v => (hY.ae_eq v).symm)
    simpa only [Y, smul_eq_mul] using h.smul (fun _ => sgn)
  have h0 : ∀ v, ∫ ω, Y v ω ∂P = 0 := by
    intro v
    rw [integral_const_mul, integral_congr_ae (hY.ae_eq v), integral_phi hW, mul_zero]
  have hcont : ∀ ω, ContinuousOn (fun v => Y v ω) (ferniqueBox x₀ b) :=
    fun ω => (continuous_const.mul (hY.cont ω)).continuousOn
  have hinc : ∀ v ∈ ferniqueBox x₀ b, ∀ w ∈ ferniqueBox x₀ b,
      ∫ ω, (Y w ω - Y v ω) ^ 2 ∂P ≤ (8 * b) * ‖v - w‖ := by
    intro v hv w hw
    have hm : AEMeasurable (fun ω => phi W a 1 w ω - phi W a 1 v ω) P :=
      ((measurable_phi hW a 1 w).sub (measurable_phi hW a 1 v)).aemeasurable
    have hmean : ∫ ω, (phi W a 1 w ω - phi W a 1 v ω) ∂P = 0 := by
      rw [integral_sub ((memLp_phi hW a 1 w).integrable one_le_two)
        ((memLp_phi hW a 1 v).integrable one_le_two), integral_phi hW,
        integral_phi hW, sub_zero]
    have hae : (fun ω => (Y w ω - Y v ω) ^ 2) =ᵐ[P]
        fun ω => (phi W a 1 w ω - phi W a 1 v ω) ^ 2 := by
      filter_upwards [hY.ae_eq v, hY.ae_eq w] with ω e₁ e₂
      simp only [Y]
      rw [e₁, e₂, ← mul_sub, mul_pow, hsgn, one_mul]
    rw [integral_congr_ae hae, ← variance_of_integral_eq_zero hm hmean]
    have hvar := LQGMetric.DZZ.dzz_variance_hat_sub_le hW ha0 ha1 w v
    have hdist := LQGMetric.DZZ.norm_sub_le_of_mem_ferniqueBox hv hw
    have hr0 : 0 ≤ ‖v - w‖ := norm_nonneg _
    have ha2 : (1 / 4 : ℝ) ≤ a ^ 2 := by nlinarith
    rw [norm_sub_rev] at hvar
    calc
      _ ≤ ‖v - w‖ ^ 2 / a ^ 2 := hvar
      _ ≤ ‖v - w‖ ^ 2 / (1 / 4) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) ha2
      _ ≤ (8 * b) * ‖v - w‖ := by nlinarith
  have hvar : ∀ v ∈ ferniqueBox x₀ b, Var[Y v; P] ≤ (1 : ℝ) ^ 2 := by
    intro v _
    rw [show Y v = sgn • phiVer W P a 1 v from rfl, variance_smul,
      variance_congr (hY.ae_eq v), variance_phi hW ha0 ha1, hsgn, one_mul,
      one_pow]
    have h2 : 1 / a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / a by positivity)
    linarith
  have htail := LQGMetric.DGo.box_sup_tail hG h0 hb (by positivity : 0 < 8 * b)
    hcont hinc hvar hu
  simpa only [one_pow, mul_one] using htail

end SupercriticalLQGUniqueness.B2.DG20Pt
