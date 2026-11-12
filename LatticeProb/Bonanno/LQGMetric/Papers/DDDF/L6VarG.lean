/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6VarG at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6VarL
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# DDDF Lemma 6: the `W'`-part of `φ_L` (DDDF's `φ_{2,2}`) has bounded variance on `K`

DDDF (arXiv:1904.08021, `tightness.tex` l. 619–640, "Second term"): the kernel
`gKer x = k_{δ,F(x)} 1_{((0,∞)×V)ᶜ}` only sees points `z ∉ V = F(U)`, at distance
`≥ d = d(F(K), Vᶜ) > 0` from `F(x)` for `x ∈ K` (the paper's `d = d(K, Uᶜ)` for `φ_{2,1}`, l. 633).
Pointwise `k² ≤ (πt)⁻² e^{−d²/t} e^{−|z − F x|²/t}`, the Gaussian integral in `z` gives
`e^{−d²/t}/(πt) ≤ 1/(πd²)` (`e^{−v} ≤ 1/v`), and `t ∈ [δ², 1]`: `‖gKer x‖² ≤ 1/(πd²)`.
(Own elementary bound for the pointwise variance of this piece; DDDF only treat its increments.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The dominating function for `‖gKer h δ x‖²`. -/
def gBound (F : ℂ → ℂ) (d δ : ℝ) (x : ℂ) (p : ℝ × ℂ) : ℝ≥0∞ :=
  (Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)).indicator (fun p : ℝ × ℂ =>
    ENNReal.ofReal ((Real.pi * p.1)⁻¹ ^ 2 * Real.exp (-d ^ 2 / p.1)) *
      ENNReal.ofReal (Real.exp (-(1 / p.1) * ‖p.2 - F x‖ ^ 2))) p

lemma enorm_phiKernel_sq_le {d δ : ℝ} (hδ : 0 < δ) {x : ℂ}
    (hx : ∀ z ∉ F '' U, d ≤ ‖F x - z‖) (hd : 0 ≤ d) {p : ℝ × ℂ}
    (hp : p ∈ (pushTarget F U)ᶜ) :
    ‖phiKernel δ 1 (F x) p‖ₑ ^ (2 : ℝ) ≤ gBound F d δ x p := by
  obtain ⟨t, z⟩ := p
  rw [phiKernel, gBound]
  by_cases hK : (t, z) ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)
  swap
  · rw [indicator_of_notMem hK, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  rw [indicator_of_mem hK, indicator_of_mem hK]
  have ht : δ ^ 2 ≤ t := (mem_Icc.1 (mem_prod.1 hK).1).1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hz : z ∉ F '' U := fun hz => hp (mk_mem_prod (show t ∈ Ioi 0 from ht0) hz)
  have hr := hx z hz
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have e1 : heatKernel (t / 2) (F x) z = (Real.pi * t)⁻¹ * Real.exp (-‖F x - z‖ ^ 2 / t) := by
    unfold heatKernel
    rw [show 2 * Real.pi * (t / 2) = Real.pi * t by ring, show 2 * (t / 2) = t by ring]
  rw [e1, Real.rpow_two, sq_abs, mul_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add, norm_sub_rev z (F x)]
  apply Real.exp_le_exp.2
  have hr2 : d ^ 2 ≤ ‖F x - z‖ ^ 2 := pow_le_pow_left₀ hd hr 2
  have e2 : ((2 : ℕ) : ℝ) * (-‖F x - z‖ ^ 2 / t) = -(2 * ‖F x - z‖ ^ 2) / t := by
    push_cast; ring
  have e3 : -d ^ 2 / t + -(1 / t) * ‖F x - z‖ ^ 2 = -(d ^ 2 + ‖F x - z‖ ^ 2) / t := by ring
  rw [e2, e3]
  exact div_le_div_of_nonneg_right (by linarith) ht0.le

lemma lintegral_gBound_le {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) (x : ℂ) :
    ∫⁻ p, gBound F d δ x p ≤ ENNReal.ofReal (1 / (Real.pi * d ^ 2)) := by
  have hpi := Real.pi_pos
  have inner : ∀ t, ∫⁻ z, gBound F d δ x (t, z) ≤
      (Icc (δ ^ 2) (1 ^ 2)).indicator (fun _ => ENNReal.ofReal (1 / (Real.pi * d ^ 2))) t := by
    intro t
    by_cases ht : t ∈ Icc (δ ^ 2) (1 ^ 2)
    swap
    · have e0 : ∀ z, gBound F d δ x (t, z) = 0 := fun z => by
        rw [gBound, indicator_of_notMem (fun hh => ht (mem_prod.1 hh).1)]
      simp [e0]
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    rw [indicator_of_mem ht]
    have e : ∀ z, gBound F d δ x (t, z) =
        ENNReal.ofReal ((Real.pi * t)⁻¹ ^ 2 * Real.exp (-d ^ 2 / t)) *
          ENNReal.ofReal (Real.exp (-(1 / t) * ‖z - F x‖ ^ 2)) := fun z => by
      rw [gBound, indicator_of_mem (mk_mem_prod ht (mem_univ z))]
    simp_rw [e]
    have hb : 0 < 1 / t := by positivity
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal
          ((integrable_rexp_neg_mul_sq_norm_complex hb).comp_sub_right (F x))
          (Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_sub_right_eq_self (fun w : ℂ => Real.exp (-(1 / t) * ‖w‖ ^ 2)) (F x),
      GaussianFourier.integral_rexp_neg_mul_sq_norm hb, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    simp only [Complex.finrank_real_complex]
    norm_num
    -- `(πt)⁻² e^{−d²/t} π t ≤ 1/(πd²)` from `e^{−d²/t} ≤ t/d²`
    have hexp : Real.exp (-d ^ 2 / t) ≤ t / d ^ 2 := by
      have h1 := Real.add_one_le_exp (d ^ 2 / t)
      rw [neg_div, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      linarith
    calc _ = Real.exp (-d ^ 2 / t) / (Real.pi * t) := by field_simp
      _ ≤ (t / d ^ 2) / (Real.pi * t) := by gcongr
      _ = _ := by field_simp
  calc ∫⁻ p, gBound F d δ x p ≤ ∫⁻ t, ∫⁻ z, gBound F d δ x (t, z) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ ≤ ∫⁻ t, (Icc (δ ^ 2) (1 ^ 2)).indicator
        (fun _ => ENNReal.ofReal (1 / (Real.pi * d ^ 2))) t := lintegral_mono inner
    _ = ENNReal.ofReal (1 / (Real.pi * d ^ 2)) * volume (Icc (δ ^ 2) (1 ^ 2)) :=
        lintegral_indicator_const measurableSet_Icc _
    _ ≤ _ := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have : 1 ^ 2 - δ ^ 2 ≤ (1 : ℝ) := by nlinarith
        calc 1 / (Real.pi * d ^ 2) * (1 ^ 2 - δ ^ 2) ≤ 1 / (Real.pi * d ^ 2) * 1 := by
              gcongr
          _ = _ := mul_one _

/-- `‖gKer h δ x‖² ≤ 1/(πd²)` when `F(x)` is at distance `≥ d` from `Vᶜ`. -/
lemma norm_sq_gKer_le (h : ConfHyp F U) {d δ : ℝ} (hd : 0 < d) (hδ : 0 < δ) {x : ℂ}
    (hx : ∀ z ∉ F '' U, d ≤ ‖F x - z‖) :
    ‖gKer h δ x‖ ^ 2 ≤ 1 / (Real.pi * d ^ 2) := by
  rw [gKer, norm_sq_cutL2]
  rw [lintegral_congr_ae (g := fun q => ‖phiKernel δ 1 (F x) q‖ₑ ^ (2 : ℝ))
    (ae_restrict_of_ae ((coeFn_phiKernelL2 δ 1 hδ (F x)).mono fun q hq => by simp only [hq]))]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ ∫⁻ q in (pushTarget F U)ᶜ, gBound F d δ x q :=
        setLIntegral_mono' h.measurableSet_pushTarget.compl
          fun q hq => enorm_phiKernel_sq_le hδ hx hd.le hq
    _ ≤ ∫⁻ q, gBound F d δ x q := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_gBound_le hd hδ x

/-- For compact `K ⊆ U`, `F(K)` is at positive distance from `Vᶜ` (open mapping theorem for the
univalent `F`, QuantumZipper `isOpen_image_of_injOn'`). -/
lemma exists_dist_image_compl (h : ConfHyp F U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d, 0 < d ∧ ∀ x ∈ K, ∀ z ∉ F '' U, d ≤ ‖F x - z‖ := by
  have hV := QuantumZipper.CA.isOpen_image_of_injOn' h.isOpen h.diff h.inj
  have hFK : IsCompact (F '' K) := hK.image_of_continuousOn (h.diff.continuousOn.mono hKU)
  obtain ⟨d, hd, hsub⟩ := hFK.exists_cthickening_subset_open hV (image_mono hKU)
  refine ⟨d, hd, fun x hx z hz => ?_⟩
  refine le_of_not_gt fun hlt => ?_
  refine hz (hsub (mem_cthickening_of_dist_le z (F x) d _ (mem_image_of_mem F hx) ?_))
  rw [dist_eq_norm, norm_sub_rev]; exact hlt.le

/-- **Uniform bound for the `W'`-kernel of `φ_L`** on `K`. -/
theorem l6_gKer_bounded (h : ConfHyp F U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ δ, 0 < δ → ∀ x ∈ K, ‖gKer h δ x‖ ^ 2 ≤ C := by
  obtain ⟨d, hd, hx⟩ := exists_dist_image_compl h hK hKU
  exact ⟨1 / (Real.pi * d ^ 2), fun δ hδ x hxK => norm_sq_gKer_le h hd hδ (hx x hxK)⟩

end DDDF
end LQGMetric
