/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6VarH at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6Decomp

/-!
# DDDF Lemma 6, third term: `Var φ_H^{(δ)}(x) ≤ C` uniformly in `δ` and `x`

DDDF (Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `tightness.tex` l. 641–645, "Third term"),
after Dubédat–Falconet (arXiv:1809.02607, `LiouvilleMetricStarScale.tex`, Lemma 4.4). With
`c = |F'(y)|²`, the kernel of `φ_H^{(δ)}(x)` is (`hKer`)

  `(t, y) ↦ 1_{t < δ², y ∈ U, δ² ≤ tc ≤ 1} c p_{tc/2}(F x − F y)
          = 1_{…} (πt)⁻¹ e^{−|F x − F y|²/(tc)}`,

so `Var φ_H^{(δ)}(x) = π ‖hKer‖²` and the integrand of `‖hKer‖²` is at most
`1_{δ²/M² ≤ t ≤ δ²} 1_U(y) (πt)⁻² c e^{−2|F y − F x|²/(t M²)}` (`1 ≤ c ≤ M²`). DDDF bound the
`y`-integral via `|F x − F y| ≥ |x − y|/C`; we instead change variables `z = F(y)`
(`dz = c dy`, QuantumZipper `lintegral_comp_holo`) and integrate the Gaussian over `ℂ`:
`∫_U c e^{−2|F y − F x|²/(tM²)} dy ≤ ∫_ℂ e^{−2|z − F x|²/(tM²)} dz = π t M²/2`. The `t`-integral
over `[δ²/M², δ²]` of `(πt)⁻² π t M²/2 ≤ M⁴/(2πδ²)` is at most `M⁴/(2π)`. Hence
`Var φ_H^{(δ)}(x) ≤ M⁴/2` for every `δ > 0` and every `x` (`l6_var_phiH_le`).

Deviation (D-DDDF-L6H, own variant of the paper's step): the lower bound
`|F x − F y| ≥ |x − y|/C` (which needs convexity of `V` and a bound on `(F⁻¹)'`) is replaced
by the change of variables `z = F(y)`; this needs only `|F'| ≥ 1` and `|F'| ≤ M` on `U`, and gives
the bound for all `x`, not only `x ∈ K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace LQGMetric
namespace DDDF

open WhiteNoise WNPush

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The dominating function for the integrand of `‖hKer F U δ x‖²`. -/
def hBound (F : ℂ → ℂ) (U : Set ℂ) (M δ : ℝ) (x : ℂ) (p : ℝ × ℂ) : ℝ≥0∞ :=
  (Icc (δ ^ 2 / M ^ 2) (δ ^ 2) ×ˢ U).indicator (fun p : ℝ × ℂ =>
    ENNReal.ofReal ((Real.pi * p.1)⁻¹ ^ 2) * (ENNReal.ofReal (‖deriv F p.2‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-(2 / (p.1 * M ^ 2)) * ‖F p.2 - F x‖ ^ 2)))) p

/-- Pointwise domination of the `φ_H` kernel on times `t < δ²`. -/
lemma enorm_pushFunOf_sq_le {M δ : ℝ} (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖)
    (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) (x : ℂ) {p : ℝ × ℂ} (hp : p ∈ (timeHigh δ)ᶜ) :
    ‖pushFunOf F U (phiKernel δ 1 (F x)) p‖ₑ ^ (2 : ℝ) ≤ hBound F U M δ x p := by
  obtain ⟨t, y⟩ := p
  have ht : t < δ ^ 2 := by simpa [timeHigh] using hp
  by_cases hD : (t, y) ∈ Ioi (0 : ℝ) ×ˢ U
  swap
  · rw [pushFunOf, indicator_of_notMem hD, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  obtain ⟨ht0, hy⟩ := mem_prod.1 hD
  have ht0' : 0 < t := ht0
  simp only [hBound, pushFunOf, pushMap, phiKernel]
  rw [indicator_of_mem hD]
  by_cases hK : (t * ‖deriv F y‖ ^ 2, F y) ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)
  swap
  · rw [indicator_of_notMem hK, mul_zero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  rw [indicator_of_mem hK]
  set c := ‖deriv F y‖ ^ 2 with hc
  have hd1 := hF1 y hy
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcM : c ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM y hy) 2
  have htc : δ ^ 2 ≤ t * c := (mem_Icc.1 (mem_prod.1 hK).1).1
  have hM0 : 0 < M ^ 2 := by linarith
  have hmem : (t, y) ∈ Icc (δ ^ 2 / M ^ 2) (δ ^ 2) ×ˢ U := by
    refine mk_mem_prod ⟨?_, ht.le⟩ hy
    rw [div_le_iff₀ hM0]
    nlinarith
  rw [indicator_of_mem hmem]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ c),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi * t)⁻¹ ^ 2),
    Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  dsimp only
  apply ENNReal.ofReal_le_ofReal
  have hc0 : 0 < c := by linarith
  have e1 : c * heatKernel (t * c / 2) (F x) (F y) =
      (Real.pi * t)⁻¹ * Real.exp (-‖F x - F y‖ ^ 2 / (t * c)) := by
    unfold heatKernel
    rw [show 2 * Real.pi * (t * c / 2) = Real.pi * t * c by ring,
      show 2 * (t * c / 2) = t * c by ring]
    have := Real.pi_pos
    field_simp
  have e2 : Real.exp (-‖F x - F y‖ ^ 2 / (t * c)) ^ 2 =
      Real.exp (-(2 * ‖F x - F y‖ ^ 2) / (t * c)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hle : Real.exp (-(2 * ‖F x - F y‖ ^ 2) / (t * c)) ≤
      Real.exp (-(2 / (t * M ^ 2)) * ‖F y - F x‖ ^ 2) := by
    apply Real.exp_le_exp.2
    rw [norm_sub_rev (F y) (F x), neg_div, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcM ht0'.le)
  rw [e1, Real.rpow_two, sq_abs, mul_pow, e2]
  exact mul_le_mul_of_nonneg_left (hle.trans (le_mul_of_one_le_left (Real.exp_pos _).le hc1))
    (by positivity)

/-- `∫ hBound ≤ M⁴/(2π)`, uniformly in `δ` and `x`. -/
lemma lintegral_hBound_le (h : ConfHyp F U) {M δ : ℝ} (hM1 : 1 ≤ M) (hδ : 0 < δ) (x : ℂ) :
    ∫⁻ p, hBound F U M δ x p ≤ ENNReal.ofReal (M ^ 4 / (2 * Real.pi)) := by
  have hM0 : 0 < M ^ 2 := by positivity
  have hpi := Real.pi_pos
  have inner : ∀ t, ∫⁻ y, hBound F U M δ x (t, y) ≤
      (Icc (δ ^ 2 / M ^ 2) (δ ^ 2)).indicator
        (fun _ => ENNReal.ofReal (M ^ 4 / (2 * Real.pi * δ ^ 2))) t := by
    intro t
    by_cases ht : t ∈ Icc (δ ^ 2 / M ^ 2) (δ ^ 2)
    swap
    · have e0 : ∀ y, hBound F U M δ x (t, y) = 0 := fun y => by
        rw [hBound, indicator_of_notMem (fun hh => ht (mem_prod.1 hh).1)]
      simp [e0]
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
    rw [indicator_of_mem ht]
    have e : ∀ y, hBound F U M δ x (t, y) = U.indicator (fun y =>
        ENNReal.ofReal ((Real.pi * t)⁻¹ ^ 2) * (ENNReal.ofReal (‖deriv F y‖ ^ 2) *
          ENNReal.ofReal (Real.exp (-(2 / (t * M ^ 2)) * ‖F y - F x‖ ^ 2)))) y := by
      intro y
      by_cases hy : y ∈ U
      · rw [hBound, indicator_of_mem (mk_mem_prod ht hy), indicator_of_mem hy]
      · rw [hBound, indicator_of_notMem (fun hh => hy (mem_prod.1 hh).2),
          indicator_of_notMem hy]
    simp_rw [e]
    rw [lintegral_indicator h.isOpen.measurableSet, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← QuantumZipper.lintegral_comp_holo h.isOpen h.diff h.inj h.deriv_ne
        h.isOpen.measurableSet subset_rfl
        (fun w => ENNReal.ofReal (Real.exp (-(2 / (t * M ^ 2)) * ‖w - F x‖ ^ 2)))]
    have hb : 0 < 2 / (t * M ^ 2) := by positivity
    have hG : ∫⁻ w, ENNReal.ofReal (Real.exp (-(2 / (t * M ^ 2)) * ‖w - F x‖ ^ 2)) =
        ENNReal.ofReal (Real.pi / (2 / (t * M ^ 2))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrable_rexp_neg_mul_sq_norm_complex hb).comp_sub_right (F x))
          (Eventually.of_forall fun _ => (Real.exp_pos _).le),
        integral_sub_right_eq_self (fun w : ℂ => Real.exp (-(2 / (t * M ^ 2)) * ‖w‖ ^ 2)) (F x),
        GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
      simp only [Complex.finrank_real_complex]
      norm_num
    calc _ ≤ ENNReal.ofReal ((Real.pi * t)⁻¹ ^ 2) *
          ∫⁻ w, ENNReal.ofReal (Real.exp (-(2 / (t * M ^ 2)) * ‖w - F x‖ ^ 2)) := by
          gcongr; exact Measure.restrict_le_self
      _ = ENNReal.ofReal ((Real.pi * t)⁻¹ ^ 2 * (Real.pi / (2 / (t * M ^ 2)))) := by
          rw [hG, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have ht1 : δ ^ 2 / M ^ 2 ≤ t := ht.1
          rw [div_le_iff₀ hM0] at ht1
          rw [show (Real.pi * t)⁻¹ ^ 2 * (Real.pi / (2 / (t * M ^ 2))) =
              M ^ 2 / (2 * Real.pi * t) by field_simp]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi * M ^ 2)
          nlinarith [this]
  calc ∫⁻ p, hBound F U M δ x p ≤ ∫⁻ t, ∫⁻ y, hBound F U M δ x (t, y) := by
        rw [Measure.volume_eq_prod]; exact lintegral_prod_le _
    _ ≤ ∫⁻ t, (Icc (δ ^ 2 / M ^ 2) (δ ^ 2)).indicator
        (fun _ => ENNReal.ofReal (M ^ 4 / (2 * Real.pi * δ ^ 2))) t := lintegral_mono inner
    _ = ENNReal.ofReal (M ^ 4 / (2 * Real.pi * δ ^ 2)) *
        volume (Icc (δ ^ 2 / M ^ 2) (δ ^ 2)) := lintegral_indicator_const measurableSet_Icc _
    _ ≤ _ := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [show M ^ 4 / (2 * Real.pi * δ ^ 2) * (δ ^ 2 - δ ^ 2 / M ^ 2) =
            M ^ 4 / (2 * Real.pi) - M ^ 2 / (2 * Real.pi) by field_simp]
        have : 0 ≤ M ^ 2 / (2 * Real.pi) := by positivity
        linarith

/-- `‖hKer F U δ x‖² ≤ M⁴/(2π)`. -/
lemma norm_sq_hKer_le (h : ConfHyp F U) {M δ : ℝ} (hM1 : 1 ≤ M) (hδ : 0 < δ)
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) (x : ℂ) :
    ‖hKer F U δ x‖ ^ 2 ≤ M ^ 4 / (2 * Real.pi) := by
  rw [hKer, norm_sq_cutL2]
  have hae : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)),
      (pushL2 F U (phiKernelL2 δ 1 (F x)) : ℝ × ℂ → ℝ) q =
        pushFunOf F U (phiKernel δ 1 (F x)) q :=
    (coeFn_pushL2 h.1 h.2 h.3 h.4 _).trans
      (pushFunOf_congr h.1 h.2 h.3 h.4 (coeFn_phiKernelL2 δ 1 hδ (F x)))
  rw [lintegral_congr_ae (g := fun q => ‖pushFunOf F U (phiKernel δ 1 (F x)) q‖ₑ ^ (2 : ℝ))
    (ae_restrict_of_ae (hae.mono fun q hq => by simp only [hq]))]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc _ ≤ ∫⁻ q in (timeHigh δ)ᶜ, hBound F U M δ x q :=
        setLIntegral_mono' (measurableSet_timeHigh δ).compl
          fun q hq => enorm_pushFunOf_sq_le hF1 hM x hq
    _ ≤ ∫⁻ q, hBound F U M δ x q := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_hBound_le h hM1 hδ x

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `Var φ_H^{(δ)}(x) = π ‖hKer‖²` (Itô isometry). -/
lemma variance_phiH {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (δ : ℝ) (x : ℂ) :
    Var[phiH F U W δ x; P] = Real.pi * ‖hKer F U δ x‖ ^ 2 := by
  have := hW.isProbabilityMeasure
  have hm : MemLp (phiH F U W δ x) 2 P :=
    ((hW.hasLaw_single _).hasGaussianLaw.memLp_two).const_mul _
  rw [← covariance_self hm.aemeasurable]
  unfold phiH
  rw [covariance_const_mul_left, covariance_const_mul_right, hW.cov_eq,
    real_inner_self_eq_norm_sq, ← mul_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- **DDDF Lemma 6, third term** (l. 641–645): `Var φ_H^{(δ)}(x) ≤ M⁴/2` for all `δ > 0` and
all `x`, where `1 ≤ |F'| ≤ M` on `U` (here `M` is replaced by `max M 1`). -/
theorem l6_var_phiH_le (h : ConfHyp F U) {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {M : ℝ}
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) {δ : ℝ} (hδ : 0 < δ)
    (x : ℂ) : Var[phiH F U W δ x; P] ≤ max M 1 ^ 4 / 2 := by
  rw [variance_phiH hW]
  have hb := norm_sq_hKer_le h (le_max_right M 1) hδ hF1
    (fun y hy => (hM y hy).trans (le_max_left M 1)) x
  have hpi := Real.pi_pos
  calc Real.pi * ‖hKer F U δ x‖ ^ 2 ≤ Real.pi * (max M 1 ^ 4 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hb hpi.le
    _ = max M 1 ^ 4 / 2 := by field_simp

/-- **DDDF Lemma 6**, "`φ_H^{(δ)}` has uniformly bounded pointwise variance (in `δ` and
`x ∈ K`)" (l. 553, 641–645). -/
theorem l6_var_phiH (h : ConfHyp F U) {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {M : ℝ}
    (hF1 : ∀ y ∈ U, 1 ≤ ‖deriv F y‖) (hM : ∀ y ∈ U, ‖deriv F y‖ ≤ M) :
    ∃ C, ∀ δ, 0 < δ → ∀ x, Var[phiH F U W δ x; P] ≤ C :=
  ⟨max M 1 ^ 4 / 2, fun _ hδ x => l6_var_phiH_le h hW hF1 hM hδ x⟩

end DDDF
end LQGMetric
