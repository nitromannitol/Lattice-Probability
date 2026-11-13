/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.RemainderVar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.CircleKernel
import LatticeProb.Bonanno.HigherDimLFPP.Field.VarBounds

/-!
# Point variance of the circle remainder (packet P-X10, target T3, deterministic part)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2 (proof of Lemma A.1: "the remainder
still has bounded point variance"); planning audit HA5, Details D12, Claim 3.

Let `c = circVec κ ε z` (the kernel of the circle average `h_ε(z)`, all scales, normalized by the
unit circle) and `b = bandVec κ ε 1 x`, `x = cToR2 z` (the kernel of `H_{ε,1}(x)`).  Then
(`norm_circVec_sub_bandVec_sq_le`)

`‖c - b‖² ≤ C + 6 |z|`  for all `ε ∈ (0,1)` and `z ∈ ℂ`,

with `C` depending only on `κ`.  The paper splits the scales into `(0,ε]`, `(ε,1)` and `[1,∞)`; we
use instead the exact diagonal values and one cross term:

* `‖c‖² = gffCircleCov ε z ε z ≤ 2(|z| + 1) + log ε⁻¹` (Claim 1 and Newton's theorem,
  `gffCircleCov_self_le`);
* `‖b‖² = log ε⁻¹` (`norm_bandVec_sq`);
* `⟪c, b⟫ = ∫_{(ε,1)} (A(t) - B(t)) dt` (`inner_bandVecM_of_subset`,
  `scalePair_dirac_zero_right`), with
  `A(t) = ∫ C(t⁻¹(u - x))/t dσ_{ε,z}(u) ≥ (1 - L ε²/t²)/t` because `σ_{ε,z}` lives on the circle
  `|u - x| = ε` and `1 - C(v) ≤ L |v|²` (`integral_autoCorr_circ_ge`), so
  `∫_{(ε,1)} A ≥ log ε⁻¹ - L/2` (`setIntegral_lower_bound`); and
  `B(t) = ∫ C(t⁻¹(u - x))/t dσ_{1,0}(u)`, whose integral over `(ε,1)` is at most
  `∫ log⁺(2ρ/|u - x|) dσ_{1,0}(u) ≤ log⁺(2ρ) + 2(|z| + 1)` (Fubini, `C(v) = 0` for `|v| ≥ 2ρ`, and
  the logarithmic integrability of circles, `LQGDimension.Coupling.integral_abs_log_le`;
  `setIntegral_unit_le`).

Hence `‖c - b‖² = ‖c‖² - 2⟪c, b⟫ + ‖b‖² ≤ 6(|z| + 1) + L + 2 log⁺(2ρ)`.  No growth bound for circle
measures is needed.  The helper lemmas live in the namespace `HigherDimLFPP.TwoD`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace HigherDimLFPP

namespace TwoD

/-! ### Two general facts on band vectors -/

section General

variable {d : ℕ} {κ : Rd d → ℝ}

/-- **Nested scale sets**: for measurable `S ⊆ S' ⊆ (0, ∞)` and pairable pairs,
`⟪bandVecM κ S' μ ν, bandVecM κ S μ' ν'⟫ = ∫_S scalePair κ t μ ν μ' ν' dt`, the integrand being
integrable on `S`. -/
theorem inner_bandVecM_of_subset (hκ : IsLFPPKernel κ) {S S' : Set ℝ} (hS : MeasurableSet S)
    (hSS' : S ⊆ S') (hS'0 : S' ⊆ Ioi 0) {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (h : IsPairable κ S' μ ν)
    (h' : IsPairable κ S μ' ν') :
    IntegrableOn (fun t => scalePair κ t μ ν μ' ν') S ∧
      ⟪bandVecM κ S' μ ν, bandVecM κ S μ' ν'⟫ = ∫ t in S, scalePair κ t μ ν μ' ν' := by
  have hint : Integrable (fun p => (bandFun κ S' μ p - bandFun κ S' ν p) *
      (bandFun κ S μ' p - bandFun κ S ν' p)) (volume.prod volume) := h.integrable_mul h'
  have key : ∀ t, ∫ y, (bandFun κ S' μ (t, y) - bandFun κ S' ν (t, y)) *
      (bandFun κ S μ' (t, y) - bandFun κ S ν' (t, y)) =
        S.indicator (fun t => scalePair κ t μ ν μ' ν') t := by
    intro t
    by_cases ht : t ∈ S
    · simp only [indicator_of_mem ht, bandFun_sub_apply_of_mem _ _ ht,
        bandFun_sub_apply_of_mem _ _ (hSS' ht)]
      exact integral_scaleConv_sub_mul hκ (hS'0 (hSS' ht)) μ ν μ' ν'
    · simp only [indicator_of_notMem ht, bandFun_apply_of_notMem _ (p := (t, _)) ht, sub_self,
        mul_zero, integral_zero]
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hS]
    exact hint.integral_prod_left.congr (Eventually.of_forall key)
  · rw [inner_bandVecM_eq_integral h h',
      show (volume : Measure (ℝ × Rd d)) = volume.prod volume from rfl, integral_prod _ hint,
      ← integral_indicator hS]
    exact integral_congr_ae (Eventually.of_forall key)

/-- `u ↦ C(t⁻¹(u - x))/t` is continuous. -/
theorem continuous_autoCorr_div (hκ : IsLFPPKernel κ) (t : ℝ) (x : Rd d) :
    Continuous fun u : Rd d => autoCorr κ (t⁻¹ • (u - x)) / t :=
  ((continuous_autoCorr hκ).comp ((continuous_id.sub continuous_const).const_smul t⁻¹)).div_const t

/-- `|C(t⁻¹(u - x))/t| ≤ |t⁻¹|`. -/
theorem abs_autoCorr_div_le (hκ : IsLFPPKernel κ) (t : ℝ) (v : Rd d) :
    |autoCorr κ (t⁻¹ • v) / t| ≤ |t⁻¹| := by
  rw [abs_div, div_eq_mul_inv, abs_inv]
  calc |autoCorr κ (t⁻¹ • v)| * |t|⁻¹ ≤ 1 * |t|⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_autoCorr_le_one hκ _) (inv_nonneg.2 (abs_nonneg t))
    _ = |t|⁻¹ := one_mul _

theorem integrable_autoCorr_div_sub (hκ : IsLFPPKernel κ) (t : ℝ) (x : Rd d) (μ : Measure (Rd d))
    [IsFiniteMeasure μ] : Integrable (fun u => autoCorr κ (t⁻¹ • (u - x)) / t) μ :=
  Integrable.of_bound (continuous_autoCorr_div hκ t x).aestronglyMeasurable |t⁻¹|
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      exact abs_autoCorr_div_le hκ t _)

/-- **Point masses in the second pair**: `scalePair κ t μ ν δ_x 0 = ∫ C(t⁻¹(u - x))/t dμ(u) -
∫ C(t⁻¹(u - x))/t dν(u)`. -/
theorem scalePair_dirac_zero_right (hκ : IsLFPPKernel κ) (t : ℝ) (μ ν : Measure (Rd d))
    [SFinite μ] [SFinite ν] (x : Rd d) :
    scalePair κ t μ ν (Measure.dirac x) 0 =
      ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂μ - ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂ν := by
  have hc : Continuous fun p : Rd d × Rd d => autoCorr κ (t⁻¹ • (p.1 - p.2)) / t :=
    ((continuous_autoCorr hκ).comp ((continuous_fst.sub continuous_snd).const_smul t⁻¹)).div_const t
  have hm : Measurable fun u : Rd d => (u, x) := measurable_id.prodMk measurable_const
  simp only [scalePair, mixInt, Measure.prod_zero, integral_zero_measure, sub_zero, add_zero,
    Measure.prod_dirac]
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable,
    integral_map hm.aemeasurable hc.aestronglyMeasurable]

/-- `t ↦ ∫ C(t⁻¹(u - x))/t dμ(u)` is measurable. -/
theorem measurable_integral_autoCorr_div (hκ : IsLFPPKernel κ) (μ : Measure (Rd d)) [SFinite μ]
    (x : Rd d) : Measurable fun t : ℝ => ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂μ := by
  have hm : Measurable fun p : ℝ × Rd d => autoCorr κ (p.1⁻¹ • (p.2 - x)) / p.1 :=
    ((continuous_autoCorr hκ).measurable.comp
      ((measurable_fst.inv).smul (measurable_snd.sub measurable_const))).div measurable_fst
  exact (hm.stronglyMeasurable.integral_prod_right (ν := μ)).measurable

/-- On `(ε, 1)`, `t ↦ ∫ C(t⁻¹(u - x))/t dμ(u)` is integrable (it is bounded by `1/ε`). -/
theorem integrableOn_integral_autoCorr_div (hκ : IsLFPPKernel κ) (μ : Measure (Rd d))
    [IsProbabilityMeasure μ] (x : Rd d) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂μ) (Ioo ε 1) := by
  refine Measure.integrableOn_of_bounded (M := ε⁻¹) measure_Ioo_lt_top.ne
    (measurable_integral_autoCorr_div hκ μ x).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := hε.trans ht.1
  rw [Real.norm_eq_abs]
  calc |∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂μ|
      ≤ ∫ u, |autoCorr κ (t⁻¹ • (u - x)) / t| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _u, |t⁻¹| ∂μ :=
        integral_mono (integrable_autoCorr_div_sub hκ t x μ).abs (integrable_const _)
          fun u => abs_autoCorr_div_le hκ t _
    _ = t⁻¹ := by rw [integral_const, probReal_univ, one_smul, abs_of_pos (inv_pos.2 ht0)]
    _ ≤ ε⁻¹ := inv_anti₀ hε ht.1.le

end General

/-! ### The small circle: lower bound -/

variable {κ : Rd 2 → ℝ}

/-- On the circle `|u - x| = ε`: `∫ C(t⁻¹(u - x))/t dσ_{ε,z}(u) ≥ (1 - L ε²/t²)/t` whenever
`1 - C(v) ≤ L |v|²`. -/
theorem integral_autoCorr_circ_ge (hκ : IsLFPPKernel κ) {L : ℝ}
    (hL : ∀ v : Rd 2, 1 - autoCorr κ v ≤ L * ‖v‖ ^ 2) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t)
    (z : ℂ) :
    (1 - L * ε ^ 2 / t ^ 2) / t ≤ ∫ u, autoCorr κ (t⁻¹ • (u - cToR2 z)) / t ∂circMeasR z ε := by
  have hconst : ∫ _u, (1 - L * ε ^ 2 / t ^ 2) / t ∂circMeasR z ε = (1 - L * ε ^ 2 / t ^ 2) / t := by
    rw [integral_const, probReal_univ, one_smul]
  rw [← hconst]
  refine integral_mono_ae (integrable_const _) (integrable_autoCorr_div_sub hκ t _ _) ?_
  filter_upwards [ae_circMeasR z ε] with u hu
  rw [abs_of_pos hε] at hu
  have h1 := hL (t⁻¹ • (u - cToR2 z))
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), hu, mul_pow, inv_pow] at h1
  have h2 : 1 - L * ε ^ 2 / t ^ 2 ≤ autoCorr κ (t⁻¹ • (u - cToR2 z)) := by
    have e : L * ε ^ 2 / t ^ 2 = L * ((t ^ 2)⁻¹ * ε ^ 2) := by field_simp
    rw [e]
    linarith
  exact div_le_div_of_nonneg_right h2 ht.le

/-- `∫_{(ε,1)} (1 - L ε²/t²)/t dt ≥ log ε⁻¹ - L/2` for `0 < ε < 1`, `L ≥ 0`. -/
theorem setIntegral_lower_bound {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε < 1) :
    Real.log ε⁻¹ - L / 2 ≤ ∫ t in Ioo ε 1, (1 - L * ε ^ 2 / t ^ 2) / t := by
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioo ε 1) := by
    refine (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono ?_)).mono_set Ioo_subset_Icc_self
    intro t ht
    exact (hε.trans_le ht.1).ne'
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-3 : ℝ)) (Ioi ε) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hε
  have hpow' : IntegrableOn (fun t : ℝ => L * ε ^ 2 * t ^ (-3 : ℝ)) (Ioo ε 1) :=
    (hpow.mono_set Ioo_subset_Ioi_self).const_mul _
  have heq : EqOn (fun t : ℝ => (1 - L * ε ^ 2 / t ^ 2) / t)
      (fun t => t⁻¹ - L * ε ^ 2 * t ^ (-3 : ℝ)) (Ioo ε 1) := by
    intro t ht
    have ht0 : 0 < t := hε.trans ht.1
    have e3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only
    rw [e3]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo heq, integral_sub hinv hpow']
  have h1 : ∫ t in Ioo ε 1, t⁻¹ = Real.log ε⁻¹ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hε1.le,
      integral_inv_of_pos hε one_pos, one_div]
  have h2 : ∫ t in Ioo ε 1, L * ε ^ 2 * t ^ (-3 : ℝ) ≤ L / 2 := by
    have hnn : ∀ t ∈ Ioi ε, 0 ≤ L * ε ^ 2 * t ^ (-3 : ℝ) := fun t ht =>
      mul_nonneg (by positivity) (Real.rpow_nonneg (hε.le.trans (le_of_lt ht)) _)
    calc ∫ t in Ioo ε 1, L * ε ^ 2 * t ^ (-3 : ℝ)
        ≤ ∫ t in Ioi ε, L * ε ^ 2 * t ^ (-3 : ℝ) :=
          setIntegral_mono_set (hpow.const_mul _)
            ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn))
            (Eventually.of_forall Ioo_subset_Ioi_self)
      _ = L * ε ^ 2 * (-ε ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1)) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hε]
      _ = L / 2 := by
          have e : ε ^ ((-3 : ℝ) + 1) = (ε ^ 2)⁻¹ := by
            rw [show (-3 : ℝ) + 1 = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hε.le,
              Real.rpow_natCast]
          rw [e]
          field_simp
          ring
  rw [h1]
  linarith

/-! ### The unit circle: upper bound -/

/-- For `v ≠ 0`: `∫_{(ε,1)} C(t⁻¹ v)/t dt ≤ log⁺(2ρ/|v|)` (`C(w) = 0` for `|w| ≥ 2ρ`, `C ≤ 1`). -/
theorem setIntegral_autoCorr_div_le (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ε : ℝ} (hε : 0 < ε) {v : Rd 2} (hv : v ≠ 0) :
    ∫ t in Ioo ε 1, autoCorr κ (t⁻¹ • v) / t ≤ Real.posLog (2 * ρ / ‖v‖) := by
  set a : ℝ := ‖v‖ / (2 * ρ) with ha
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  have ha0 : 0 < a := by positivity
  set g : ℝ → ℝ := (Ioo a 1).indicator fun t => t⁻¹ with hg
  have hg_int : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Ioo]
    refine (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono ?_)).mono_set
      Ioo_subset_Icc_self
    intro t ht
    exact (ha0.trans_le ht.1).ne'
  have hg_nn : ∀ t, 0 ≤ g t := fun t => by
    rw [hg]
    by_cases ht : t ∈ Ioo a 1
    · rw [indicator_of_mem ht]
      exact inv_nonneg.2 (ha0.trans ht.1).le
    · rw [indicator_of_notMem ht]
  have hle : ∀ t ∈ Ioo ε 1, autoCorr κ (t⁻¹ • v) / t ≤ g t := by
    intro t ht
    have ht0 : 0 < t := hε.trans ht.1
    by_cases hta : a < t
    · rw [hg, indicator_of_mem (show t ∈ Ioo a 1 from ⟨hta, ht.2⟩), div_eq_mul_inv]
      calc autoCorr κ (t⁻¹ • v) * t⁻¹ ≤ 1 * t⁻¹ :=
            mul_le_mul_of_nonneg_right (autoCorr_le_one hκ _) (inv_nonneg.2 ht0.le)
        _ = t⁻¹ := one_mul _
    · have h2 : 2 * ρ ≤ ‖t⁻¹ • v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht0.le), inv_mul_eq_div,
          le_div_iff₀ ht0]
        rw [not_lt, ha, le_div_iff₀ (by positivity)] at hta
        linarith
      rw [autoCorr_eq_zero_of_two_mul_le hρ h2, zero_div]
      exact hg_nn t
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo ε 1)] fun t => autoCorr κ (t⁻¹ • v) / t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact div_nonneg (autoCorr_nonneg hκ _) (hε.trans ht.1).le
  have hle' : (fun t => autoCorr κ (t⁻¹ • v) / t) ≤ᵐ[volume.restrict (Ioo ε 1)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hle t ht
  calc ∫ t in Ioo ε 1, autoCorr κ (t⁻¹ • v) / t
      ≤ ∫ t in Ioo ε 1, g t := integral_mono_of_nonneg hnn hg_int.integrableOn hle'
    _ ≤ ∫ t, g t := setIntegral_le_integral hg_int (Eventually.of_forall hg_nn)
    _ = ∫ t in Ioo a 1, t⁻¹ := integral_indicator measurableSet_Ioo
    _ ≤ Real.posLog (2 * ρ / ‖v‖) := by
        rcases lt_or_ge a 1 with ha1 | ha1
        · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha1.le,
            integral_inv_of_pos ha0 one_pos, Real.posLog_apply, one_div, ha, inv_div]
          exact le_max_right _ _
        · rw [Ioo_eq_empty (not_lt.2 ha1), Measure.restrict_empty, integral_zero_measure]
          exact Real.posLog_nonneg

/-- `log⁺(2ρ/r) ≤ log⁺(2ρ) + |log r|`. -/
theorem posLog_div_le (ρ r : ℝ) :
    Real.posLog (2 * ρ / r) ≤ Real.posLog (2 * ρ) + |Real.log r| := by
  calc Real.posLog (2 * ρ / r) = Real.posLog (2 * ρ * r⁻¹) := by rw [div_eq_mul_inv]
    _ ≤ Real.posLog (2 * ρ) + Real.posLog r⁻¹ := Real.posLog_mul
    _ ≤ Real.posLog (2 * ρ) + |Real.log r| := by
        gcongr
        rw [Real.posLog_apply, Real.log_inv]
        exact max_le (abs_nonneg _) (neg_le_abs _)

/-- `∫ |log |u - x|| dσ_{1,0}(u) ≤ 2(|z| + 1)` for `x = cToR2 z`. -/
theorem integral_abs_log_unit_le (z : ℂ) :
    ∫ u, |Real.log ‖u - cToR2 z‖| ∂circMeasR 0 1 ≤ 2 * (‖z‖ + 1) := by
  rw [circMeasR_eq_map_equiv, integral_map_equiv]
  have e : (fun y : ℂ => |Real.log ‖cToR2Meas y - cToR2 z‖|) =
      fun y => |Real.log ‖z - y‖| := by
    funext y
    rw [coe_cToR2Meas, norm_cToR2_sub, norm_sub_rev]
  rw [e]
  have h := LQGDimension.Coupling.integral_abs_log_le z 0 one_pos
  simpa using h

theorem integrable_abs_log_unit (z : ℂ) :
    Integrable (fun u => |Real.log ‖u - cToR2 z‖|) (circMeasR 0 1) := by
  rw [circMeasR_eq_map_equiv, integrable_map_equiv]
  refine (LQGDimension.Coupling.integrable_log_norm_sub_circ z 0 1).abs.congr
    (Eventually.of_forall fun y => ?_)
  show |Real.log ‖z - y‖| = |Real.log ‖cToR2 y - cToR2 z‖|
  rw [norm_cToR2_sub, norm_sub_rev]

/-- **The unit-circle part**: `∫_{(ε,1)} ∫ C(t⁻¹(u - x))/t dσ_{1,0}(u) dt ≤ log⁺(2ρ) + 2(|z| + 1)`
for `x = cToR2 z`. -/
theorem setIntegral_unit_le (hκ : IsLFPPKernel κ) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    ∫ t in Ioo ε 1, ∫ u, autoCorr κ (t⁻¹ • (u - cToR2 z)) / t ∂circMeasR 0 1 ≤
      Real.posLog (2 * ρ) + 2 * (‖z‖ + 1) := by
  set x := cToR2 z with hx
  set f : ℝ → Rd 2 → ℝ := fun t u => autoCorr κ (t⁻¹ • (u - x)) / t with hf
  have hfm : Measurable (Function.uncurry f) :=
    ((continuous_autoCorr hκ).measurable.comp
      ((measurable_fst.inv).smul (measurable_snd.sub measurable_const))).div measurable_fst
  -- Fubini
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioo ε 1)).prod (circMeasR 0 1)) := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ε⁻¹ ?_
    have hae : ∀ᵐ p ∂((volume.restrict (Ioo ε 1)).prod (circMeasR 0 1)), p.1 ∈ Ioo ε 1 :=
      (measurePreserving_fst.quasiMeasurePreserving).ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [hae] with p hp
    have ht0 : 0 < p.1 := hε.trans hp.1
    rw [Real.norm_eq_abs]
    refine (abs_autoCorr_div_le hκ p.1 _).trans ?_
    rw [abs_of_pos (inv_pos.2 ht0)]
    exact inv_anti₀ hε hp.1.le
  rw [integral_integral_swap hint]
  -- the inner integral, for a.e. `u`
  have hnn : ∀ u, 0 ≤ ∫ t in Ioo ε 1, f t u := fun u =>
    setIntegral_nonneg measurableSet_Ioo fun t ht =>
      div_nonneg (autoCorr_nonneg hκ _) (hε.trans ht.1).le
  have hne : ∀ᵐ u ∂circMeasR 0 1, u ≠ x := by
    have := nullSingletonClass_circMeasR 0 one_ne_zero
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton x
  have hle : ∀ᵐ u ∂circMeasR 0 1, ∫ t in Ioo ε 1, f t u ≤
      Real.posLog (2 * ρ) + |Real.log ‖u - x‖| := by
    filter_upwards [hne] with u hu
    have hv : u - x ≠ 0 := sub_ne_zero.2 hu
    exact (setIntegral_autoCorr_div_le hκ hρ0 hρ hε hv).trans
      (posLog_div_le ρ ‖u - x‖)
  calc ∫ u, (∫ t in Ioo ε 1, f t u) ∂circMeasR 0 1
      ≤ ∫ u, (Real.posLog (2 * ρ) + |Real.log ‖u - x‖|) ∂circMeasR 0 1 :=
        integral_mono_of_nonneg (Eventually.of_forall hnn)
          ((integrable_const _).add (integrable_abs_log_unit z)) hle
    _ = Real.posLog (2 * ρ) + ∫ u, |Real.log ‖u - x‖| ∂circMeasR 0 1 := by
        rw [integral_add (integrable_const _) (integrable_abs_log_unit z), integral_const,
          probReal_univ, one_smul]
    _ ≤ Real.posLog (2 * ρ) + 2 * (‖z‖ + 1) := by
        have := integral_abs_log_unit_le z
        linarith

/-! ### The diagonal of the circle covariance -/

/-- `gffCircleCov ε z ε z ≤ 2(|z| + 1) + log ε⁻¹` for `0 < ε ≤ 1`. -/
theorem gffCircleCov_self_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : ℂ) :
    LQGDimension.gffCircleCov ε z ε z ≤ 2 * (‖z‖ + 1) + Real.log ε⁻¹ := by
  rw [LQGDimension.Osc37.gffCircleCov_formula hε, LQGDimension.Osc37.aAvg_self hε, Real.log_inv]
  have hβ : LQGDimension.Osc37.betaAvg ε z ≤ ‖z‖ + 1 := by
    apply Real.circleAverage_mono_on_of_le_circle
      (LQGDimension.Osc37.circleIntegrable_logMaxOne _ _)
    intro y hy
    rw [mem_sphere_iff_norm, abs_of_pos hε] at hy
    have hy' : ‖y‖ ≤ ‖z‖ + 1 := by
      calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by rw [hy]; linarith
    have hpos : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    calc Real.log (max ‖y‖ 1) ≤ max ‖y‖ 1 - 1 := Real.log_le_sub_one_of_pos hpos
      _ ≤ ‖z‖ + 1 := by
          have := norm_nonneg z
          rcases le_total ‖y‖ 1 with h | h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
  linarith

end TwoD

open TwoD

/-! ### The point variance -/

variable {κ : Rd 2 → ℝ}

/-- **Point variance of the circle remainder** (HA5 D12, Claim 3, first step): there is `C`
(depending only on `κ`) with `‖circVec κ ε z - bandVec κ ε 1 (cToR2 z)‖² ≤ C + 6 |z|` for every
`ε ∈ (0,1)` and every `z ∈ ℂ`. -/
theorem norm_circVec_sub_bandVec_sq_le (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ z : ℂ,
      ‖circVec κ ε z - bandVec κ ε 1 (cToR2 z)‖ ^ 2 ≤ C + 6 * ‖z‖ := by
  obtain ⟨L, hL0, hL⟩ := exists_one_sub_autoCorr_le hκ
  obtain ⟨ρ, hρ0, hρ⟩ := hκ.exists_radius
  refine ⟨6 + L + 2 * Real.posLog (2 * ρ), fun ε hε z => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  set x := cToR2 z with hx
  set A : ℝ → ℝ := fun t => ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂circMeasR z ε with hA
  set B : ℝ → ℝ := fun t => ∫ u, autoCorr κ (t⁻¹ • (u - x)) / t ∂circMeasR 0 1 with hB
  have hAi : IntegrableOn A (Ioo ε 1) := integrableOn_integral_autoCorr_div hκ _ x hε0
  have hBi : IntegrableOn B (Ioo ε 1) := integrableOn_integral_autoCorr_div hκ _ x hε0
  -- the cross term
  have hcross : ⟪circVec κ ε z, bandVec κ ε 1 x⟫ = ∫ t in Ioo ε 1, (A t - B t) := by
    rw [circVec, ← bandVecM_dirac_zero]
    obtain ⟨-, heq⟩ := inner_bandVecM_of_subset hκ measurableSet_Ioo
      (Ioo_subset_Ioi_self.trans (Ioi_subset_Ioi hε0.le)) subset_rfl (isPairable_circ hκ hε0 z)
      (isPairable_dirac_zero hκ hε0 1 x)
    rw [heq]
    refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
    exact scalePair_dirac_zero_right hκ t _ _ x
  have hAlow : Real.log ε⁻¹ - L / 2 ≤ ∫ t in Ioo ε 1, A t := by
    refine (setIntegral_lower_bound hL0 hε0 hε1).trans ?_
    refine setIntegral_mono_on ?_ hAi measurableSet_Ioo fun t ht =>
      integral_autoCorr_circ_ge hκ (fun v => (hL v).2) hε0 (hε0.trans ht.1) z
    -- integrability of the lower function
    have heq : EqOn (fun t : ℝ => (1 - L * ε ^ 2 / t ^ 2) / t)
        (fun t => t⁻¹ - L * ε ^ 2 * t ^ (-3 : ℝ)) (Ioo ε 1) := by
      intro t ht
      have ht0 : 0 < t := hε0.trans ht.1
      have e3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
        rw [Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      simp only
      rw [e3]
      field_simp
    refine IntegrableOn.congr_fun ?_ heq.symm measurableSet_Ioo
    refine IntegrableOn.sub ?_ ?_
    · refine (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono ?_)).mono_set
        Ioo_subset_Icc_self
      intro t ht
      exact (hε0.trans_le ht.1).ne'
    · exact ((integrableOn_Ioi_rpow_of_lt (by norm_num) hε0).mono_set
        Ioo_subset_Ioi_self).const_mul _
  have hBup : ∫ t in Ioo ε 1, B t ≤ Real.posLog (2 * ρ) + 2 * (‖z‖ + 1) :=
    setIntegral_unit_le hκ hρ0 hρ hε0 z
  have hcb : Real.log ε⁻¹ - L / 2 - (Real.posLog (2 * ρ) + 2 * (‖z‖ + 1)) ≤
      ⟪circVec κ ε z, bandVec κ ε 1 x⟫ := by
    rw [hcross, integral_sub hAi hBi]
    linarith
  have hc := norm_circVec_sq hκ hε0 z
  have hcle := gffCircleCov_self_le hε0 hε1.le z
  have hb : ‖bandVec κ ε 1 x‖ ^ 2 = Real.log ε⁻¹ := by
    rw [norm_bandVec_sq hκ hε0 hε1.le, one_div]
  rw [norm_sub_sq_real, hc, hb]
  linarith

end HigherDimLFPP
