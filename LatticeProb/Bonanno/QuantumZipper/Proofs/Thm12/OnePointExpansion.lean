/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.OnePointExpansion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseODE
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Deterministic short-time expansion of the reverse Loewner flow at one point

Task GEN-DET-1 (part of the proof of Theorem 1.2, `PLAN.md` §5 M2).

Setting: `W : ℝ → ℝ` continuous, `z` with `δ ≤ z.im` (`δ > 0`) and `‖z‖ ≤ R`, `0 ≤ s ≤ 1`.
Write `f_r := revMap W r z`, `a_s := ∫_0^s 2/f_r`, `m_s := ∫_0^s |W_r|`,
`L_s := ∫_0^s 2/f_r²`. We prove, with explicit constants `C₁ δ`, `C₂ δ`, `C₃ δ R`,
`C₄ κ δ R`:

1. `norm_revMap_sub_self_le`: `‖f_r - z‖ ≤ |W r| + 2 r / δ`.
2. `revMap_eq_sub_drift`, `norm_drift_sub_le`: `f_s = z - W s - a_s` and
   `‖a_s - 2 s / z‖ ≤ C₁ (m_s + s²)`.
3. `norm_logDeriv_sub_le`: `‖L_s - 2 s / z²‖ ≤ C₂ (m_s + s²)`.
4. `log_norm_sub_taylor_le`: global cubic remainder for `log ‖f‖ - log ‖z‖`.
5. `drift_cancel`, `oneHFun_expansion`: the drift-free expansion of `𝔥_s(z)`.
-/

noncomputable section

open Complex

namespace QuantumZipper

namespace OnePointExpansion

/-! ### Constants -/

/-- Constant of item 2. -/
def C₁ (δ : ℝ) : ℝ := 2 / δ ^ 2 + 2 / δ ^ 3

/-- Constant of item 3. -/
def C₂ (δ : ℝ) : ℝ := 4 / δ ^ 3 + 4 / δ ^ 4

/-- Constant of item 4 (cubic remainder of the log expansion). -/
def C₃ (δ R : ℝ) : ℝ := 9 + 8 * Real.log (R / δ)

/-- Constant of item 5 (depends on `κ` too, through `√κ` and `Qc (√κ)`). -/
def C₄ (κ δ R : ℝ) : ℝ :=
  2 / √κ * C₁ δ / δ + 4 / δ ^ 3 + 4 / (√κ * δ ^ 4) + Qc (√κ) * C₂ δ
    + 8 / √κ * C₃ δ R * (√κ ^ 3 / δ ^ 3) + 8 / √κ * C₃ δ R * (8 / δ ^ 6)

/-- The quantity `𝔥_s(z) = (2/√κ) log ‖f_s(z)‖ + Qc(√κ) Re L_s - (2/√κ) log ‖z‖`. -/
def oneHFun (κ : ℝ) (W : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  2 / √κ * Real.log ‖revMap W s z‖ + Qc (√κ) * (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2).re
    - 2 / √κ * Real.log ‖z‖

/-! ### Elementary facts about the flow -/

theorem le_norm_revMap (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hzδ : δ ≤ z.im) {r : ℝ} (hr : 0 ≤ r) : δ ≤ ‖revMap W r z‖ :=
  hzδ.trans ((im_le_im_revMap W hW z (hδ.trans_le hzδ) hr).trans (Complex.im_le_norm _))

/-- Item 1. -/
theorem norm_revMap_sub_self_le (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hzδ : δ ≤ z.im) {r : ℝ} (hr : 0 ≤ r) :
    ‖revMap W r z - z‖ ≤ |W r| + 2 * r / δ := by
  have hz : 0 < z.im := hδ.trans_le hzδ
  have h1 := norm_revMap_sub_le W hW z hz hr
  have h2 : 2 * r / z.im ≤ 2 * r / δ := div_le_div_of_nonneg_left (by linarith) hδ hzδ
  calc ‖revMap W r z - z‖ = ‖(revMap W r z - (z - (W r : ℂ))) + (-(W r : ℂ))‖ := by
        congr 1; ring
    _ ≤ ‖revMap W r z - (z - (W r : ℂ))‖ + ‖(-(W r : ℂ))‖ := norm_add_le _ _
    _ ≤ 2 * r / δ + |W r| := by
        rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]; linarith
    _ = _ := by ring

theorem continuousOn_revMap_and_eq (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {s : ℝ} (hs : 0 ≤ s) :
    ContinuousOn (fun r => revMap W r z) (Set.Icc 0 s) ∧
      revMap W s z = z - W s - ∫ r in (0 : ℝ)..s, 2 / revMap W r z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz s hs
  have heq : Set.EqOn (fun r => revMap W r z) u (Set.Icc 0 s) := fun r hr =>
    revMap_eq W hW z hr.1 hr.2 hu
  refine ⟨hu.1.congr heq, ?_⟩
  have hs' : revMap W s z = u s := heq ⟨hs, le_rfl⟩
  rw [hs', (hu.2 s ⟨hs, le_rfl⟩).2]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le hs] at hr
  have h' : revMap W r z = u r := heq hr
  simp only [h']

/-- Item 2, first half. -/
theorem revMap_eq_sub_drift (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {s : ℝ} (hs : 0 ≤ s) :
    revMap W s z = z - W s - ∫ r in (0 : ℝ)..s, 2 / revMap W r z :=
  (continuousOn_revMap_and_eq W hW hz hs).2

/-- Integrating a pointwise bound of the form `K (|W r| + 2 r / δ)`. -/
theorem norm_integral_le_drift_bound (W : ℝ → ℝ) (hW : Continuous W) {δ K s : ℝ}
    (hs : 0 ≤ s) {g : ℝ → ℂ}
    (hg : ∀ r ∈ Set.Icc 0 s, ‖g r‖ ≤ K * (|W r| + 2 * r / δ)) :
    ‖∫ r in (0 : ℝ)..s, g r‖ ≤ K * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2 / δ) := by
  have hint1 : IntervalIntegrable (fun r => |W r|) MeasureTheory.volume 0 s :=
    (continuous_abs.comp hW).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun r : ℝ => 2 * r / δ) MeasureTheory.volume 0 s :=
    (by fun_prop : Continuous fun r : ℝ => 2 * r / δ).intervalIntegrable _ _
  have hid : (∫ r in (0 : ℝ)..s, 2 * r / δ) = s ^ 2 / δ := by
    have : (fun r : ℝ => 2 * r / δ) = fun r => (2 / δ) * r := by funext r; ring
    rw [this, intervalIntegral.integral_const_mul, integral_id]; ring
  calc ‖∫ r in (0 : ℝ)..s, g r‖ ≤ ∫ r in (0 : ℝ)..s, K * (|W r| + 2 * r / δ) :=
        intervalIntegral.norm_integral_le_of_norm_le hs
          (Filter.Eventually.of_forall fun r hr => hg r (Set.Ioc_subset_Icc_self hr))
          ((hint1.add hint2).const_mul K)
    _ = K * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2 / δ) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hint1 hint2, hid]

theorem norm_inv_sub_inv_le {δ : ℝ} (hδ : 0 < δ) {f z : ℂ} (hf : δ ≤ ‖f‖) (hz : δ ≤ ‖z‖) :
    ‖1 / f - 1 / z‖ ≤ ‖f - z‖ / δ ^ 2 := by
  have hf0 : f ≠ 0 := norm_pos_iff.mp (hδ.trans_le hf)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hδ.trans_le hz)
  rw [div_sub_div _ _ hf0 hz0, norm_div, norm_mul, one_mul, mul_one, ← norm_neg (z - f), neg_sub]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    (by rw [sq]; exact mul_le_mul hf hz hδ.le (norm_nonneg _))

theorem norm_one_div_le {δ : ℝ} (hδ : 0 < δ) {f : ℂ} (hf : δ ≤ ‖f‖) : ‖1 / f‖ ≤ 1 / δ := by
  rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hδ hf

theorem absorb_aux {δ c m s : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hm : 0 ≤ m) :
    c * (m + s ^ 2 / δ) ≤ (c + c / δ) * (m + s ^ 2) := by
  have h : (c + c / δ) * (m + s ^ 2) - c * (m + s ^ 2 / δ) = c * s ^ 2 + c / δ * m := by
    field_simp; ring
  have : 0 ≤ c * s ^ 2 + c / δ * m := by positivity
  linarith

theorem integral_abs_nonneg (W : ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ ∫ r in (0 : ℝ)..s, |W r| :=
  intervalIntegral.integral_nonneg hs (fun _ _ => abs_nonneg _)

/-- `‖a_s‖ ≤ 2 s / δ`. -/
theorem norm_drift_le (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} {δ s : ℝ} (hδ : 0 < δ)
    (hzδ : δ ≤ z.im) (hs : 0 ≤ s) :
    ‖∫ r in (0 : ℝ)..s, 2 / revMap W r z‖ ≤ 2 * s / δ := by
  have hb : ∀ r ∈ Set.uIoc (0 : ℝ) s, ‖2 / revMap W r z‖ ≤ 2 / δ := by
    intro r hr
    rw [Set.uIoc_of_le hs] at hr
    have h1 := norm_one_div_le hδ (le_norm_revMap W hW hδ hzδ hr.1.le)
    rw [show (2 : ℂ) / revMap W r z = 2 * (1 / revMap W r z) by ring, norm_mul,
      show ‖(2 : ℂ)‖ = 2 by norm_num]
    have : 2 / δ = 2 * (1 / δ) := by ring
    linarith
  calc _ ≤ 2 / δ * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = 2 * s / δ := by rw [sub_zero, abs_of_nonneg hs]; ring

/-- Item 2, second half. -/
theorem norm_drift_sub_le (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} {δ s : ℝ} (hδ : 0 < δ)
    (hzδ : δ ≤ z.im) (hs : 0 ≤ s) :
    ‖(∫ r in (0 : ℝ)..s, 2 / revMap W r z) - 2 * s / z‖
      ≤ C₁ δ * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2) := by
  have hz : 0 < z.im := hδ.trans_le hzδ
  have hzn : δ ≤ ‖z‖ := hzδ.trans (Complex.im_le_norm z)
  have hc := (continuousOn_revMap_and_eq W hW hz hs).1
  have hne : ∀ r ∈ Set.Icc (0 : ℝ) s, revMap W r z ≠ 0 := fun r hr =>
    norm_pos_iff.mp (hδ.trans_le (le_norm_revMap W hW hδ hzδ hr.1))
  have hint : IntervalIntegrable (fun r => 2 / revMap W r z) MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs]
    exact continuousOn_const.div hc hne
  have hconst : (2 : ℂ) * s / z = ∫ _ in (0 : ℝ)..s, 2 / z := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]; ring
  rw [hconst, ← intervalIntegral.integral_sub hint intervalIntegrable_const]
  have hC : C₁ δ = 2 / δ ^ 2 + 2 / δ ^ 2 / δ := by
    unfold C₁; rw [div_div, ← pow_succ]
  refine (norm_integral_le_drift_bound W hW (δ := δ) (K := 2 / δ ^ 2) hs ?_).trans ?_
  · intro r hr
    have hfr := le_norm_revMap W hW hδ hzδ hr.1
    have h1 := norm_inv_sub_inv_le hδ hfr hzn
    have h2 := norm_revMap_sub_self_le W hW hδ hzδ hr.1
    rw [show (2 : ℂ) / revMap W r z - 2 / z = 2 * (1 / revMap W r z - 1 / z) by ring,
      norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc 2 * ‖1 / revMap W r z - 1 / z‖ ≤ 2 * (‖revMap W r z - z‖ / δ ^ 2) := by
          linarith
      _ ≤ 2 * ((|W r| + 2 * r / δ) / δ ^ 2) := by gcongr
      _ = 2 / δ ^ 2 * (|W r| + 2 * r / δ) := by ring
  · rw [hC]; exact absorb_aux hδ (by positivity) (integral_abs_nonneg W hs)

/-- Item 3. -/
theorem norm_logDeriv_sub_le (W : ℝ → ℝ) (hW : Continuous W) {z : ℂ} {δ s : ℝ} (hδ : 0 < δ)
    (hzδ : δ ≤ z.im) (hs : 0 ≤ s) :
    ‖(∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2) - 2 * s / z ^ 2‖
      ≤ C₂ δ * ((∫ r in (0 : ℝ)..s, |W r|) + s ^ 2) := by
  have hz : 0 < z.im := hδ.trans_le hzδ
  have hzn : δ ≤ ‖z‖ := hzδ.trans (Complex.im_le_norm z)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hδ.trans_le hzn)
  have hc := (continuousOn_revMap_and_eq W hW hz hs).1
  have hne : ∀ r ∈ Set.Icc (0 : ℝ) s, revMap W r z ^ 2 ≠ 0 := fun r hr =>
    pow_ne_zero 2 (norm_pos_iff.mp (hδ.trans_le (le_norm_revMap W hW hδ hzδ hr.1)))
  have hint : IntervalIntegrable (fun r => 2 / revMap W r z ^ 2) MeasureTheory.volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs]
    exact continuousOn_const.div (hc.pow 2) hne
  have hconst : (2 : ℂ) * s / z ^ 2 = ∫ _ in (0 : ℝ)..s, 2 / z ^ 2 := by
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]; ring
  rw [hconst, ← intervalIntegral.integral_sub hint intervalIntegrable_const]
  have hC : C₂ δ = 4 / δ ^ 3 + 4 / δ ^ 3 / δ := by
    unfold C₂; rw [div_div, ← pow_succ]
  refine (norm_integral_le_drift_bound W hW (δ := δ) (K := 4 / δ ^ 3) hs ?_).trans ?_
  · intro r hr
    have hfr := le_norm_revMap W hW hδ hzδ hr.1
    have hf0 : revMap W r z ≠ 0 := norm_pos_iff.mp (hδ.trans_le hfr)
    have h1 := norm_inv_sub_inv_le hδ hfr hzn
    have h2 := norm_revMap_sub_self_le W hW hδ hzδ hr.1
    have h3 : ‖1 / revMap W r z + 1 / z‖ ≤ 2 / δ := by
      have := norm_add_le (1 / revMap W r z) (1 / z)
      have := norm_one_div_le hδ hfr
      have := norm_one_div_le hδ hzn
      have : 1 / δ + 1 / δ = 2 / δ := by ring
      linarith
    rw [show (2 : ℂ) / revMap W r z ^ 2 - 2 / z ^ 2
        = 2 * ((1 / revMap W r z - 1 / z) * (1 / revMap W r z + 1 / z)) by
          field_simp; ring,
      norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    calc 2 * (‖1 / revMap W r z - 1 / z‖ * ‖1 / revMap W r z + 1 / z‖)
        ≤ 2 * ((‖revMap W r z - z‖ / δ ^ 2) * (2 / δ)) := by
          gcongr
      _ ≤ 2 * (((|W r| + 2 * r / δ) / δ ^ 2) * (2 / δ)) := by gcongr
      _ = 4 / δ ^ 3 * (|W r| + 2 * r / δ) := by field_simp; ring
  · rw [hC]; exact absorb_aux hδ (by positivity) (integral_abs_nonneg W hs)

/-! ### Item 4: the log expansion with a global cubic remainder -/

theorem logTaylor_three (u : ℂ) : Complex.logTaylor (2 + 1) u = u - u ^ 2 / 2 := by
  simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

/-- Item 4. -/
theorem log_norm_sub_taylor_le {δ R : ℝ} (hδ : 0 < δ) {z f : ℂ} (hzδ : δ ≤ ‖z‖)
    (hzR : ‖z‖ ≤ R) (hf : δ ≤ ‖f‖) :
    |Real.log ‖f‖ - Real.log ‖z‖ - ((f - z) / z - ((f - z) / z) ^ 2 / 2).re|
      ≤ C₃ δ R * ‖(f - z) / z‖ ^ 3 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hδ.trans_le hzδ)
  have hf0 : f ≠ 0 := norm_pos_iff.mp (hδ.trans_le hf)
  have hfu' : f = z * (1 + (f - z) / z) := by field_simp; ring
  generalize hu : (f - z) / z = u at hfu' ⊢
  have h1u : 1 + u ≠ 0 := by
    rintro h; rw [h, mul_zero] at hfu'; exact hf0 hfu'
  have hD : Real.log ‖f‖ - Real.log ‖z‖ = (Complex.log (1 + u)).re := by
    rw [hfu', norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hz0) (norm_ne_zero_iff.mpr h1u),
      Complex.log_re]
    ring
  have hRδ : 1 ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlog0 : 0 ≤ Real.log (R / δ) := Real.log_nonneg hRδ
  have hC3 : 1 ≤ C₃ δ R := by unfold C₃; linarith
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hu3 : 0 ≤ ‖u‖ ^ 3 := pow_nonneg hu0 3
  rcases le_or_gt ‖u‖ (1 / 2) with hsmall | hlarge
  · rw [hD]
    have ht := Complex.norm_log_sub_logTaylor_le 2 (show ‖u‖ < 1 by linarith)
    rw [logTaylor_three] at ht
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
    have ht' : ‖Complex.log (1 + u) - (u - u ^ 2 / 2)‖ ≤ ‖u‖ ^ 3 * 2 / 3 := by
      calc _ ≤ _ := ht
        _ = ‖u‖ ^ 3 * (1 - ‖u‖)⁻¹ / 3 := by norm_num
        _ ≤ ‖u‖ ^ 3 * 2 / 3 := by gcongr
    calc |(Complex.log (1 + u)).re - (u - u ^ 2 / 2).re|
        = |(Complex.log (1 + u) - (u - u ^ 2 / 2)).re| := by
          congr 1
      _ ≤ ‖Complex.log (1 + u) - (u - u ^ 2 / 2)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖u‖ ^ 3 * 2 / 3 := ht'
      _ ≤ C₃ δ R * ‖u‖ ^ 3 := by nlinarith
  · have hupper : Real.log ‖f‖ - Real.log ‖z‖ ≤ ‖u‖ := by
      rw [hD, Complex.log_re]
      have hpos : 0 < ‖1 + u‖ := norm_pos_iff.mpr h1u
      have := Real.log_le_sub_one_of_pos hpos
      have h2 : ‖1 + u‖ ≤ 1 + ‖u‖ := by simpa using norm_add_le (1 : ℂ) u
      linarith
    have hlower : -Real.log (R / δ) ≤ Real.log ‖f‖ - Real.log ‖z‖ := by
      rw [Real.log_div (by linarith) hδ.ne']
      have h1 : Real.log δ ≤ Real.log ‖f‖ := Real.log_le_log hδ hf
      have h2 : Real.log ‖z‖ ≤ Real.log R := Real.log_le_log (hδ.trans_le hzδ) hzR
      linarith
    have hv : |(u - u ^ 2 / 2).re| ≤ ‖u‖ + ‖u‖ ^ 2 / 2 := by
      refine (Complex.abs_re_le_norm _).trans ((norm_sub_le _ _).trans ?_)
      rw [norm_div, norm_pow]; norm_num
    have hDabs : |Real.log ‖f‖ - Real.log ‖z‖| ≤ ‖u‖ + Real.log (R / δ) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have htri := abs_sub (Real.log ‖f‖ - Real.log ‖z‖) ((u - u ^ 2 / 2).re)
    set t := ‖u‖
    have ht2 : 1 / 4 < t ^ 2 := by nlinarith
    have ht3 : 1 / 8 < t ^ 3 := by nlinarith
    have h2t : 2 * t ≤ 8 * t ^ 3 := by nlinarith
    have htt : t ^ 2 / 2 ≤ t ^ 3 := by nlinarith
    have hl : Real.log (R / δ) ≤ 8 * Real.log (R / δ) * t ^ 3 := by nlinarith
    unfold C₃
    nlinarith

/-! ### Item 5: the drift-free expansion -/

/-- Item 5. -/
theorem oneHFun_expansion {κ : ℝ} (hκ : 0 < κ) {W B : ℝ → ℝ} (hW : Continuous W)
    (hWB : ∀ r, W r = √κ * B r) {z : ℂ} {δ R s : ℝ} (hδ : 0 < δ) (hzδ : δ ≤ z.im)
    (hzR : ‖z‖ ≤ R) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |oneHFun κ W s z - (-2 * (1 / z).re * B s - √κ * (1 / z ^ 2).re * (B s ^ 2 - s))|
      ≤ C₄ κ δ R * (|B s| ^ 3 + s * |B s| + (∫ r in (0 : ℝ)..s, |W r|) + s ^ 2) := by
  have hz : 0 < z.im := hδ.trans_le hzδ
  have hzn : δ ≤ ‖z‖ := hzδ.trans (Complex.im_le_norm z)
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hδ.trans_le hzn)
  have hfn : δ ≤ ‖revMap W s z‖ := le_norm_revMap W hW hδ hzδ hs
  have hfeq := revMap_eq_sub_drift W hW hz hs
  have he1 := norm_drift_sub_le W hW hδ hzδ hs
  have he2 := norm_logDeriv_sub_le W hW hδ hzδ hs
  have hlog := log_norm_sub_taylor_le hδ hzn hzR hfn
  have hdisp := norm_revMap_sub_self_le W hW hδ hzδ hs
  have ha := norm_drift_le W hW hδ hzδ hs
  have hm := integral_abs_nonneg W hs
  have hγ : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hC1 : 0 ≤ C₁ δ := by unfold C₁; positivity
  have hC2 : 0 ≤ C₂ δ := by unfold C₂; positivity
  have hC3 : 0 ≤ C₃ δ R := by
    have hRδ : 1 ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith
    have := Real.log_nonneg hRδ
    unfold C₃; linarith
  unfold oneHFun C₄
  generalize (∫ r in (0 : ℝ)..s, |W r|) = m at hm he1 he2 ⊢
  generalize (∫ r in (0 : ℝ)..s, 2 / revMap W r z) = a at hfeq he1 ha
  generalize (∫ r in (0 : ℝ)..s, 2 / revMap W r z ^ 2) = L at he2 ⊢
  generalize revMap W s z = f at hfeq hfn hlog hdisp ⊢
  have hWs := hWB s
  generalize W s = w at hfeq hdisp hWs
  have hQc : Qc (√κ) = 2 / √κ + √κ / 2 := rfl
  generalize √κ = γ at hγ hWs hQc ⊢
  subst hWs
  generalize B s = b at *
  have hQc0 : 0 ≤ Qc γ := by rw [hQc]; positivity
  -- the remainders
  obtain ⟨e₁, he₁⟩ : ∃ e : ℂ, e = a - 2 * s / z := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : ℂ, e = L - 2 * s / z ^ 2 := ⟨_, rfl⟩
  rw [← he₁] at he1
  rw [← he₂] at he2
  obtain ⟨Rc, hRc⟩ : ∃ Rc : ℂ, Rc = ((2 / γ : ℝ) : ℂ) * (-(e₁ / z))
      + ((-1 / γ : ℝ) : ℂ) * ((2 * ((γ * b : ℝ) : ℂ) * a + a ^ 2) / z ^ 2)
      + ((Qc γ : ℝ) : ℂ) * e₂ := ⟨_, rfl⟩
  have key : ((2 / γ : ℝ) : ℂ) * ((f - z) / z - ((f - z) / z) ^ 2 / 2) + ((Qc γ : ℝ) : ℂ) * L
      = ((-2 * b : ℝ) : ℂ) * (1 / z) + ((-γ * (b ^ 2 - s) : ℝ) : ℂ) * (1 / z ^ 2) + Rc := by
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    rw [hRc, he₁, he₂, hfeq, hQc]
    push_cast
    field_simp
    ring
  have kre := congrArg Complex.re key
  simp only [Complex.add_re, Complex.re_ofReal_mul] at kre
  set T := Real.log ‖f‖ - Real.log ‖z‖ - ((f - z) / z - ((f - z) / z) ^ 2 / 2).re with hT
  have hexpr : 2 / γ * Real.log ‖f‖ + Qc γ * L.re - 2 / γ * Real.log ‖z‖
      - (-2 * (1 / z).re * b - γ * (1 / z ^ 2).re * (b ^ 2 - s)) = 2 / γ * T + Rc.re := by
    rw [hT]; linear_combination kre
  rw [hexpr]
  -- bound on ‖u‖³
  have hu : ‖(f - z) / z‖ ≤ γ * |b| / δ + 2 * s / δ ^ 2 := by
    rw [norm_div]
    have h1 : ‖f - z‖ / ‖z‖ ≤ ‖f - z‖ / δ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hzn
    have h2 : ‖f - z‖ / δ ≤ (γ * |b| + 2 * s / δ) / δ := by
      apply div_le_div_of_nonneg_right _ hδ.le
      rw [abs_mul, abs_of_pos hγ] at hdisp; exact hdisp
    have h3 : (γ * |b| + 2 * s / δ) / δ = γ * |b| / δ + 2 * s / δ ^ 2 := by field_simp
    linarith
  have hx : 0 ≤ γ * |b| / δ := by positivity
  have hy : 0 ≤ 2 * s / δ ^ 2 := by positivity
  have hu3 : ‖(f - z) / z‖ ^ 3 ≤ 4 * (γ ^ 3 / δ ^ 3 * |b| ^ 3 + 8 / δ ^ 6 * s ^ 2) := by
    have hcube : ‖(f - z) / z‖ ^ 3 ≤ (γ * |b| / δ + 2 * s / δ ^ 2) ^ 3 := by
      gcongr
    have hpm : (γ * |b| / δ + 2 * s / δ ^ 2) ^ 3
        ≤ 4 * ((γ * |b| / δ) ^ 3 + (2 * s / δ ^ 2) ^ 3) := by
      nlinarith [mul_nonneg (add_nonneg hx hy) (sq_nonneg (γ * |b| / δ - 2 * s / δ ^ 2))]
    have hs3 : s ^ 3 ≤ s ^ 2 := by nlinarith
    have hy3 : (2 * s / δ ^ 2) ^ 3 ≤ 8 / δ ^ 6 * s ^ 2 := by
      rw [div_pow, mul_pow]
      have : (δ ^ 2) ^ 3 = δ ^ 6 := by ring
      rw [this, div_le_iff₀ (by positivity)]
      have : 8 / δ ^ 6 * s ^ 2 * δ ^ 6 = 8 * s ^ 2 := by field_simp
      rw [this]; norm_num; linarith
    have hx3 : (γ * |b| / δ) ^ 3 = γ ^ 3 / δ ^ 3 * |b| ^ 3 := by ring
    linarith
  have hTb : |2 / γ * T| ≤ 2 / γ * (C₃ δ R * (4 * (γ ^ 3 / δ ^ 3 * |b| ^ 3
      + 8 / δ ^ 6 * s ^ 2))) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / γ)]
    gcongr
    exact hlog.trans (mul_le_mul_of_nonneg_left hu3 hC3)
  -- bound on ‖Rc‖
  have hP1 : ‖((2 / γ : ℝ) : ℂ) * (-(e₁ / z))‖ ≤ 2 / γ * (C₁ δ * (m + s ^ 2) / δ) := by
    rw [norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / γ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hδ hzn).trans
      (div_le_div_of_nonneg_right he1 hδ.le)
  have hN : ‖2 * ((γ * b : ℝ) : ℂ) * a + a ^ 2‖
      ≤ 2 * (γ * |b|) * (2 * s / δ) + (2 * s / δ) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hγ]
    norm_num
    have hA : 0 ≤ ‖a‖ := norm_nonneg a
    gcongr
  have hP2 : ‖((-1 / γ : ℝ) : ℂ) * ((2 * ((γ * b : ℝ) : ℂ) * a + a ^ 2) / z ^ 2)‖
      ≤ 4 / δ ^ 3 * (s * |b|) + 4 / (γ * δ ^ 4) * s ^ 2 := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      show |(-1 / γ)| = 1 / γ by rw [abs_div, abs_neg, abs_one, abs_of_pos hγ]]
    calc 1 / γ * (‖2 * ((γ * b : ℝ) : ℂ) * a + a ^ 2‖ / ‖z‖ ^ 2)
        ≤ 1 / γ * ((2 * (γ * |b|) * (2 * s / δ) + (2 * s / δ) ^ 2) / δ ^ 2) := by
          gcongr
      _ = 4 / δ ^ 3 * (s * |b|) + 4 / (γ * δ ^ 4) * s ^ 2 := by field_simp; ring
  have hP3 : ‖((Qc γ : ℝ) : ℂ) * e₂‖ ≤ Qc γ * (C₂ δ * (m + s ^ 2)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQc0]
    exact mul_le_mul_of_nonneg_left he2 hQc0
  have hRcb : |Rc.re| ≤ 2 / γ * (C₁ δ * (m + s ^ 2) / δ)
      + (4 / δ ^ 3 * (s * |b|) + 4 / (γ * δ ^ 4) * s ^ 2) + Qc γ * (C₂ δ * (m + s ^ 2)) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hRc]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    linarith
  -- combine
  have hsb : 0 ≤ s * |b| := by positivity
  have hs2 : 0 ≤ s ^ 2 := by positivity
  have hb3 : 0 ≤ |b| ^ 3 := by positivity
  have hα : 0 ≤ 2 / γ * C₁ δ / δ := div_nonneg (mul_nonneg (by positivity) hC1) hδ.le
  have hζ : 0 ≤ Qc γ * C₂ δ := mul_nonneg hQc0 hC2
  have hη : 0 ≤ 4 / (γ * δ ^ 4) := by positivity
  have hβ : 0 ≤ 4 / δ ^ 3 := by positivity
  have hεp : 0 ≤ 8 / γ * C₃ δ R * (γ ^ 3 / δ ^ 3) :=
    mul_nonneg (mul_nonneg (by positivity) hC3) (by positivity)
  have hεq : 0 ≤ 8 / γ * C₃ δ R * (8 / δ ^ 6) :=
    mul_nonneg (mul_nonneg (by positivity) hC3) (by positivity)
  set K := 2 / γ * C₁ δ / δ + 4 / δ ^ 3 + 4 / (γ * δ ^ 4) + Qc γ * C₂ δ
    + 8 / γ * C₃ δ R * (γ ^ 3 / δ ^ 3) + 8 / γ * C₃ δ R * (8 / δ ^ 6) with hK
  have k1 : 2 / γ * C₁ δ / δ + Qc γ * C₂ δ ≤ K := by rw [hK]; linarith
  have k2 : 4 / δ ^ 3 ≤ K := by rw [hK]; linarith
  have k3 : 2 / γ * C₁ δ / δ + 4 / (γ * δ ^ 4) + Qc γ * C₂ δ
      + 8 / γ * C₃ δ R * (8 / δ ^ 6) ≤ K := by rw [hK]; linarith
  have k4 : 8 / γ * C₃ δ R * (γ ^ 3 / δ ^ 3) ≤ K := by rw [hK]; linarith
  calc |2 / γ * T + Rc.re| ≤ |2 / γ * T| + |Rc.re| := abs_add_le _ _
    _ ≤ 2 / γ * (C₃ δ R * (4 * (γ ^ 3 / δ ^ 3 * |b| ^ 3 + 8 / δ ^ 6 * s ^ 2)))
        + (2 / γ * (C₁ δ * (m + s ^ 2) / δ)
          + (4 / δ ^ 3 * (s * |b|) + 4 / (γ * δ ^ 4) * s ^ 2) + Qc γ * (C₂ δ * (m + s ^ 2))) :=
        add_le_add hTb hRcb
    _ = (2 / γ * C₁ δ / δ + Qc γ * C₂ δ) * m + 4 / δ ^ 3 * (s * |b|)
        + (2 / γ * C₁ δ / δ + 4 / (γ * δ ^ 4) + Qc γ * C₂ δ + 8 / γ * C₃ δ R * (8 / δ ^ 6))
          * s ^ 2
        + 8 / γ * C₃ δ R * (γ ^ 3 / δ ^ 3) * |b| ^ 3 := by ring
    _ ≤ K * m + K * (s * |b|) + K * s ^ 2 + K * |b| ^ 3 :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right k1 hm)
          (mul_le_mul_of_nonneg_right k2 hsb)) (mul_le_mul_of_nonneg_right k3 hs2))
          (mul_le_mul_of_nonneg_right k4 hb3)
    _ = K * (|b| ^ 3 + s * |b| + m + s ^ 2) := by ring

end OnePointExpansion

end QuantumZipper
