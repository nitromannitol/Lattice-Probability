/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PowerWindow at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib




 

set_option autoImplicit false

open Filter Real
open scoped Topology

namespace SupercriticalLQGUniqueness.Exponent.PowerWindow

private lemma sqrt_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt (n : ℝ) / (n : ℝ)
  rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by ring, Real.rpow_sub hn', Real.rpow_one, Real.sqrt_eq_rpow]

private lemma sqrt_error_div_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => (C * Real.sqrt (n : ℝ) + C) / (n : ℝ)) atTop (𝓝 0) := by
  have h₁ := (sqrt_div_nat_tendsto_zero.const_mul C)
  have h₂ := (tendsto_const_nhds.div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ)) :
    Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0))
  convert h₁.add h₂ using 1 <;> simp only [mul_zero, zero_add, add_div]
  funext n
  ring

lemma perturbation_sqrt_tendsto {a b : ℕ → ℝ} {l C : ℝ}
    (ha : Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 l))
    (he : ∀ n, |b n - a n| ≤ C * Real.sqrt (n : ℝ) + C) :
    Tendsto (fun n => b n / (n : ℝ)) atTop (𝓝 l) := by
  have hz := sqrt_error_div_tendsto_zero C
  have hd : Tendsto (fun n => (b n - a n) / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm ?_ hz
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.cast_zero, div_zero, norm_zero, Real.sqrt_zero, mul_zero, zero_add]
      norm_num
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      calc
        ‖(b n - a n) / (n : ℝ)‖ = |b n - a n| / (n : ℝ) := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hn']
        _ ≤ (C * Real.sqrt (n : ℝ) + C) / (n : ℝ) := div_le_div_of_nonneg_right (he n) hn'.le
  convert ha.add hd using 1
  · funext n
    simp only [sub_div]
    ring
  · simp only [add_zero]

lemma logb_median_asymptotic
    (μ lam : ℕ → ℝ) (α C : ℝ)
    (_hμ : ∀ n, 0 < μ n) (_hlam : ∀ n, 0 < lam n)
    (hlim : Tendsto (fun n => Real.logb 2 (μ n) / (n : ℝ)) atTop (𝓝 (-α)))
    (hcmp : ∀ n, |Real.log (μ n) - Real.log (lam n)| ≤ C * Real.sqrt (n : ℝ) + C) :
    Tendsto (fun n => (Real.logb 2 (lam n) + α * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcmp' : ∀ n, |Real.logb 2 (lam n) - Real.logb 2 (μ n)| ≤
      (C / Real.log 2) * Real.sqrt (n : ℝ) + C / Real.log 2 := by
    intro n
    rw [Real.logb, Real.logb, ← sub_div, abs_div, abs_of_pos hlog2]
    have h := div_le_div_of_nonneg_right (hcmp n) hlog2.le
    calc
      |Real.log (lam n) - Real.log (μ n)| / Real.log 2 =
          |Real.log (μ n) - Real.log (lam n)| / Real.log 2 := by rw [abs_sub_comm]
      _ ≤ (C * Real.sqrt (n : ℝ) + C) / Real.log 2 := h
      _ = (C / Real.log 2) * Real.sqrt (n : ℝ) + C / Real.log 2 := by ring
  have hlamlim := perturbation_sqrt_tendsto hlim hcmp'
  have hsum := hlamlim.add (tendsto_const_nhds (x := α) (f := atTop))
  have hsum' : Tendsto (fun n => Real.logb 2 (lam n) / (n : ℝ) + α) atTop (𝓝 0) := by
    simpa only [neg_add_cancel] using hsum
  apply hsum'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp


private lemma sqrt_div_real_tendsto_zero :
    Tendsto (fun r : ℝ => Real.sqrt r / r) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by ring,
    Real.rpow_sub hr, Real.rpow_one, Real.sqrt_eq_rpow]

private lemma sqrt_add_one_div_tendsto_zero :
    Tendsto (fun r : ℝ => Real.sqrt (r + 1) / r) atTop (𝓝 0) := by
  have h₁ := sqrt_div_real_tendsto_zero.comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have h₂ : Tendsto (fun r : ℝ => (r + 1) / r) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds.div_atTop tendsto_id :
      Tendsto (fun r : ℝ => (1 : ℝ) / r) atTop (𝓝 0))
    have hsum : Tendsto (fun r : ℝ => 1 + 1 / r) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds.add h)
    apply hsum.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    field_simp
  have hprod := h₁.mul h₂
  have hprod' : Tendsto (fun r : ℝ => Real.sqrt (r + 1) / (r + 1) * ((r + 1) / r))
      atTop (𝓝 0) := by simpa only [Function.comp_def, id_eq, zero_mul] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop (-1 : ℝ)] with r hr
  have hr1 : r + 1 ≠ 0 := by linarith
  field_simp

private lemma logb_floor_div_tendsto (lam : ℕ → ℝ) (α : ℝ)
    (hlim : Tendsto (fun n => Real.logb 2 (lam n) / (n : ℝ)) atTop (𝓝 (-α))) :
    Tendsto (fun r : ℝ => Real.logb 2 (lam ⌊r⌋₊) / r) atTop (𝓝 (-α)) := by
  have h₁ := hlim.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h₂ := (tendsto_nat_floor_div_atTop :
    Tendsto (fun r : ℝ => (⌊r⌋₊ : ℝ) / r) atTop (𝓝 1))
  have hprod := h₁.mul h₂
  have hprod' : Tendsto (fun r : ℝ =>
      (Real.logb 2 (lam ⌊r⌋₊) / (⌊r⌋₊ : ℝ)) * ((⌊r⌋₊ : ℝ) / r))
      atTop (𝓝 (-α)) := by simpa only [Function.comp_def, mul_one] using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hfloor : ⌊r⌋₊ ≠ 0 := by
    exact Nat.ne_of_gt (Nat.floor_pos.mpr (by linarith))
  have hfloor' : (⌊r⌋₊ : ℝ) ≠ 0 := by exact_mod_cast hfloor
  field_simp

private lemma floor_sqrt_error_div_tendsto_zero (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun r : ℝ => (C * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C) / r)
      atTop (𝓝 0) := by
  have h₁ := (sqrt_add_one_div_tendsto_zero.const_mul C)
  have h₂ := (tendsto_const_nhds.div_atTop tendsto_id :
    Tendsto (fun r : ℝ => C / r) atTop (𝓝 0))
  have hg : Tendsto (fun r : ℝ => (C * Real.sqrt (r + 1) + C) / r) atTop (𝓝 0) := by
    convert h₁.add h₂ using 1
    · funext r
      ring
    · norm_num
  apply squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hs : 0 ≤ Real.sqrt ((⌊r⌋₊ : ℝ) + 1) := Real.sqrt_nonneg _
    exact div_nonneg (add_nonneg (mul_nonneg hC hs) hC) hr.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hf : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr.le
    have hs := Real.sqrt_le_sqrt (show (⌊r⌋₊ : ℝ) + 1 ≤ r + 1 by linarith)
    apply div_le_div_of_nonneg_right _ hr.le
    linarith only [mul_le_mul_of_nonneg_left hs hC]

private lemma perturbation_floor_sqrt_tendsto (a : ℝ → ℝ) (b : ℕ → ℝ)
    (C l : ℝ) (hC : 0 ≤ C)
    (hb : Tendsto (fun r : ℝ => b ⌊r⌋₊ / r) atTop (𝓝 l))
    (hcmp : ∀ r : ℝ, 1 ≤ r → |a r - b ⌊r⌋₊| ≤
      C * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C) :
    Tendsto (fun r : ℝ => a r / r) atTop (𝓝 l) := by
  have hz : Tendsto (fun r : ℝ =>
      (C * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C) / r) atTop (𝓝 0) := by
    exact floor_sqrt_error_div_tendsto_zero C hC
  have hd : Tendsto (fun r : ℝ => (a r - b ⌊r⌋₊) / r) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    calc
      ‖(a r - b ⌊r⌋₊) / r‖ = |a r - b ⌊r⌋₊| / r := by rw [Real.norm_eq_abs, abs_div, abs_of_pos hrpos]
      _ ≤ (C * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C) / r := div_le_div_of_nonneg_right (hcmp r hr) hrpos.le
  convert hb.add hd using 1
  · funext r
    simp only [sub_div]
    ring
  · simp only [add_zero]

lemma power_window_of_log_ratio (a : ℝ → ℝ) (α : ℝ)
    (ha : ∀ ε, 0 < ε → 0 < a ε)
    (hlim : Tendsto (fun ε : ℝ => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 α)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (α + δ)) ≤ ENNReal.ofReal (a ε) ∧
      ENNReal.ofReal (a ε) ≤ ENNReal.ofReal (ε ^ (α - δ)) := by
  intro δ hδ
  have hnear : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      α - δ < Real.log (a ε) / Real.log ε ∧
      Real.log (a ε) / Real.log ε < α + δ :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hnear, self_mem_nhdsWithin, hsmall]
    with ε hnear hε hεone
  have hεpos : 0 < ε := hε
  have hεlt : ε < 1 := hεone
  have hlogneg : Real.log ε < 0 := Real.log_neg hεpos hεlt
  have hlow : (α + δ) * Real.log ε ≤ Real.log (a ε) := by
    have hh := (div_lt_iff_of_neg hlogneg).mp hnear.2
    nlinarith only [hh]
  have hupp : Real.log (a ε) ≤ (α - δ) * Real.log ε := by
    have hh := (lt_div_iff_of_neg hlogneg).mp hnear.1
    nlinarith only [hh]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    exact (Real.rpow_le_iff_le_log hεpos (ha ε hεpos)).2 hlow
  · apply ENNReal.ofReal_le_ofReal
    exact (Real.le_rpow_iff_log_le (ha ε hεpos) hεpos).2 hupp

lemma logb_half_eq_logb_two_inv (ε : ℝ) :
    Real.logb (1 / 2) ε = Real.logb 2 (1 / ε) := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    Real.logb_inv_base, one_div, Real.logb_inv]

lemma median_power_window (lam : ℕ → ℝ) (a : ℝ → ℝ) (α C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ ε, 0 < ε → 0 < a ε)
    (hlim : Tendsto (fun n => Real.logb 2 (lam n) / (n : ℝ)) atTop (𝓝 (-α)))
    (hmed : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |Real.log (a ε) - Real.log (lam ⌊Real.logb (1 / 2) ε⌋₊)| ≤
        C * Real.sqrt ((⌊Real.logb (1 / 2) ε⌋₊ : ℝ) + 1) + C) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (α + δ)) ≤ ENNReal.ofReal (a ε) ∧
      ENNReal.ofReal (a ε) ≤ ENNReal.ofReal (ε ^ (α - δ)) := by
  have hhalf0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hhalfne : (1 / 2 : ℝ) ≠ 1 := ne_of_lt hhalf1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfloor := logb_floor_div_tendsto lam α hlim
  have hcmp : ∀ r : ℝ, 1 ≤ r →
      |Real.logb 2 (a ((1 / 2 : ℝ) ^ r)) - Real.logb 2 (lam ⌊r⌋₊)| ≤
        (C / Real.log 2) * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C / Real.log 2 := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
    have hepos : 0 < (1 / 2 : ℝ) ^ r := Real.rpow_pos_of_pos hhalf0 r
    have helt : (1 / 2 : ℝ) ^ r < 1 := Real.rpow_lt_one hhalf0.le hhalf1 hrpos
    have hmed' := hmed ((1 / 2 : ℝ) ^ r) hepos helt
    rw [Real.logb_rpow hhalf0 hhalfne] at hmed'
    rw [Real.logb, Real.logb, ← sub_div, abs_div, abs_of_pos hlog2]
    calc
      |Real.log (a ((1 / 2 : ℝ) ^ r)) - Real.log (lam ⌊r⌋₊)| / Real.log 2
          ≤ (C * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C) / Real.log 2 :=
            div_le_div_of_nonneg_right hmed' hlog2.le
      _ = (C / Real.log 2) * Real.sqrt ((⌊r⌋₊ : ℝ) + 1) + C / Real.log 2 := by ring
  have hAR : Tendsto (fun r : ℝ => Real.logb 2 (a ((1 / 2 : ℝ) ^ r)) / r)
      atTop (𝓝 (-α)) :=
    perturbation_floor_sqrt_tendsto
      (fun r => Real.logb 2 (a ((1 / 2 : ℝ) ^ r)))
      (fun n => Real.logb 2 (lam n)) (C / Real.log 2) (-α)
      (div_nonneg hC hlog2.le) hfloor hcmp
  have hR : Tendsto (Real.logb (1 / 2)) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_logb_nhdsGT_zero_of_base_lt_one hhalf0 hhalf1
  have hquot : Tendsto (fun ε : ℝ =>
      Real.logb 2 (a ε) / Real.logb (1 / 2) ε) (𝓝[>] (0 : ℝ)) (𝓝 (-α)) := by
    apply (hAR.comp hR).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Function.comp_def, Real.rpow_logb hhalf0 hhalfne hε]
  have hratio : Tendsto (fun ε : ℝ => Real.log (a ε) / Real.log ε)
      (𝓝[>] (0 : ℝ)) (𝓝 α) := by
    have hneg := hquot.neg
    have hneg' : Tendsto (fun ε : ℝ =>
        -(Real.logb 2 (a ε) / Real.logb (1 / 2) ε))
        (𝓝[>] (0 : ℝ)) (𝓝 α) := by simpa only [neg_neg] using hneg
    apply hneg'.congr'
    filter_upwards [self_mem_nhdsWithin,
        (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 from
          nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)))]
      with ε hε hεone
    have hlogeps : Real.log ε ≠ 0 := ne_of_lt (Real.log_neg hε hεone)
    have hlogtwo : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2
    rw [Real.logb, Real.logb]
    have hhalf_log : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      norm_num [Real.log_div]
    rw [hhalf_log]
    field_simp
  exact power_window_of_log_ratio a α ha hratio

lemma median_power_window_exponent (lam : ℕ → ℝ) (a : ℝ → ℝ)
    (ξ α C : ℝ) (hξ : 0 < ξ) (hC : 0 ≤ C)
    (ha : ∀ ε, 0 < ε → 0 < a ε)
    (hlim : Tendsto (fun n => Real.logb 2 (lam n) / (n : ℝ)) atTop (𝓝 (-α)))
    (hmed : ∀ ε : ℝ, 0 < ε → ε < 1 →
      |Real.log (a ε) - Real.log (lam ⌊Real.logb (1 / 2) ε⌋₊)| ≤
        C * Real.sqrt ((⌊Real.logb (1 / 2) ε⌋₊ : ℝ) + 1) + C) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε ^ (1 - ξ * ((1 - α) / ξ) + δ)) ≤ ENNReal.ofReal (a ε) ∧
      ENNReal.ofReal (a ε) ≤ ENNReal.ofReal (ε ^ (1 - ξ * ((1 - α) / ξ) - δ)) := by
  have heq : 1 - ξ * ((1 - α) / ξ) = α := by
    have hξne : ξ ≠ 0 := ne_of_gt hξ
    field_simp
    ring
  intro δ hδ
  simpa only [heq] using median_power_window lam a α C hC ha hlim hmed δ hδ





end SupercriticalLQGUniqueness.Exponent.PowerWindow
