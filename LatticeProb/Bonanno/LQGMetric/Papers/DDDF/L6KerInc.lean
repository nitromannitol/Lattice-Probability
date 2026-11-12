/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L6KerInc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L6KerBd

/-!
# DDDF Lemma 6, Step 3: increments of the kernels of `φ_L`

DDDF (arXiv:1904.08021, `tightness.tex` l. 577–640): `E(φ_i(x) − φ_i(x'))² ≤ C|x − x'|` for
`φ₁`, `φ_{2,1}`, `φ_{2,2}`, `φ_{2,3}`. With `h = |x − x'|` the time integral is split at `t = h`
(DDDF's `t ≶ √|x − x'|` after their change of variables `t ↔ 2t²`, l. 584):

* `t ≤ h`: `(k_x − k_{x'})² ≤ 2k_x² + 2k_{x'}²` and the pointwise bound `C/t e^{−r²/(βt)}`
  (Step 3(B), `L6KerBd`), whose `y`-integral is bounded: contribution `≤ C h`;
* `t > h`: the Gaussian increment bound (Step 3(A), (eq:BoundBis), (eq:BoundBis2))
  `≤ K h² t⁻³ (e^{−r²/(βt)} + e^{−r'²/(βt)})`, `y`-integral `≤ K' h²/t²`, and `∫_h^∞ h²/t² = h`.

`lintegral_inc_le` packages this; `l6_lKer_inc`, `l6_gKer_inc` apply it. For `h ≥ ε` the bound
follows from the uniform bounds. No convexity of `U`, `V`, `K` is used (`U` bounded).
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

lemma measurable_gaussR {S : Set ℝ} (hS : MeasurableSet S) {α : ℝ → ℝ} (hα : Measurable α)
    (β : ℝ) (w : ℂ) : Measurable (gaussR S α β w) := by
  unfold gaussR
  refine Measurable.indicator ?_ (hS.prod MeasurableSet.univ)
  exact (hα.comp measurable_fst).mul (by fun_prop)

lemma gaussR_of_mem {S : Set ℝ} {α : ℝ → ℝ} {β : ℝ} {w : ℂ} {t : ℝ} (ht : t ∈ S) (y : ℂ) :
    gaussR S α β w (t, y) = α t * Real.exp (-‖w - y‖ ^ 2 / (β * t)) := by
  rw [gaussR, indicator_of_mem (mk_mem_prod ht (mem_univ y))]

lemma gaussR_of_notMem {S : Set ℝ} {α : ℝ → ℝ} {β : ℝ} {w : ℂ} {t : ℝ} (ht : t ∉ S) (y : ℂ) :
    gaussR S α β w (t, y) = 0 := by
  rw [gaussR, indicator_of_notMem (fun hh => ht (mem_prod.1 hh).1)]

/-- `∫_h^1 (K h²/t³)(π β t) dt ≤ K π β h`. -/
lemma setLIntegral_Ioc_inv_sq_le {K β h : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (hh : 0 < h) :
    ∫⁻ t in Ioc h 1, ENNReal.ofReal (K * h ^ 2 / t ^ 3 * (Real.pi * (β * t))) ≤
      ENNReal.ofReal (K * (Real.pi * β) * h) := by
  have hc : 0 ≤ K * (Real.pi * β) * h ^ 2 := by positivity
  have hint : IntegrableOn (fun t : ℝ => K * (Real.pi * β) * h ^ 2 * t ^ (-2 : ℝ)) (Ioi h) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hh).const_mul _
  calc ∫⁻ t in Ioc h 1, ENNReal.ofReal (K * h ^ 2 / t ^ 3 * (Real.pi * (β * t)))
      = ∫⁻ t in Ioc h 1, ENNReal.ofReal (K * (Real.pi * β) * h ^ 2 * t ^ (-2 : ℝ)) := by
        refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        have ht0 : 0 < t := hh.trans (mem_Ioc.1 ht).1
        congr 1
        rw [Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
    _ ≤ ∫⁻ t in Ioi h, ENNReal.ofReal (K * (Real.pi * β) * h ^ 2 * t ^ (-2 : ℝ)) :=
        lintegral_mono_set Ioc_subset_Ioi_self
    _ = ENNReal.ofReal (∫ t in Ioi h, K * (Real.pi * β) * h ^ 2 * t ^ (-2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg hc (Real.rpow_nonneg (le_of_lt (hh.trans ht)) _)
    _ = ENNReal.ofReal (K * (Real.pi * β) * h) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hh]
        congr 1
        rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- **Increment lemma** (DDDF Step 3, split at `t = |x − x'|`). -/
lemma lintegral_inc_le {φ φ' : ℝ × ℂ → ℝ} {w w' : ℂ} {C K β h : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hβ : 0 < β) (hh : 0 < h)
    (h1 : ∀ p, φ p ^ 2 ≤ gaussR (Ioc 0 1) (fun t => C / t) β w p)
    (h1' : ∀ p, φ' p ^ 2 ≤ gaussR (Ioc 0 1) (fun t => C / t) β w' p)
    (h2 : ∀ t y, h < t → t ≤ 1 → (φ (t, y) - φ' (t, y)) ^ 2 ≤
      K * h ^ 2 / t ^ 3 * (Real.exp (-‖w - y‖ ^ 2 / (β * t)) +
        Real.exp (-‖w' - y‖ ^ 2 / (β * t)))) :
    ∫⁻ p, ENNReal.ofReal ((φ p - φ' p) ^ 2) ≤ ENNReal.ofReal ((4 * C + 2 * K) * (Real.pi * β) * h) := by
  have hpi := Real.pi_pos
  set α₁ : ℝ → ℝ := fun t => 2 * C / t
  set α₂ : ℝ → ℝ := fun t => K * h ^ 2 / t ^ 3
  have hα₁ : Measurable α₁ := by fun_prop
  have hα₂ : Measurable α₂ := by fun_prop
  have hS1 : Ioc (0 : ℝ) h ⊆ Ioi 0 := fun t ht => (mem_Ioc.1 ht).1
  have hS2 : Ioc h 1 ⊆ Ioi 0 := fun t ht => hh.trans (mem_Ioc.1 ht).1
  have hn1 : ∀ t ∈ Ioc (0 : ℝ) h, 0 ≤ α₁ t := fun t ht => by
    have := (mem_Ioc.1 ht).1; simp only [α₁]; positivity
  have hn2 : ∀ t ∈ Ioc h 1, 0 ≤ α₂ t := fun t ht => by
    have := hh.trans (mem_Ioc.1 ht).1; simp only [α₂]; positivity
  set G : ℝ × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (gaussR (Ioc 0 h) α₁ β w p) + ENNReal.ofReal (gaussR (Ioc 0 h) α₁ β w' p) +
      (ENNReal.ofReal (gaussR (Ioc h 1) α₂ β w p) + ENNReal.ofReal (gaussR (Ioc h 1) α₂ β w' p))
  have hzero : ∀ {ψ : ℝ × ℂ → ℝ} {v : ℂ}, (∀ p, ψ p ^ 2 ≤ gaussR (Ioc 0 1) (fun t => C / t) β v p)
      → ∀ t y, t ∉ Ioc (0 : ℝ) 1 → ψ (t, y) = 0 := fun {ψ} {v} hψ t y ht => by
    have := hψ (t, y); rw [gaussR_of_notMem ht] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
  have hpt : ∀ p, ENNReal.ofReal ((φ p - φ' p) ^ 2) ≤ G p := by
    rintro ⟨t, y⟩
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    swap
    · rw [hzero h1 t y ht, hzero h1' t y ht, sub_zero, sq, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    by_cases hth : t ≤ h
    · have hth' : t ∈ Ioc (0 : ℝ) h := ⟨ht.1, hth⟩
      have a1 := h1 (t, y)
      have a2 := h1' (t, y)
      rw [gaussR_of_mem ht] at a1 a2
      refine le_trans ?_ le_self_add
      rw [gaussR_of_mem hth', gaussR_of_mem hth', ← ENNReal.ofReal_add (by
        have := hn1 t hth'; positivity) (by have := hn1 t hth'; positivity)]
      apply ENNReal.ofReal_le_ofReal
      simp only [α₁]
      have e : 2 * C / t = 2 * (C / t) := by ring
      rw [e]
      nlinarith [sq_nonneg (φ (t, y) + φ' (t, y))]
    · push Not at hth
      have hth' : t ∈ Ioc h 1 := ⟨hth, ht.2⟩
      refine le_trans ?_ le_add_self
      rw [gaussR_of_mem hth', gaussR_of_mem hth', ← ENNReal.ofReal_add (by
        have := hn2 t hth'; positivity) (by have := hn2 t hth'; positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (h2 t y hth ht.2).trans (le_of_eq ?_)
      simp only [α₂]; ring
  have hm1 := measurable_gaussR (measurableSet_Ioc (a := 0) (b := h)) hα₁ β
  have hm2 := measurable_gaussR (measurableSet_Ioc (a := h) (b := 1)) hα₂ β
  have I1 : ∀ v, ∫⁻ p, ENNReal.ofReal (gaussR (Ioc 0 h) α₁ β v p) ≤
      ENNReal.ofReal (2 * C * (Real.pi * β) * h) := fun v => by
    refine (lintegral_gaussR_le measurableSet_Ioc hS1 hn1 hβ v).trans (le_of_eq ?_)
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => ENNReal.ofReal
      (2 * C * (Real.pi * β))) (fun t ht => by
        have := (mem_Ioc.1 ht).1; simp only [α₁]; congr 1; field_simp),
      setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  have I2 : ∀ v, ∫⁻ p, ENNReal.ofReal (gaussR (Ioc h 1) α₂ β v p) ≤
      ENNReal.ofReal (K * (Real.pi * β) * h) := fun v =>
    (lintegral_gaussR_le measurableSet_Ioc hS2 hn2 hβ v).trans
      (setLIntegral_Ioc_inv_sq_le hK hβ hh)
  calc ∫⁻ p, ENNReal.ofReal ((φ p - φ' p) ^ 2) ≤ ∫⁻ p, G p := lintegral_mono hpt
    _ = ((∫⁻ p, ENNReal.ofReal (gaussR (Ioc 0 h) α₁ β w p)) +
          (∫⁻ p, ENNReal.ofReal (gaussR (Ioc 0 h) α₁ β w' p))) +
        ((∫⁻ p, ENNReal.ofReal (gaussR (Ioc h 1) α₂ β w p)) +
          (∫⁻ p, ENNReal.ofReal (gaussR (Ioc h 1) α₂ β w' p))) := by
        simp only [G]
        rw [lintegral_add_left, lintegral_add_left, lintegral_add_left]
        all_goals first
          | exact (hm2 w).ennreal_ofReal
          | exact (hm1 w).ennreal_ofReal
          | exact ((hm1 w).ennreal_ofReal).add (hm1 w').ennreal_ofReal
    _ ≤ (ENNReal.ofReal (2 * C * (Real.pi * β) * h) + ENNReal.ofReal (2 * C * (Real.pi * β) * h))
        + (ENNReal.ofReal (K * (Real.pi * β) * h) + ENNReal.ofReal (K * (Real.pi * β) * h)) := by
        exact add_le_add (add_le_add (I1 w) (I1 w')) (add_le_add (I2 w) (I2 w'))
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- Gaussian increments with time dilation `τ ∈ [t, M²t]` (DDDF (eq:BoundBis), (eq:BoundBis2)). -/
lemma gauss_sub_sq_le {t τ h M : ℝ} (ht : 0 < t) (htτ : t ≤ τ) (hτM : τ ≤ M ^ 2 * t)
    (hM : 1 ≤ M) (hh : h ^ 2 ≤ t) {w w' z : ℂ} (hη : ‖w - w'‖ ≤ M * h) :
    ((Real.pi * t)⁻¹ * Real.exp (-‖w - z‖ ^ 2 / τ) -
        (Real.pi * t)⁻¹ * Real.exp (-‖w' - z‖ ^ 2 / τ)) ^ 2 ≤
      10 * M ^ 4 / Real.pi ^ 2 * h ^ 2 / t ^ 3 *
        (Real.exp (-‖w - z‖ ^ 2 / τ) + Real.exp (-‖w' - z‖ ^ 2 / τ)) := by
  have hpi := Real.pi_pos
  have hτ : 0 < τ := ht.trans_le htτ
  have h0 := sq_gauss_sub_le hτ w w' z
  set η := ‖w - w'‖
  have hη0 : 0 ≤ η := norm_nonneg _
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hη2 : η ^ 2 ≤ M ^ 2 * h ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hη0 hη 2
  have hfac : η ^ 2 * (8 * τ + 2 * η ^ 2) / τ ^ 2 ≤ 10 * M ^ 4 * h ^ 2 / t := by
    have a : (8 * τ + 2 * η ^ 2) / τ ^ 2 ≤ 10 * M ^ 2 / t := by
      rw [div_le_div_iff₀ (by positivity) ht]
      have : η ^ 2 ≤ M ^ 2 * t := hη2.trans (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left htτ hτ.le]
    calc η ^ 2 * (8 * τ + 2 * η ^ 2) / τ ^ 2 = η ^ 2 * ((8 * τ + 2 * η ^ 2) / τ ^ 2) := by ring
      _ ≤ M ^ 2 * h ^ 2 * (10 * M ^ 2 / t) := mul_le_mul hη2 a (by positivity) (by positivity)
      _ = _ := by ring
  have hE : 0 ≤ Real.exp (-‖w - z‖ ^ 2 / τ) + Real.exp (-‖w' - z‖ ^ 2 / τ) := by positivity
  calc _ = (Real.pi * t)⁻¹ ^ 2 * (Real.exp (-‖w - z‖ ^ 2 / τ) -
        Real.exp (-‖w' - z‖ ^ 2 / τ)) ^ 2 := by ring
    _ ≤ (Real.pi * t)⁻¹ ^ 2 * (10 * M ^ 4 * h ^ 2 / t *
        (Real.exp (-‖w - z‖ ^ 2 / τ) + Real.exp (-‖w' - z‖ ^ 2 / τ))) := by
        gcongr; exact h0.trans (mul_le_mul_of_nonneg_right hfac hE)
    _ = _ := by field_simp

end DDDF
end LQGMetric
