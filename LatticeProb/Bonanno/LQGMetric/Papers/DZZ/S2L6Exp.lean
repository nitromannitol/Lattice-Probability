/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S2L6Exp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L6Max

/-!
# DZZ Lemma 2.6, second inequality: expectation form (task P2-DZZPRE3)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 521:
`E max_{u,v ∈ 𝕍, |u−v| ≤ δ} (|h̃_δ(u) − h̃_δ(v)| + |η_δ(v) − η_δ(u)|) = O(√(log δ⁻¹))`.

DZZ (l. 527–529) obtain this from Fernique (Lemma 2.3) + concentration (Lemma 2.1) + a union bound;
the resulting tail bound is `dzz_sup_incr_tail` (S2L6Max). Here we integrate the tail
(layer-cake formula, `lintegral_eq_lintegral_meas_lt`, plus the Gaussian integral), which is the
standard passage from a Gaussian tail to an expectation implicit in DZZ's "this yields".

* `integral_le_of_gaussTail`: `P(f > B + x) ≤ 2e^{−x²/c}` for `x > 0` ⟹ `E f ≤ B + 2√(πc)`.
* `exists_continuous_tildeHInf`: continuous versions of `h̃_δ`.
* `dzz_lemma26_max`: **DZZ Lemma 2.6, second inequality**, for continuous versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace LQGMetric
namespace DZZ

open KilledHeat WhiteNoise SupTail DGo

universe u

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `π ‖K^{h̃}_δ(u) − K^{h̃}_δ(v)‖² ≤ 28 |u − v|/δ` (Lemma 2.5, kernel form). -/
lemma pi_sq_norm_tildeHKernel_sub_le (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) (u v : ℂ) :
    Real.pi * ‖wndKernelL2 openSquare (Ioi (δ ^ 2)) u - wndKernelL2 openSquare (Ioi (δ ^ 2)) v‖ ^ 2
      ≤ 28 * ‖u - v‖ / δ := by
  have h := dzz_lemma25_tildeH hW hδ u v
  simp only [tildeHInf, wnField] at h
  rwa [variance_sqrtPi_sub hW] at h

/-- Continuous versions of `h̃_δ` exist. -/
theorem exists_continuous_tildeHInf (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧
      ∀ x, Y x =ᵐ[P] tildeHInf W δ x := by
  have hpi := Real.pi_pos
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_continuous_modification_of_kernel_half hW
    (wndKernelL2 openSquare (Ioi (δ ^ 2))) (K := 28 / (Real.pi * δ)) (by positivity)
    (fun x x' => by
      have h := pi_sq_norm_tildeHKernel_sub_le hW hδ x x'
      have h' := (le_div_iff₀ hδ).mp h
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith) (Real.sqrt Real.pi)
  exact ⟨Y, hYc, hYm, hY⟩

/-- The tail bound of `dzz_sup_incr_tail` for a continuous version of a white-noise field
`√π W(F x)` with `π‖F u − F v‖² ≤ 1076 |u − v|/δ`. -/
lemma sup_tail_of_wn (hW : IsWhiteNoise P W) (F : ℂ → WNSpace) {δ : ℝ} (hδ : 0 < δ)
    (hF : ∀ u v, Real.pi * ‖F u - F v‖ ^ 2 ≤ 1076 * ‖u - v‖ / δ) (X : ℂ → Ω → ℝ)
    (hXc : ∀ ω, Continuous fun x => X x ω)
    (hX : ∀ x, X x =ᵐ[P] fun ω => Real.sqrt Real.pi * W (F x) ω) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ∃ u ∈ ferniqueBox 0 1, ∃ v ∈ ferniqueBox 0 1, ‖u - v‖ ≤ δ ∧
      2 * (Real.sqrt (2 * (6 * 1076) * Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2)) +
        ferniqueCF * Real.sqrt (3 * 1076) + x) ≤ |X u ω - X v ω|} ≤
      Real.exp (-x ^ 2 / (2 * (6 * 1076))) := by
  have := hW.isProbabilityMeasure
  refine dzz_sup_incr_tail ((isGaussianProcess_sqrtPi hW F).congr fun x => (hX x).symm)
    (fun v => by rw [integral_congr_ae (hX v)]; exact integral_sqrtPi hW _) hXc
    (by norm_num) hδ (fun u v => ?_) hx
  have hae : (fun ω => (X v ω - X u ω) ^ 2) =ᵐ[P] fun ω =>
      (Real.sqrt Real.pi * W (F u) ω - Real.sqrt Real.pi * W (F v) ω) ^ 2 := by
    filter_upwards [hX u, hX v] with ω h1 h2; rw [h1, h2]; ring
  rw [integral_congr_ae hae, integral_sq_sqrtPi_sub hW]
  exact hF u v

/-- `log(2⌈1/δ⌉²) ≤ 5 log δ⁻¹` for `0 < δ ≤ 1/2`. -/
lemma log_two_ceil_sq_le {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    Real.log (2 * (⌈1 / δ⌉₊ : ℝ) ^ 2) ≤ 5 * Real.log δ⁻¹ := by
  set t := δ⁻¹ with ht
  have ht2 : 2 ≤ t := by rw [ht, le_inv_comm₀ (by norm_num) hδ]; linarith
  have hm1 : (⌈1 / δ⌉₊ : ℝ) < t + 1 := by
    rw [ht, ← one_div]; exact Nat.ceil_lt_add_one (by positivity)
  have hm0 : (0 : ℝ) < ⌈1 / δ⌉₊ := Nat.cast_pos.2 (Nat.ceil_pos.2 (by positivity))
  rw [show (5 : ℝ) * Real.log t = Real.log (t ^ 5) by rw [Real.log_pow]; norm_num]
  refine Real.log_le_log (by positivity) ?_
  have h8 : (2 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht2 3
  have hmsq : (⌈1 / δ⌉₊ : ℝ) ^ 2 ≤ (t + 1) ^ 2 := pow_le_pow_left₀ hm0.le hm1.le 2
  have h4 : (t + 1) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h5 : 2 ^ 3 * t ^ 2 ≤ t ^ 3 * t ^ 2 := mul_le_mul_of_nonneg_right h8 (sq_nonneg t)
  have e5 : t ^ 5 = t ^ 3 * t ^ 2 := by ring
  nlinarith

end DZZ
end LQGMetric
