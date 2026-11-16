import LatticeProb.Analysis.Schauder.KernelDerivBound
import LatticeProb.Analysis.Schauder.GaussPolyArith

/-!
# Domination of every space derivative of the heat kernel by a doubled-time heat kernel

For `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` on `ℝ^d` and `t > 0`, every derivative of `p_t` is
dominated, with a polynomial weight in `‖y‖/√t`, by `p_{2t}`:
`‖D^n p_t(y)‖ (1 + ‖y‖²/t)^k ≤ C (1/√t)^n p_{2t}(y)`,
with a constant `C` depending only on `d`, `n` and `k`.

The proof writes `s = ‖y‖/√t`. The Gaussian-times-polynomial bound of `KernelDerivBound.lean`
involves `(‖y‖/(2t) + 1/√(2t))^n ≤ (1/√t)^n (1 + s)^n`. The kernel splits as
`p_t(y) = 2^{d/2} exp(-s²/8) p_{2t}(y)`, and the half Gaussian `exp(-s²/8)` absorbs the polynomial
`(1 + s)^n (1 + s²)^k` into a constant.

Away from the origin the same splitting, applied once more at time `2t`, gives
`p_{2t}(y) = 2^{d/2} exp(-‖y‖²/(16t)) p_{4t}(y)`. For `‖y‖ ≥ δ` the exponential is at most
`exp(-δ²/(16t))`, which absorbs the singular factor `(1/√t)^n` uniformly in `t > 0`. Hence every
derivative of `p_t` is bounded by a constant multiple of `p_{4t}` outside the ball of radius `δ`,
uniformly in `t`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

open scoped Nat

noncomputable section

variable {d : ℕ}

/-- The coefficient `‖y‖/(2t) + 1/√(2t)` of the derivative bound is at most
`(1/√t) (1 + ‖y‖/√t)`. -/
private theorem norm_div_add_inv_sqrt_le {t : ℝ} (ht : 0 < t) (y : Euc d) :
    ‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t) ≤ 1 / Real.sqrt t * (1 + ‖y‖ / Real.sqrt t) := by
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hs : Real.sqrt (2 * t) = Real.sqrt 2 * Real.sqrt t := Real.sqrt_mul (by norm_num) t
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have h1 : 1 / Real.sqrt (2 * t) ≤ 1 / Real.sqrt t := by
    apply one_div_le_one_div_of_le hr
    rw [hs]
    nlinarith
  have h3 : ‖y‖ / (2 * t) ≤ ‖y‖ / t := by
    apply div_le_div_of_nonneg_left (norm_nonneg y) ht
    linarith
  have h4 : 1 / Real.sqrt t * (1 + ‖y‖ / Real.sqrt t) = 1 / Real.sqrt t + ‖y‖ / t := by
    rw [show 1 / Real.sqrt t * (1 + ‖y‖ / Real.sqrt t) =
      1 / Real.sqrt t + ‖y‖ / (Real.sqrt t * Real.sqrt t) by ring, hsq]
  rw [h4]
  linarith

/-- Every derivative of `p_t`, with a polynomial weight in `‖y‖/√t`, is dominated by `p_{2t}`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_mul_le (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ * (1 + ‖y‖ ^ 2 / t) ^ k ≤
        C * (1 / Real.sqrt t) ^ n * heatKernel d (2 * t) y := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_one_add_pow_mul_exp_le n k
  refine ⟨n ! * 2 ^ ((d : ℝ) / 2) * C₁, by positivity, fun t ht y => ?_⟩
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs0 : 0 ≤ ‖y‖ / Real.sqrt t := by positivity
  have hsq : ‖y‖ ^ 2 / t = (‖y‖ / Real.sqrt t) ^ 2 := by
    rw [div_pow, Real.sq_sqrt ht.le]
  have hB := norm_div_add_inv_sqrt_le ht y
  have hB0 : 0 ≤ ‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t) := by positivity
  have h1 : ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ ≤
      n ! * heatKernel d t y * (‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t)) ^ n :=
    norm_iteratedFDeriv_heatKernel_le n ht y
  have hsplit := heatKernel_eq_two_pow_mul_exp_mul_heatKernel_two_mul ht y
  have hQ := heatKernel_nonneg (by positivity : 0 < 2 * t) y
  have hP := heatKernel_nonneg ht y
  have hK : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hmp : (1 / Real.sqrt t * (1 + ‖y‖ / Real.sqrt t)) ^ n =
      (1 / Real.sqrt t) ^ n * (1 + ‖y‖ / Real.sqrt t) ^ n := mul_pow _ _ _
  rw [hsq]
  calc ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ * (1 + (‖y‖ / Real.sqrt t) ^ 2) ^ k
      ≤ (n ! * heatKernel d t y * (‖y‖ / (2 * t) + 1 / Real.sqrt (2 * t)) ^ n) *
          (1 + (‖y‖ / Real.sqrt t) ^ 2) ^ k := by gcongr
    _ ≤ (n ! * heatKernel d t y *
          (1 / Real.sqrt t * (1 + ‖y‖ / Real.sqrt t)) ^ n) *
          (1 + (‖y‖ / Real.sqrt t) ^ 2) ^ k := by gcongr
    _ = n ! * 2 ^ ((d : ℝ) / 2) * ((1 + ‖y‖ / Real.sqrt t) ^ n *
          (1 + (‖y‖ / Real.sqrt t) ^ 2) ^ k *
          Real.exp (-((‖y‖ / Real.sqrt t) ^ 2) / 8)) * (1 / Real.sqrt t) ^ n *
          heatKernel d (2 * t) y := by
        rw [hsplit, hsq, neg_div, hmp]
        ring
    _ ≤ n ! * 2 ^ ((d : ℝ) / 2) * C₁ * (1 / Real.sqrt t) ^ n * heatKernel d (2 * t) y := by
        gcongr
        exact hC₁ _ hs0

/-- Away from the origin every derivative of `p_t` is dominated by `p_{4t}`, uniformly in `t`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le_of_le_norm (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ y : Euc d, δ ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ ≤ C * heatKernel d (4 * t) y := by
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_norm_iteratedFDeriv_heatKernel_mul_le (d := d) n 0
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_inv_sqrt_pow_mul_exp_le n (c := δ ^ 2 / 16) (by positivity)
  refine ⟨C₃ * 2 ^ ((d : ℝ) / 2) * C₂, by positivity, fun t ht y hy => ?_⟩
  have h3 : ‖iteratedFDeriv ℝ n (heatKernel d t) y‖ ≤
      C₃ * (1 / Real.sqrt t) ^ n * heatKernel d (2 * t) y := by
    simpa using hC₃ t ht y
  have hsplit := heatKernel_eq_two_pow_mul_exp_mul_heatKernel_two_mul
    (by positivity : 0 < 2 * t) y
  have hQ := heatKernel_nonneg (by positivity : 0 < 4 * t) y
  have hK : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hr : 0 ≤ 1 / Real.sqrt t := by positivity
  have hexp : Real.exp (-(‖y‖ ^ 2 / (2 * t) / 8)) ≤ Real.exp (-(δ ^ 2 / 16 / t)) := by
    apply Real.exp_le_exp.2
    have hy2 : δ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ hδ.le hy 2
    have he : ‖y‖ ^ 2 / (2 * t) / 8 = ‖y‖ ^ 2 / 16 / t := by
      field_simp
      ring
    rw [he]
    have : δ ^ 2 / 16 / t ≤ ‖y‖ ^ 2 / 16 / t := by gcongr
    linarith
  calc ‖iteratedFDeriv ℝ n (heatKernel d t) y‖
      ≤ C₃ * (1 / Real.sqrt t) ^ n * heatKernel d (2 * t) y := h3
    _ = C₃ * (1 / Real.sqrt t) ^ n *
          (2 ^ ((d : ℝ) / 2) * Real.exp (-(‖y‖ ^ 2 / (2 * t) / 8)) *
            heatKernel d (4 * t) y) := by
        rw [hsplit, show 2 * (2 * t) = 4 * t by ring]
    _ ≤ C₃ * (1 / Real.sqrt t) ^ n *
          (2 ^ ((d : ℝ) / 2) * Real.exp (-(δ ^ 2 / 16 / t)) * heatKernel d (4 * t) y) := by
        gcongr
    _ = C₃ * 2 ^ ((d : ℝ) / 2) *
          ((1 / Real.sqrt t) ^ n * Real.exp (-(δ ^ 2 / 16 / t))) * heatKernel d (4 * t) y := by
        ring
    _ ≤ C₃ * 2 ^ ((d : ℝ) / 2) * C₂ * heatKernel d (4 * t) y := by
        gcongr
        exact hC₂ t ht

end

end LatticeProb.Analysis.Schauder
