/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P16Real at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Basic.ENNReal.Real

/-!
# Elementary estimates for the recursion of DDDF Proposition 16

DDDF (arXiv:1904.08021, `tightness.tex` l. 842–869): with `p_i = (p₀C²)^{2^i} C^{-2}` and
`r_i ≥ ℓ_{3,3}(p₀) e^{-Ci} e^{-Cξ√|log p₀C²| 2^{i/2}}`, "taking `i = ⌊2 log₂ s⌋`" gives the
Gaussian tail. Here the arithmetic: `|log q_i| ≤ 2^i κ²` (`sqrt_abs_log_q_le`), the summation
`Σ_{k<i} M 2^{k/2} ≤ 4M(2^{i/2} − 1)` in the inductive form (`four_mul_step`), and the choice of
`i` from `s` (`tail_of_levels`; we take `i = log₂ ⌊s²/(4D²)⌋`, the same choice up to constants).
Own elementary arguments following DDDF's computation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real

namespace LQGMetric
namespace DDDF

lemma sqrt_two_pow (i : ℕ) : √((2 : ℝ) ^ i) = √2 ^ i := by
  rw [show (2 : ℝ) ^ i = (√2 ^ i) ^ 2 by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]]
  exact Real.sqrt_sq (by positivity)

lemma one_le_sqrt_two_pow (i : ℕ) : 1 ≤ √2 ^ i :=
  one_le_pow₀ (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)

/-- `4M(r^i − 1) + M r^i ≤ 4M(r^{i+1} − 1)` for `r = √2` -/
lemma four_mul_step {M : ℝ} (hM : 0 ≤ M) (i : ℕ) :
    4 * M * (√2 ^ i - 1) + M * √2 ^ i ≤ 4 * M * (√2 ^ (i + 1) - 1) := by
  have hr : 5 / 4 ≤ √2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h1 := one_le_sqrt_two_pow i
  rw [pow_succ]
  nlinarith [mul_nonneg hM (by linarith : (0 : ℝ) ≤ √2 ^ i), mul_le_mul_of_nonneg_left hr
    (mul_nonneg hM (by linarith : (0 : ℝ) ≤ √2 ^ i))]

/-- `√|log(θ^{2^i}/C²)| ≤ √2^i √(|log θ| + 2|log C|)` -/
lemma sqrt_abs_log_q_le {θ C : ℝ} (hθ : 0 < θ) (hC : 0 < C) (i : ℕ) :
    √|Real.log (θ ^ (2 ^ i) / C ^ 2)| ≤ √2 ^ i * √(|Real.log θ| + 2 * |Real.log C|) := by
  have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  rw [← sqrt_two_pow, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h3 := abs_sub (((2 ^ i : ℕ) : ℝ) * Real.log θ) (((2 : ℕ) : ℝ) * Real.log C)
  rw [abs_mul, abs_mul] at h3
  push_cast at h3 ⊢
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i), abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
  nlinarith [abs_nonneg (Real.log C), abs_nonneg (Real.log θ)]

/-- `(1/4)^{2^i} ≤ e^{-c s²}` when `s² ≤ 8D²·2^i` and `c = log 4/(8D²)` -/
lemma quarter_pow_le {D s : ℝ} (hD : 0 < D) {i : ℕ} (hi : s ^ 2 ≤ 8 * D ^ 2 * 2 ^ i) :
    ((4 : ℝ)⁻¹) ^ (2 ^ i) ≤ Real.exp (-(Real.log 4 / (8 * D ^ 2)) * s ^ 2) := by
  have e : ((4 : ℝ)⁻¹) ^ (2 ^ i) = Real.exp (-(Real.log 4 * 2 ^ i)) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4⁻¹), ← Real.exp_nat_mul, Real.log_inv]
    push_cast; ring_nf
  rw [e]
  refine Real.exp_le_exp.2 ?_
  have hl : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hi hl.le]

/-- **The choice of the level `i`** (DDDF l. 866, "taking `i = ⌊2 log₂ s⌋`"): if `f ≤ 1` and
`f ≤ B θ^{2^i}` whenever `L + 5M√2^i < s`, then `f ≤ C e^{-c s²}`. -/
theorem tail_of_levels {M L B θ : ℝ} (hM : 0 < M) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 4⁻¹) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (s : ℝ) (f : ENNReal), 0 < s → f ≤ 1 →
      (∀ i : ℕ, L + 5 * M * √2 ^ i < s → f ≤ ENNReal.ofReal (B * θ ^ (2 ^ i))) →
      f ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2)) := by
  set D : ℝ := |L| + 5 * M
  have hD : 0 < D := by positivity
  set c : ℝ := Real.log 4 / (8 * D ^ 2)
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨(B + 1) * Real.exp (c * (2 * D) ^ 2), c, by positivity, hc, fun s f hs hf1 hf => ?_⟩
  by_cases hsD : s < 2 * D
  · refine hf1.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 ≤ Real.exp (c * (2 * D) ^ 2) * Real.exp (-c * s ^ 2) := by
      rw [← Real.exp_add]; refine Real.one_le_exp ?_
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hsD.le 2) hc.le]
    nlinarith [Real.exp_pos (c * (2 * D) ^ 2), Real.exp_pos (-c * s ^ 2)]
  push Not at hsD
  set x : ℝ := (s / (2 * D)) ^ 2
  have hx1 : 1 ≤ x := one_le_pow₀ (by rw [le_div_iff₀ (by positivity)]; linarith)
  set N : ℕ := ⌊x⌋₊
  have hN : N ≠ 0 := by
    have := Nat.floor_pos.2 hx1; omega
  set i : ℕ := Nat.log 2 N
  have hiN : 2 ^ i ≤ N := Nat.pow_log_le_self 2 hN
  have hNi : N < 2 ^ (i + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hix : (2 : ℝ) ^ i ≤ x := by
    have : ((2 ^ i : ℕ) : ℝ) ≤ N := by exact_mod_cast hiN
    push_cast at this
    exact this.trans (Nat.floor_le (by positivity))
  have hxi : x < 2 * 2 ^ i := by
    have h1 : x < N + 1 := Nat.lt_floor_add_one x
    have h2 : ((N + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast hNi
    push_cast at h2
    rw [pow_succ] at h2
    linarith
  have hr1 := one_le_sqrt_two_pow i
  have hri : √2 ^ i ≤ s / (2 * D) := by
    rw [← sqrt_two_pow]
    calc √((2 : ℝ) ^ i) ≤ √x := Real.sqrt_le_sqrt hix
      _ = s / (2 * D) := Real.sqrt_sq (by positivity)
  have hlev : L + 5 * M * √2 ^ i < s := by
    have h1 : L ≤ |L| * √2 ^ i := (le_abs_self L).trans (le_mul_of_one_le_right (abs_nonneg L) hr1)
    have h2 : D * √2 ^ i ≤ s / 2 := by
      have := mul_le_mul_of_nonneg_left hri hD.le
      rwa [mul_div_assoc', mul_comm 2 D, ← div_div, mul_div_cancel_left₀ _ hD.ne'] at this
    nlinarith
  refine (hf i hlev).trans (ENNReal.ofReal_le_ofReal ?_)
  have hs2 : s ^ 2 ≤ 8 * D ^ 2 * 2 ^ i := by
    have : x = s ^ 2 / (4 * D ^ 2) := by simp only [x]; rw [div_pow, mul_pow]; norm_num
    rw [this, div_lt_iff₀ (by positivity)] at hxi
    nlinarith
  have hq := quarter_pow_le hD hs2
  have hθq : θ ^ (2 ^ i) ≤ ((4 : ℝ)⁻¹) ^ (2 ^ i) := pow_le_pow_left₀ hθ0 hθ _
  have he : 1 ≤ Real.exp (c * (2 * D) ^ 2) := Real.one_le_exp (by positivity)
  calc B * θ ^ (2 ^ i) ≤ (B + 1) * Real.exp (-c * s ^ 2) :=
        mul_le_mul (by linarith) (hθq.trans hq) (by positivity) (by linarith)
    _ ≤ (B + 1) * Real.exp (c * (2 * D) ^ 2) * Real.exp (-c * s ^ 2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le he)
          (by linarith)

end DDDF
end LQGMetric
