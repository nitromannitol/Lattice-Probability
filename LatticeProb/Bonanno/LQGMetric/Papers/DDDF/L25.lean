/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L25 at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# DDDF Lemma 25 (weakly multiplicative sequences have an exponent)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1221–1258 (`Lem:RealAnalysis`; blueprint node DDDF.L25): if `λ_n > 0` and
`e^{-C√k} λ_n λ_k ≤ λ_{n+k} ≤ e^{C√k} λ_n λ_k` for all `n, k ≥ 1`, then there is `ρ > 0` with
`λ_n = ρ^{n + O(√n)}`, i.e. `|log λ_n − n log ρ| ≤ C' √n` for `n ≥ 1`.

We follow DDDF's proof for `a_n = log λ_n`: along the dyadic subsequence, `a_{2^{j+1}} = 2 a_{2^j}
+ e_j` with `|e_j| ≤ C 2^{j/2}` (l. 1233–1236), so `a_{2^j}/2^j` converges geometrically fast to
some `r = log ρ` and `|a_{2^j} − 2^j r| ≤ D 2^{j/2}` (l. 1237–1240, (eq:IneDya)); then the dyadic
induction `n = 2^k + n_k`, `n_k < 2^k`, with `C_3² ≥ (C_1 + C_2)² + (C_1 + C_2) C_3` (l. 1241–1257).
DDDF only write the upper bound ("the proof of the lower bound is similar", l. 1258); we run the
induction on `|a_n − n r|`, which proves both bounds at once (`C_3 = max (3A) D`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Real

namespace LQGMetric
namespace DDDF
namespace L25

/-- dyadic step: `|a_{2^j} − 2^j r| ≤ D √2^j` for some `r` and `D` -/
theorem dyadic {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → |a (n + k) - a n - a k| ≤ C * √(k : ℝ)) :
    ∃ r D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, |a (2 ^ j) - 2 ^ j * r| ≤ D * √2 ^ j := by
  set q : ℝ := √2 with hq
  have hq2 : q ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq1 : 1 < q := by rw [hq, Real.lt_sqrt (by norm_num)]; norm_num
  have hq0 : 0 < q := by linarith
  have hsq : ∀ j : ℕ, √(((2 ^ j : ℕ) : ℝ)) = q ^ j := by
    intro j
    rw [show (((2 ^ j : ℕ)) : ℝ) = (q ^ j) ^ 2 by push_cast; rw [← pow_mul, mul_comm,
      pow_mul, hq2]]
    exact Real.sqrt_sq (by positivity)
  set u : ℕ → ℝ := fun j => a (2 ^ j) / 2 ^ j with hu
  -- `|u_{j+1} − u_j| ≤ (C/2) q⁻ʲ`
  have hstep : ∀ j, dist (u j) (u (j + 1)) ≤ C / 2 * q⁻¹ ^ j := by
    intro j
    have h1 := h (2 ^ j) (2 ^ j) (Nat.one_le_two_pow) (Nat.one_le_two_pow)
    rw [hsq j, ← two_mul, ← pow_succ'] at h1
    rw [Real.dist_eq, hu]
    simp only
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have e : a (2 ^ j) / 2 ^ j - a (2 ^ (j + 1)) / 2 ^ (j + 1) =
        -(a (2 ^ (j + 1)) - a (2 ^ j) - a (2 ^ j)) / 2 ^ (j + 1) := by
      rw [pow_succ]; field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (j + 1)),
      div_le_iff₀ (by positivity)]
    refine h1.trans (le_of_eq ?_)
    rw [inv_pow, pow_succ, show (2 : ℝ) ^ j = (q ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, hq2]]
    field_simp
  have hr1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  obtain ⟨r, hr⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hr1 hstep)
  have hD := dist_le_of_le_geometric_of_tendsto _ _ hr1 hstep hr
  set D := C / 2 / (1 - q⁻¹) with hDdef
  have hD0 : 0 ≤ D := div_nonneg (by linarith) (by linarith)
  refine ⟨r, D, hD0, fun j => ?_⟩
  have hj := hD j
  rw [Real.dist_eq, hu] at hj
  simp only at hj
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have e : a (2 ^ j) - 2 ^ j * r = 2 ^ j * (a (2 ^ j) / 2 ^ j - r) := by field_simp
  rw [e, abs_mul, abs_of_pos h2j]
  calc (2 : ℝ) ^ j * |a (2 ^ j) / 2 ^ j - r| ≤ 2 ^ j * (C / 2 * q⁻¹ ^ j / (1 - q⁻¹)) :=
        mul_le_mul_of_nonneg_left hj h2j.le
    _ = D * q ^ j := by
        rw [hDdef, show (2 : ℝ) ^ j = q ^ j * q ^ j by
          rw [← mul_pow, ← sq, hq2]]
        rw [inv_pow]
        field_simp

/-- the additive form of DDDF Lemma 25 -/
theorem additive {a : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → |a (n + k) - a n - a k| ≤ C * √(k : ℝ)) :
    ∃ r C' : ℝ, ∀ n : ℕ, 1 ≤ n → |a n - n * r| ≤ C' * √(n : ℝ) := by
  obtain ⟨r, D, hD0, hdy⟩ := dyadic hC h
  set A := D + C with hA
  have hA0 : 0 ≤ A := by positivity
  set C3 := max (3 * A) D with hC3
  have hC3A : 3 * A ≤ C3 := le_max_left _ _
  have hC3D : D ≤ C3 := le_max_right _ _
  refine ⟨r, C3, ?_⟩
  have hsq : ∀ j : ℕ, √((2 : ℝ) ^ j) = √2 ^ j := fun j => by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by norm_num)]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    set k := Nat.log 2 n
    have hk1 : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hk2 : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    set m := n - 2 ^ k with hm
    have hnm : n = m + 2 ^ k := by omega
    have hmk : m < 2 ^ k := by rw [pow_succ] at hk2; omega
    set s : ℝ := √2 ^ k with hs
    have hs2 : s ^ 2 = 2 ^ k := by rw [hs, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
    have hs0 : 0 ≤ s := by positivity
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · have e : n = 2 ^ k := by omega
      have := hdy k
      rw [e]; push_cast
      refine this.trans ?_
      rw [hsq k]
      exact mul_le_mul_of_nonneg_right hC3D (by positivity)
    · have h1 := h m (2 ^ k) hm0 Nat.one_le_two_pow
      have h2 := ih m (by omega) hm0
      have h3 := hdy k
      rw [← hnm] at h1
      push_cast at h1
      rw [hsq k, ← hs] at h1
      have hmR : (m : ℝ) ≤ s ^ 2 := by rw [hs2]; exact_mod_cast hmk.le
      have hnR : (n : ℝ) = m + s ^ 2 := by rw [hs2]; exact_mod_cast hnm
      have hsm : √(m : ℝ) ≤ s := by
        rw [Real.sqrt_le_left hs0]; exact hmR
      have htri : |a n - n * r| ≤ A * s + C3 * √(m : ℝ) := by
        have e : a n - n * r = (a n - a m - a (2 ^ k)) + (a m - m * r) +
            (a (2 ^ k) - 2 ^ k * r) := by rw [hnR, hs2]; ring
        rw [e]
        have t1 := abs_add_le (a n - a m - a (2 ^ k) + (a m - m * r)) (a (2 ^ k) - 2 ^ k * r)
        have t2 := abs_add_le (a n - a m - a (2 ^ k)) (a m - m * r)
        have t3 : A * s = D * s + C * s := by rw [hA]; ring
        linarith
      refine htri.trans ?_
      -- `(A s + C₃ √m)² ≤ C₃² (s² + m)`
      have hC30 : 0 ≤ C3 := le_trans (by positivity) hC3A
      have hmr0 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
      have hsqm : √(m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg _)
      rw [hnR, show C3 * √((m : ℝ) + s ^ 2) = √(C3 ^ 2 * ((m : ℝ) + s ^ 2)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC30]]
      apply Real.le_sqrt_of_sq_le
      have hq : A ^ 2 + 2 * A * C3 ≤ C3 ^ 2 := by nlinarith
      have h4 : 2 * A * C3 * s * √(m : ℝ) ≤ 2 * A * C3 * s ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsm (by positivity : 0 ≤ 2 * A * C3 * s)
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg s)]

end L25

/-- **DDDF Lemma 25** (`Lem:RealAnalysis`, tightness.tex l. 1221–1258): a positive sequence with
`e^{-C√k} λ_n λ_k ≤ λ_{n+k} ≤ e^{C√k} λ_n λ_k` for `n, k ≥ 1` satisfies `λ_n = ρ^{n + O(√n)}`
for some `ρ > 0`, in the form `|log λ_n − n log ρ| ≤ C' √n` for all `n ≥ 1`. -/
theorem dddf_lemma25 {lam : ℕ → ℝ} (hpos : ∀ n, 1 ≤ n → 0 < lam n) {C : ℝ}
    (h : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      exp (-(C * √(k : ℝ))) * lam n * lam k ≤ lam (n + k) ∧
        lam (n + k) ≤ exp (C * √(k : ℝ)) * lam n * lam k) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C' : ℝ, ∀ n : ℕ, 1 ≤ n →
      |Real.log (lam n) - n * Real.log ρ| ≤ C' * √(n : ℝ) := by
  -- `C ≥ 0` is forced (`n = k = 1`), but we just use `|C|`
  have hadd : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      |Real.log (lam (n + k)) - Real.log (lam n) - Real.log (lam k)| ≤ |C| * √(k : ℝ) := by
    intro n k hn hk
    obtain ⟨h1, h2⟩ := h n k hn hk
    have hn0 := hpos n hn
    have hk0 := hpos k hk
    have hnk0 := hpos (n + k) (by omega)
    have l1 := Real.log_le_log (by positivity) h1
    have l2 := Real.log_le_log hnk0 h2
    rw [Real.log_mul (by positivity) hk0.ne', Real.log_mul (by positivity) hn0.ne',
      Real.log_exp] at l1 l2
    have hCs : C * √(k : ℝ) ≤ |C| * √(k : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
    have hCs' : -(C * √(k : ℝ)) ≤ |C| * √(k : ℝ) := by
      rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs C) (Real.sqrt_nonneg _)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨r, C', hr⟩ := L25.additive (a := fun n => Real.log (lam n)) (abs_nonneg C) hadd
  exact ⟨exp r, exp_pos r, C', fun n hn => by rw [Real.log_exp]; exact hr n hn⟩

end DDDF
end LQGMetric
