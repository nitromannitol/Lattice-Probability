/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39Exp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39Tail
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.11, step 3: the stretched-exponential tail

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1700–1716: "Now set `M = N^{χ/16}` and sum over all `j` … `≼ (4C)^{β̃N^{χ/16}} N^{−β̃N^{χ/16}}` …
bounded above by `b₀e^{−b₁N^β}` … except on an event of probability at most `b₀e^{−b₁N^β}`,
`s_{K_N} ≤ τ + c N^{−χ/16} 𝔠_𝕣 e^{ξh_𝕣(0)}`."

`t39_tail_exp`: in the setting of `t39_tail` (count exponent `θ`, CONF `θ = χ/8`; kill exponent
`a`, CONF `a = α/4`), with `M = ⌈N^{θ/2}⌉`: there is `b₀` (depending on `C₁, a, θ, N₀`) such
that for every `N ≥ 1` the probability that `E` occurs and the alive steps with `n_k ≥ N` have
`∑ n_k^{−θ} > c_θ N^{−θ/2}`, `c_θ = 2^{θ+1}/(1 − 2^{−θ})`, is at most `b₀ e^{−N^{θ/2}}`
(CONF's `b₁ = 1`, `β = θ/2`; `c_θ` depends only on `θ`).
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set Finset Real
open scoped ENNReal

/-- the geometric series of the level bounds -/
theorem t39_levels_tsum_le {C₁ a : ℝ} (hC₁ : 0 ≤ C₁) (ha : 0 < a) (N M : ℕ) (hN : 1 ≤ N)
    (hM : 1 ≤ M) (hsmall : C₁ * ((N : ℝ) / 2) ^ (-a) ≤ exp (-1)) :
    ∑' j : ℕ, ENNReal.ofReal (C₁ * ((2 : ℕ) ^ (Nat.log 2 N + j) : ℕ) ^ (-a)) ^ M ≤
      ENNReal.ofReal (exp (-(M : ℝ)) / (1 - (2 : ℝ) ^ (-a))) := by
  set r : ℝ := (2 : ℝ) ^ (-a)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set ℓ₀ := Nat.log 2 N
  have h2 : (N : ℝ) / 2 ≤ 2 ^ ℓ₀ := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    rw [pow_succ] at this
    have : (N : ℝ) < 2 ^ ℓ₀ * 2 := by exact_mod_cast this
    linarith
  have hterm : ∀ j : ℕ, C₁ * ((((2 : ℕ) ^ (ℓ₀ + j) : ℕ) : ℝ)) ^ (-a) ≤ exp (-1) * r ^ j := by
    intro j
    have : ((((2 : ℕ) ^ (ℓ₀ + j) : ℕ) : ℝ)) ^ (-a) = ((2 : ℝ) ^ ℓ₀) ^ (-a) * r ^ j := by
      push_cast
      rw [pow_add, Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    rw [this, ← mul_assoc]
    gcongr
    calc C₁ * ((2 : ℝ) ^ ℓ₀) ^ (-a) ≤ C₁ * ((N : ℝ) / 2) ^ (-a) := by
          have : (0 : ℝ) < N := by exact_mod_cast hN
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (div_pos this two_pos) h2 (neg_nonpos.2 ha.le)) hC₁
      _ ≤ exp (-1) := hsmall
  have hnn : ∀ j : ℕ, 0 ≤ C₁ * ((((2 : ℕ) ^ (ℓ₀ + j) : ℕ) : ℝ)) ^ (-a) := fun j => by positivity
  have hrM0 : 0 ≤ r ^ M := pow_nonneg hr0 M
  have hrM1 : r ^ M < 1 := pow_lt_one₀ hr0 hr1 (by omega)
  calc ∑' j : ℕ, ENNReal.ofReal (C₁ * ((2 : ℕ) ^ (ℓ₀ + j) : ℕ) ^ (-a)) ^ M
      ≤ ∑' j : ℕ, ENNReal.ofReal (exp (-(M : ℝ)) * (r ^ M) ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        rw [← ENNReal.ofReal_pow (hnn j)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (C₁ * ((((2 : ℕ) ^ (ℓ₀ + j) : ℕ) : ℝ)) ^ (-a)) ^ M ≤ (exp (-1) * r ^ j) ^ M :=
              pow_le_pow_left₀ (hnn j) (hterm j) M
          _ = exp (-(M : ℝ)) * (r ^ M) ^ j := by
              rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, ← pow_mul, mul_comm j M]
              ring_nf
    _ = ENNReal.ofReal (∑' j : ℕ, exp (-(M : ℝ)) * (r ^ M) ^ j) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          ((summable_geometric_of_lt_one hrM0 hrM1).mul_left _)).symm
    _ ≤ ENNReal.ofReal (exp (-(M : ℝ)) / (1 - r)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrM0 hrM1, div_eq_mul_inv]
        gcongr
        calc r ^ M ≤ r ^ 1 := pow_le_pow_of_le_one hr0 hr1.le hM
          _ = r := pow_one r

/-- the threshold: `⌈N^{θ/2}⌉ (N/2)^{−θ}/(1 − 2^{−θ}) ≤ 2^{θ+1}/(1 − 2^{−θ}) · N^{−θ/2}` -/
theorem t39_threshold_le {θ : ℝ} (hθ : 0 < θ) (N : ℕ) (hN : 1 ≤ N) :
    ((⌈(N : ℝ) ^ (θ / 2)⌉₊ : ℕ) : ℝ) * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) ≤
      (2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ)) * (N : ℝ) ^ (-(θ / 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr1 : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (2 : ℝ) ^ (-θ) := by linarith
  have hpow1 : 1 ≤ (N : ℝ) ^ (θ / 2) := Real.one_le_rpow hN1 (by linarith)
  have hM : ((⌈(N : ℝ) ^ (θ / 2)⌉₊ : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (θ / 2) := by
    have := Nat.ceil_lt_add_one (R := ℝ) (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ (θ / 2))
    linarith
  have hsplit : ((N : ℝ) / 2) ^ (-θ) = (2 : ℝ) ^ θ * (N : ℝ) ^ (-θ) := by
    rw [Real.div_rpow hN0.le (by norm_num), Real.rpow_neg (x := 2) (by norm_num) θ,
      div_inv_eq_mul, mul_comm]
  have hcomb : (N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (-θ) = (N : ℝ) ^ (-(θ / 2)) := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [div_mul_eq_mul_div]
  gcongr ?_ / _
  calc ((⌈(N : ℝ) ^ (θ / 2)⌉₊ : ℕ) : ℝ) * ((N : ℝ) / 2) ^ (-θ)
      ≤ 2 * (N : ℝ) ^ (θ / 2) * ((N : ℝ) / 2) ^ (-θ) := by gcongr
    _ = (2 : ℝ) ^ (θ + 1) * ((N : ℝ) ^ (θ / 2) * (N : ℝ) ^ (-θ)) := by
        rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_one]; ring
    _ = (2 : ℝ) ^ (θ + 1) * (N : ℝ) ^ (-(θ / 2)) := by rw [hcomb]

end CONF
end LQGMetric
