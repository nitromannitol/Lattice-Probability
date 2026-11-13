/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.Asymptotic at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.QPos

lemma sqrt_nat_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change (n : ℝ) ^ (-(1 / 2 : ℝ)) = Real.sqrt (n : ℝ) / (n : ℝ)
  rw [show (-(1 / 2 : ℝ)) = 1 / 2 - 1 by ring, Real.rpow_sub hn',
    Real.rpow_one, Real.sqrt_eq_rpow]

lemma sqrt_nat_sub_div_nat_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.sqrt ((n - k : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero ?_ ?_ sqrt_nat_div_nat_tendsto_zero
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · subst n; simp
    · exact div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.sub_le n k) :
          (((n-k : ℕ) : ℝ)) ≤ (n : ℝ)))
        (Nat.cast_nonneg n)

lemma sqrt_error_eventually_le (C D ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      C * Real.sqrt ((n - k : ℕ) : ℝ) + D ≤ ε * (n : ℝ) := by
  have h1 := (sqrt_nat_sub_div_nat_tendsto_zero k).const_mul C
  have h2 : Tendsto (fun n : ℕ => D / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have h : Tendsto (fun n : ℕ =>
      (C * Real.sqrt ((n-k : ℕ) : ℝ) + D) / (n : ℝ)) atTop (𝓝 0) := by
    convert h1.add h2 using 1
    · funext n; ring
    · simp
  filter_upwards [h.eventually (eventually_lt_nhds hε),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  exact (div_le_iff₀ (by exact_mod_cast hn0 : (0 : ℝ) < n)).mp hn.le

end SupercriticalLQGUniqueness.B2.QPos
