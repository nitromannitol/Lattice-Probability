/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.PowerComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.Asymptotic

 

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace SupercriticalLQGUniqueness.B2.QPos

 
lemma shifted_exp_power_le {α δ ε s C : ℝ}
    (hgap : s < (ε - δ) * Real.log 2) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (s * (n : ℝ) + C * Real.sqrt ((n - 3 : ℕ) : ℝ)) *
          (2 : ℝ) ^ (-(α - δ) * ((n - 3 : ℕ) : ℝ)) ≤
        (2 : ℝ) ^ (-(α - ε) * (n : ℝ)) := by
  let θ := ((ε - δ) * Real.log 2 - s) / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have herror := sqrt_error_eventually_le C (3 * |α - δ| * Real.log 2) θ hθ 3
  filter_upwards [herror, eventually_ge_atTop (3 : ℕ)] with n he hn
  have hm : (((n - 3 : ℕ) : ℝ)) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub hn]; norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 3 * (α - δ) * Real.log 2 ≤ 3 * |α - δ| * Real.log 2 := by
    gcongr; exact le_abs_self _
  have hmain : s * (n : ℝ) + C * Real.sqrt ((n - 3 : ℕ) : ℝ) -
      (α - δ) * (((n - 3 : ℕ) : ℝ)) * Real.log 2 ≤
      -(α - ε) * (n : ℝ) * Real.log 2 := by
    rw [hm]
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hθn : θ * (n : ℝ) ≤ ((ε - δ) * Real.log 2 - s) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (by dsimp [θ]; linarith) hn0
    have ht : C * Real.sqrt ((n - 3 : ℕ) : ℝ) +
        3 * (α - δ) * Real.log 2 ≤
        ((ε - δ) * Real.log 2 - s) * (n : ℝ) := by
      calc
        _ ≤ C * Real.sqrt ((n - 3 : ℕ) : ℝ) +
            3 * |α - δ| * Real.log 2 := by linarith only [hD]
        _ ≤ θ * (n : ℝ) := he
        _ ≤ _ := hθn
    calc
      s * (n : ℝ) + C * Real.sqrt ((n : ℝ) - 3) -
          (α - δ) * ((n : ℝ) - 3) * Real.log 2 =
        -(α - ε) * (n : ℝ) * Real.log 2 +
          (C * Real.sqrt ((n : ℝ) - 3) + 3 * (α - δ) * Real.log 2 -
            ((ε - δ) * Real.log 2 - s) * (n : ℝ)) := by ring
      _ ≤ -(α - ε) * (n : ℝ) * Real.log 2 := by
        rw [hm] at ht
        linarith only [ht]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith only [hmain])

 

lemma shifted_quantile_le_power
    (a b c : ℕ → ℝ) {α δ ε s C : ℝ}
    (hgap : s < (ε - δ) * Real.log 2)
    (hb : ∀ n, b n ≤ Real.exp (C * Real.sqrt (n : ℝ)))
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ a n)
    (ha : ∀ᶠ n : ℕ in atTop,
      a n ≤ (2 : ℝ) ^ (-(α - δ) * (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (s * (n : ℝ)) * b (n - 3) * c (n - 3) ≤
        (2 : ℝ) ^ (-(α - ε) * (n : ℝ)) := by
  have has := (tendsto_sub_atTop_nat 3).eventually ha
  filter_upwards [has, shifted_exp_power_le hgap] with n han hpow
  have hbc : b (n-3) * c (n-3) ≤
      Real.exp (C * Real.sqrt (((n-3 : ℕ) : ℝ))) *
        (2 : ℝ) ^ (-(α - δ) * (((n-3 : ℕ) : ℝ))) := by
    exact mul_le_mul (hb _) ((hc _).2.trans han) (hc _).1 (Real.exp_pos _).le
  calc
    Real.exp (s * (n : ℝ)) * b (n - 3) * c (n - 3) =
        Real.exp (s * (n : ℝ)) * (b (n-3) * c (n-3)) := by ring
    _ ≤ Real.exp (s * (n : ℝ)) *
        (Real.exp (C * Real.sqrt (((n-3 : ℕ) : ℝ))) *
          (2 : ℝ) ^ (-(α - δ) * (((n-3 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hbc (Real.exp_pos _).le
    _ = Real.exp (s * (n : ℝ) + C * Real.sqrt (((n-3 : ℕ) : ℝ))) *
        (2 : ℝ) ^ (-(α - δ) * (((n-3 : ℕ) : ℝ))) := by rw [Real.exp_add]; ring
    _ ≤ _ := hpow

end SupercriticalLQGUniqueness.B2.QPos
