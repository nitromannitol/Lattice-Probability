/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2FlipReal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2FlipVertex

 








set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

open WiredConductances

theorem flipBound_le_pow {A S : ℝ} (hA : 0 ≤ A) (hS : 0 < S) :
    flipBound A S ≤ A / (S ^ 2 * Real.sqrt S) := by
  refine (flipBound_le_poly' hA hS).trans ?_
  have h1 : S ^ 2 ≤ S * (1 + S) := by nlinarith
  have h2 : Real.sqrt S ≤ Real.sqrt (1 + S) := Real.sqrt_le_sqrt (by linarith)
  have hsS : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  rw [← div_eq_mul_inv, div_div]
  apply div_le_div_of_nonneg_left hA (by positivity)
  exact mul_le_mul h1 h2 hsS.le (by positivity)

theorem pow_bound_anti {A S S₀ : ℝ} (hA : 0 ≤ A) (hS₀ : 0 < S₀) (hS : S₀ ≤ S) :
    A / (S ^ 2 * Real.sqrt S) ≤ A / (S₀ ^ 2 * Real.sqrt S₀) := by
  apply div_le_div_of_nonneg_left hA (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hS₀.le hS 2) (Real.sqrt_le_sqrt hS)
    (Real.sqrt_nonneg _) (by positivity)

theorem exp_bound_mono {A S S₁ : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hS₁ : S ≤ S₁) :
    Real.exp (-(A / (1 + S))) ≤ Real.exp (-(A / (1 + S₁))) := by
  rw [Real.exp_le_exp, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hA (by linarith) (by linarith)

 
theorem exp_neg_le_pow_ten {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ (Nat.factorial 10 : ℝ) / x ^ 10 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 10
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

 
theorem sum_Ico_inv_pow_five_le {J M : ℕ} (hJ : 1 ≤ J) :
    ∑ j ∈ Finset.Ico (J + 1) M, (1 : ℝ) / (j : ℝ) ^ 5 ≤ 1 / (J : ℝ) ^ 4 := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [Finset.sum_Ico_eq_sum_range]
  set g : ℕ → ℝ := fun i => 1 / ((J : ℝ) + i)
  have hterm : ∀ i ∈ Finset.range (M - (J + 1)), (1 : ℝ) / (((J + 1 + i : ℕ) : ℝ)) ^ 5 ≤
      (1 / (J : ℝ) ^ 3) * (g i - g (i + 1)) := by
    intro i _
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [g]
    push_cast
    rw [show (1 : ℝ) / ((J : ℝ) + i) - 1 / ((J : ℝ) + (i + 1)) =
      1 / (((J : ℝ) + i) * ((J : ℝ) + i + 1)) by field_simp; ring]
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have h1 : (J : ℝ) ^ 3 ≤ ((J : ℝ) + 1 + i) ^ 3 := pow_le_pow_left₀ hJ0.le (by linarith) 3
    have h2 : ((J : ℝ) + i) * ((J : ℝ) + i + 1) ≤ ((J : ℝ) + 1 + i) ^ 2 := by nlinarith
    calc (J : ℝ) ^ 3 * (((J : ℝ) + i) * ((J : ℝ) + i + 1))
        ≤ ((J : ℝ) + 1 + i) ^ 3 * ((J : ℝ) + 1 + i) ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((J : ℝ) + 1 + i) ^ 5 := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub']
  have hg0 : g 0 = 1 / (J : ℝ) := by simp [g]
  have hgn : 0 ≤ g (M - (J + 1)) := by simp only [g]; positivity
  calc 1 / (J : ℝ) ^ 3 * (g 0 - g (M - (J + 1))) ≤ 1 / (J : ℝ) ^ 3 * (1 / (J : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hg0]; linarith
    _ = 1 / (J : ℝ) ^ 4 := by field_simp

end SupercriticalLQGUniqueness.B2.QPos
