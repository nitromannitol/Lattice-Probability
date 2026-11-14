/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateLinear at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateMono

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_log_le_two_sqrt (s : ℝ) (hs : 0 < s) :
    Real.log s ≤ 2 * Real.sqrt s := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h := Real.log_le_sub_one_of_pos hsqrt
  rw [Real.log_sqrt hs.le] at h
  linarith

theorem pt_dist_rate_ge_sqrt (s : ℝ) (hs : 3 ≤ s) :
    s * Real.sqrt s / 2 ≤ s ^ 2 / Real.log s := by
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log s := Real.log_pos (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0.le
  apply (le_div_iff₀ hlog).2
  calc
    (s * Real.sqrt s / 2) * Real.log s ≤
        (s * Real.sqrt s / 2) * (2 * Real.sqrt s) :=
      mul_le_mul_of_nonneg_left (pt_dist_log_le_two_sqrt s hs0)
        (by positivity)
    _ = s ^ 2 := by nlinarith [hsq]

theorem pt_dist_rate_linear_large (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    ∃ H : ℝ, 3 ≤ H ∧
      ∀ s : ℝ, H ≤ s →
        M * s ≤ a * (s ^ 2 / Real.log s) := by
  let H : ℝ := max 3 ((2 * M / a) ^ 2)
  have hH : 3 ≤ H := le_max_left _ _
  refine ⟨H, hH, ?_⟩
  intro s hHs
  have hs3 : 3 ≤ s := hH.trans hHs
  have hs0 : 0 < s := by linarith
  have hq0 : 0 ≤ 2 * M / a := by positivity
  have hq : (2 * M / a) ^ 2 ≤ s :=
    (le_max_right _ _).trans hHs
  have hsqrt : 2 * M / a ≤ Real.sqrt s := by
    nlinarith [Real.sq_sqrt hs0.le, Real.sqrt_nonneg s]
  calc
    M * s = (a * s / 2) * (2 * M / a) := by field_simp
    _ ≤ (a * s / 2) * Real.sqrt s :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = a * (s * Real.sqrt s / 2) := by ring
    _ ≤ a * (s ^ 2 / Real.log s) :=
      mul_le_mul_of_nonneg_left (pt_dist_rate_ge_sqrt s hs3) ha.le

theorem pt_dist_rate_boost_large (a α : ℝ) (ha : 0 < a) (hα : 0 < α) :
    ∃ H : ℝ, 3 ≤ H ∧
      ∀ L : ℝ, H ≤ L → ∀ k : ℕ,
        (a / 2) * (L ^ 2 / Real.log L) + Real.log 8 * (k : ℝ) ≤
          a * ((L + α * (k : ℝ)) ^ 2 /
            Real.log (L + α * (k : ℝ))) := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  obtain ⟨H, hH, hlarge⟩ :=
    pt_dist_rate_linear_large a (2 * Real.log 8 / α) ha (by positivity)
  refine ⟨H, hH, ?_⟩
  intro L hL k
  let s : ℝ := L + α * (k : ℝ)
  have hLs : L ≤ s := by
    dsimp [s]
    nlinarith [mul_nonneg hα.le (Nat.cast_nonneg k)]
  have hHs : H ≤ s := hL.trans hLs
  have hmono := mul_le_mul_of_nonneg_left
    (pt_dist_log_rate_mono L s (hH.trans hL) hLs) ha.le
  have hlin := hlarge s hHs
  have hk : 2 * Real.log 8 * (k : ℝ) ≤
      (2 * Real.log 8 / α) * s := by
    dsimp [s]
    have he : (2 * Real.log 8 / α) * α = 2 * Real.log 8 := by
      field_simp
    nlinarith [mul_nonneg (show 0 ≤ 2 * Real.log 8 / α by positivity)
      (show 0 ≤ L by linarith)]
  dsimp [s] at hmono hlin hk ⊢
  nlinarith

end SupercriticalLQGUniqueness.B2.DG20Pt
