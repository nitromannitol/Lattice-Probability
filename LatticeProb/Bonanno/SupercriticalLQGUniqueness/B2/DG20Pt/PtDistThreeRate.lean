/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistThreeRate at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateSum

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_three_rate_sum_large
    (A B D a₁ b₁ b α β : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (hb : 0 < b)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ H : ℝ, 3 ≤ H ∧ ∀ L : ℝ, H ≤ L → ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
        ((A * (4 : ℝ) ^ k * Real.exp
          (-a₁ * ((L + α * (k : ℝ)) ^ 2 /
            Real.log (L + α * (k : ℝ)))) +
         B * (4 : ℝ) ^ k * Real.exp
          (-b₁ * ((L + α * (k : ℝ)) ^ 2 /
            Real.log (L + α * (k : ℝ))))) +
         D * (4 : ℝ) ^ k * Real.exp
          (-b * (L + β * (k : ℝ)) ^ 2)) ≤
        2 * A * Real.exp (-(a₁ / 2) * (L ^ 2 / Real.log L)) +
        2 * B * Real.exp (-(b₁ / 2) * (L ^ 2 / Real.log L)) +
        2 * D * Real.exp (-(b / 2) * L ^ 2) := by
  obtain ⟨H₁, hH₁, hsum₁⟩ := pt_dist_rate_sum_large a₁ α ha₁ hα
  obtain ⟨H₂, hH₂, hsum₂⟩ := pt_dist_rate_sum_large b₁ α hb₁ hα
  obtain ⟨H₃, hH₃, hsum₃⟩ := pt_dist_gaussian_sum_large b β hb hβ
  let H := max H₁ (max H₂ H₃)
  refine ⟨H, hH₁.trans (le_max_left _ _), ?_⟩
  intro L hL n
  have hL₁ : H₁ ≤ L := (le_max_left _ _).trans hL
  have hL₂ : H₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL₃ : H₃ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have h₁ := mul_le_mul_of_nonneg_left (hsum₁ L hL₁ n) hA
  have h₂ := mul_le_mul_of_nonneg_left (hsum₂ L hL₂ n) hB
  have h₃ := mul_le_mul_of_nonneg_left (hsum₃ L hL₃ n) hD
  simp only [Finset.mul_sum] at h₁ h₂ h₃
  simpa only [Finset.sum_add_distrib, mul_assoc, mul_left_comm, mul_comm] using
    (add_le_add (add_le_add h₁ h₂) h₃)

end SupercriticalLQGUniqueness.B2.DG20Pt
