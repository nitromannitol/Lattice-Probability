/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateScaleENN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateScaleT

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_scale_rate_sum_large
    (Cnet : ℕ) (a₀ a₁ b₀ b₁ D σ2 ζ R ξ : ℝ)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 < a₁)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 < b₁)
    (hD : 0 ≤ D) (hσ2 : 0 < σ2)
    (hζ : 0 < ζ) (hR : 0 < R) (hξ : 0 < ξ) :
    ∃ H : ℝ, 3 ≤ H ∧ ∀ T : ℝ, Real.exp H ≤ T → ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
        ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
          ((Real.log T + ζ * (k : ℝ)) / (R * ξ)) ≤
      ENNReal.ofReal
        (2 * ((Cnet : ℝ) * a₀) *
          Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
         2 * ((Cnet : ℝ) * b₀) *
          Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
         2 * D * Real.exp (-(1 / (2 * σ2 * (R * ξ) ^ 2) / 2) *
           (Real.log T) ^ 2)) := by
  obtain ⟨H, hH, hsum⟩ :=
    pt_dist_scale_rate_real_sum_large Cnet a₀ a₁ b₀ b₁ D σ2 ζ R ξ
      ha₀ ha₁ hb₀ hb₁ hD hσ2 hζ hR hξ
  refine ⟨H, hH, ?_⟩
  intro T hT n
  calc
    ∑ k ∈ Finset.range n,
        ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
          ((Real.log T + ζ * (k : ℝ)) / (R * ξ)) =
      ∑ k ∈ Finset.range n,
        ENNReal.ofReal (ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
          ((Real.log T + ζ * (k : ℝ)) / (R * ξ))) := by
      apply Finset.sum_congr rfl
      intro k _
      exact pt_dist_scale_rate_eq_ofReal Cnet ha₀ hb₀ hD k _
    _ = ENNReal.ofReal
      (∑ k ∈ Finset.range n,
        ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
          ((Real.log T + ζ * (k : ℝ)) / (R * ξ))) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun k _ => pt_dist_scale_rate_real_nonneg Cnet ha₀ hb₀ hD k _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hsum T hT n)

end SupercriticalLQGUniqueness.B2.DG20Pt
