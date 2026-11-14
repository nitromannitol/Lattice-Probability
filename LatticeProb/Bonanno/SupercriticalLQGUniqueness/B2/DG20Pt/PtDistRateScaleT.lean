/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateScaleT at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateReal

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_scale_rate_real_sum_large
    (Cnet : ℕ) (a₀ a₁ b₀ b₁ D σ2 ζ R ξ : ℝ)
    (ha₀ : 0 ≤ a₀) (ha₁ : 0 < a₁)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 < b₁)
    (hD : 0 ≤ D) (hσ2 : 0 < σ2)
    (hζ : 0 < ζ) (hR : 0 < R) (hξ : 0 < ξ) :
    ∃ H : ℝ, 3 ≤ H ∧ ∀ T : ℝ, Real.exp H ≤ T → ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
        ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
          ((Real.log T + ζ * (k : ℝ)) / (R * ξ)) ≤
        2 * ((Cnet : ℝ) * a₀) *
          Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
        2 * ((Cnet : ℝ) * b₀) *
          Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
        2 * D * Real.exp (-(1 / (2 * σ2 * (R * ξ) ^ 2) / 2) *
          (Real.log T) ^ 2) := by
  let α : ℝ := (ζ / 2) * Real.log 2
  let b : ℝ := 1 / (2 * σ2 * (R * ξ) ^ 2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨H, hH, hsum⟩ :=
    pt_dist_three_rate_sum_large ((Cnet : ℝ) * a₀) ((Cnet : ℝ) * b₀)
      D a₁ b₁ b α ζ (by positivity) (by positivity) hD ha₁ hb₁ hb hα hζ
  refine ⟨H, hH, ?_⟩
  intro T hT n
  have hT0 : 0 < T := (Real.exp_pos H).trans_le hT
  have hlogT : H ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hT
  have hlog (k : ℕ) :
      Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) =
        Real.log T + α * (k : ℝ) := by
    rw [Real.log_mul hT0.ne' (by positivity), Real.log_rpow (by norm_num)]
    dsimp [α]
    ring
  have hgauss (k : ℕ) :
      -((Real.log T + ζ * (k : ℝ)) / (R * ξ)) ^ 2 / (2 * σ2) =
        -b * (Real.log T + ζ * (k : ℝ)) ^ 2 := by
    dsimp [b]
    field_simp
  have hterm (k : ℕ) :
      ptDistScaleRateReal Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k
        ((Real.log T + ζ * (k : ℝ)) / (R * ξ)) =
      (((Cnet : ℝ) * a₀) * (4 : ℝ) ^ k * Real.exp
          (-a₁ * ((Real.log T + α * (k : ℝ)) ^ 2 /
            Real.log (Real.log T + α * (k : ℝ)))) +
       ((Cnet : ℝ) * b₀) * (4 : ℝ) ^ k * Real.exp
          (-b₁ * ((Real.log T + α * (k : ℝ)) ^ 2 /
            Real.log (Real.log T + α * (k : ℝ))))) +
       D * (4 : ℝ) ^ k * Real.exp
          (-b * (Real.log T + ζ * (k : ℝ)) ^ 2) := by
    dsimp [ptDistScaleRateReal]
    rw [hlog k, hgauss k]
    ring
  simpa only [hterm, b] using
    hsum (Real.log T) hlogT n

end SupercriticalLQGUniqueness.B2.DG20Pt
