/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSqrtAbsorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBQuantileSandwich

 


set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneB_exp_sqrt_le_dyadic_power (K δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ,
      Real.exp (K * Real.sqrt (m : ℝ)) ≤
        A * (2 : ℝ) ^ (δ * (m : ℝ)) := by
  let β : ℝ := δ * Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hβ : 0 < β := mul_pos hδ hlog2
  refine ⟨Real.exp (K ^ 2 / (4 * β)), Real.exp_pos _, ?_⟩
  intro m
  let t : ℝ := Real.sqrt m
  have ht : t ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
  have hlin : K * t ≤ β * (m : ℝ) + K ^ 2 / (4 * β) := by
    rw [← ht]
    have hden : 0 < 4 * β := by positivity
    have heq : β * t ^ 2 + K ^ 2 / (4 * β) =
        (4 * β ^ 2 * t ^ 2 + K ^ 2) / (4 * β) := by
      field_simp
    rw [heq]
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (2 * β * t - K)]
  have he : Real.exp (K * t) ≤
      Real.exp (K ^ 2 / (4 * β)) * Real.exp (β * (m : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow : Real.exp (β * (m : ℝ)) = (2 : ℝ) ^ (δ * (m : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [β]
    ring
  simpa only [t, hpow] using he

end SupercriticalLQGUniqueness.B2.DG20Conc
