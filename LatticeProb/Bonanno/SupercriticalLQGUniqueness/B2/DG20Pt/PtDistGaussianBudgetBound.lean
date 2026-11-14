/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianBudgetAlgebra

 


set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_gaussian_budget_real_as_geometric
    (ξ Q ζ L β T C Clam lam : ℝ) (n k₀ : ℕ) :
    let α := ξ * Q - 3 * ζ - 2 * β
    let q := (2 : ℝ) ^ (-α)
    let A := T ^ 2 * Real.exp L * lam
    ptDistLocalGaussianBudgetReal ξ Q ζ L β T C Clam lam n k₀ =
      ptDistGeometricTwoArmReal q A C Clam n k₀ := by
  dsimp
  unfold ptDistLocalGaussianBudgetReal ptDistGeometricTwoArmReal
  dsimp
  simp_rw [pt_dist_dyadic_power_eq_geometric]
  ring

theorem pt_dist_gaussian_budget_le_uniform
    (ξ Q ζ L β T C Clam lam : ℝ) (n k₀ : ℕ)
    (hkn : k₀ ≤ n) (hα : 0 < ξ * Q - 3 * ζ - 2 * β)
    (hC : 0 ≤ C) (hClam : 0 ≤ Clam) (hlam : 0 ≤ lam) :
    let α := ξ * Q - 3 * ζ - 2 * β
    let q := (2 : ℝ) ^ (-α)
    let K := 2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)
    ptDistLocalGaussianBudget ξ Q ζ L β T C Clam lam n k₀ ≤
      ENNReal.ofReal
        (K * T ^ 2 * Real.exp L * lam * q ^ k₀) := by
  dsimp
  let α : ℝ := ξ * Q - 3 * ζ - 2 * β
  let q : ℝ := (2 : ℝ) ^ (-α)
  let A : ℝ := T ^ 2 * Real.exp L * lam
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by dsimp [α] at hα ⊢; linarith)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [pt_dist_local_gaussian_budget_eq_ofReal ξ Q ζ L β T C Clam lam n k₀ hC hClam hlam]
  have heq := pt_dist_gaussian_budget_real_as_geometric
    ξ Q ζ L β T C Clam lam n k₀
  have hbound := pt_dist_geometric_two_arm_real_le q A C Clam n k₀ hkn
    hq0 hq1 hA hC hClam
  have hreal : ptDistLocalGaussianBudgetReal ξ Q ζ L β T C Clam lam n k₀ ≤
      (2 * Clam + 4 + C + 6 * (2 + C) / (1 - q)) *
        T ^ 2 * Real.exp L * lam * q ^ k₀ := by
    rw [heq]
    dsimp [q, A] at hbound ⊢
    nlinarith [hbound]
  exact ENNReal.ofReal_le_ofReal hreal

end SupercriticalLQGUniqueness.B2.DG20Pt
