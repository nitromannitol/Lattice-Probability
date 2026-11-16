import LatticeProb.Analysis.Schauder.KernelDef

/-!
# The time derivative of the Gaussian heat kernel

At positive times the heat kernel `p_t(x) = (4πt)^{-d/2} exp(-‖x‖²/(4t))` is differentiable in `t`,
with
`∂_t p_t(x) = (‖x‖²/(4t²) - d/(2t)) p_t(x)`.
This module proves that formula, and the elementary identity showing that the coefficient of
`p_t(x)` agrees with the sum of the second-derivative coefficients `x_j²/(4t²) - 1/(2t)` over the
coordinates `j`, which is what makes `p_t` solve the heat equation `∂_t p = Δ p`.
-/

namespace LatticeProb.Analysis.Schauder

open Real

noncomputable section

variable {d : ℕ}

/-- The heat kernel is differentiable in time at every positive time, with derivative
`(‖x‖²/(4t²) - d/(2t)) p_t(x)`. -/
theorem hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasDerivAt (fun s => heatKernel d s x)
      ((-(d : ℝ) / (2 * t) + ‖x‖ ^ 2 / (4 * t ^ 2)) * heatKernel d t x) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hbase : 0 < 4 * π * t := by positivity
  have hbase0 : 4 * π * t ≠ 0 := hbase.ne'
  -- the normalising factor `s ↦ (4πs)^{-d/2}`
  have h1 : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(d : ℝ) / 2))
      (4 * π * (-(d : ℝ) / 2) * (4 * π * t) ^ (-(d : ℝ) / 2 - 1)) t := by
    have hlin : HasDerivAt (fun s : ℝ => 4 * π * s) (4 * π) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * π)
    have := hlin.rpow_const (p := -(d : ℝ) / 2) (Or.inl hbase0)
    simpa [mul_assoc] using this
  -- the Gaussian factor `s ↦ exp(-‖x‖²/(4s))`
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t := by
    have hlin : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have hdiv : HasDerivAt (fun s : ℝ => -‖x‖ ^ 2 / (4 * s))
        ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2) t :=
      (hasDerivAt_const t (-‖x‖ ^ 2)).div hlin (by positivity)
    have hexp := hdiv.exp
    convert hexp using 1
    field_simp
    ring
  show HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s))) _ t
  refine (h1.mul h2).congr_deriv ?_
  unfold heatKernel
  rw [Real.rpow_sub_one hbase0]
  field_simp

/-- `Σ_j (x_j²/(4t²) − 1/(2t)) = ‖x‖²/(4t²) − d/(2t)`: the second-derivative coefficients of the
heat kernel sum to its time coefficient. -/
theorem sum_heatKernel_coeff (t : ℝ) (x : Euc d) :
    ∑ j : Fin d, ((x j) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) =
      -(d : ℝ) / (2 * t) + ‖x‖ ^ 2 / (4 * t ^ 2) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end

end LatticeProb.Analysis.Schauder
