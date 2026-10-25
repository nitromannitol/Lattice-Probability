import LatticeProb.Prob.Percolation.LatticeClusterL2

/-!
# Linear inequalities for normalized component-ball L²

The actual finite cluster-ball L² is a Euclidean norm divided by the square root
of the actual cardinality. Mathlib's norm triangle inequality therefore gives
Minkowski, including empty balls with the established zero convention.
-/

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The literal normalized sum is a finite Euclidean norm with its cardinality factor. -/
theorem componentBallL2_eq_norm_div (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r u =
      ‖(WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x) :
        EuclideanSpace ℝ (componentEuclideanBall C z r))‖ /
        Real.sqrt ((componentEuclideanBall C z r).card : ℝ) := by
  classical
  rw [componentBallL2, Real.sqrt_div (Finset.sum_nonneg (fun x _ => sq_nonneg (u x))),
    EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 2
  exact (Finset.sum_coe_sort (componentEuclideanBall C z r) (fun x => (u x) ^ 2)).symm

/-- Finite L² Minkowski on the actual component ball, including the empty case. -/
theorem componentBallL2_add_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u v : C → ℝ) :
    componentBallL2 C z r (u + v) ≤
      componentBallL2 C z r u + componentBallL2 C z r v := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div,
    componentBallL2_eq_norm_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact norm_add_le
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => v x))

/-- Scalar multiplication scales the normalized L² by the absolute scalar. -/
theorem componentBallL2_smul (C : OpenComponent ω) (z : Vertex d) (r a : ℝ)
    (u : C → ℝ) :
    componentBallL2 C z r (a • u) = |a| * componentBallL2 C z r u := by
  classical
  rw [componentBallL2_eq_norm_div, componentBallL2_eq_norm_div, ← mul_div_assoc]
  congr 1
  exact norm_smul a
    (WithLp.toLp 2 (fun x : componentEuclideanBall C z r => u x))

/-- A pointwise bound on the actual ball bounds its cardinality-normalized L². -/
theorem componentBallL2_le_of_abs_le (C : OpenComponent ω) (z : Vertex d) (r : ℝ)
    (u : C → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hu : ∀ x ∈ componentEuclideanBall C z r, |u x| ≤ b) :
    componentBallL2 C z r u ≤ b := by
  classical
  by_cases h : (componentEuclideanBall C z r).Nonempty
  · have hc : (0 : ℝ) < (componentEuclideanBall C z r).card := by
      exact_mod_cast Finset.card_pos.mpr h
    rw [componentBallL2, Real.sqrt_le_left hb]
    apply (div_le_iff₀ hc).mpr
    calc
      ∑ x ∈ componentEuclideanBall C z r, (u x) ^ 2 ≤
          ∑ _x ∈ componentEuclideanBall C z r, b ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hu x hx)
      _ = b ^ 2 * (componentEuclideanBall C z r).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · rw [componentBallL2_of_empty C z r u (Finset.not_nonempty_iff_eq_empty.mp h)]
    exact hb

/-- Constants have norm at most their absolute value even if the ball is empty. -/
theorem componentBallL2_const_le (C : OpenComponent ω) (z : Vertex d) (r c : ℝ) :
    componentBallL2 C z r (fun _ => c) ≤ |c| :=
  componentBallL2_le_of_abs_le C z r _ (abs_nonneg c) (fun _ _ => le_rfl)

end

end LatticeProb.Percolation
