import LatticeProb.Prob.GMSRealMeshDiameter
import LatticeProb.Walk.CellConfigInterpolationDiameter

/-! # Small adjacent-cell jumps at positive real scales -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.GMSScaledAdjacentJump

/-- On the GMS diameter-decay event, scaled representative jumps starting in
any bounded ball tend to zero uniformly over all adjacent cells and all choices
of cell representatives. -/
theorem ae_scaled_adjacent_jump_lt {μ : Measure GMSSpace} [IsProbabilityMeasure μ]
    (hL : ConnectedAlongLines μ) (hMT : MassTransport μ) (hFE : FiniteExpectation μ) :
    ∀ᵐ H ∂μ, ∀ R : ℝ, ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (p : H.1.cells → Plane), (∀ K, p K ∈ (K.1 : Set Plane)) →
      ∀ K L : H.1.cells, ε • p K ∈ closedBall (0 : Plane) R → H.1.Adj K L →
        ε * dist (p K) (p L) < δ := by
  filter_upwards [GMSRealMeshDiameter.ae_scaled_cell_diam_lt hL hMT hFE] with H hdiam
  intro R δ hδ
  let ρ := min (δ / 2) (1 / 2)
  have hρ : 0 < ρ := lt_min (half_pos hδ) (by norm_num)
  have hρδ : 2 * ρ ≤ δ := by dsimp [ρ]; have := min_le_left (δ / 2) (1 / 2); linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := min_le_right (δ / 2) (1 / 2); linarith
  obtain ⟨ε₀, hε₀, hsmall⟩ := hdiam (R + 1) ρ hρ
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hεsmall p hp K L hK hKL
  have hK' : ε • p K ∈ closedBall (0 : Plane) (R + 1) :=
    closedBall_subset_closedBall (by linarith) hK
  have hcancel (x : Plane) : ε⁻¹ • (ε • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hKd : ε * diam (K.1 : Set Plane) < ρ :=
    hsmall ε hε hεsmall (ε • p K) hK' K.1 K.2 (by simpa only [hcancel] using hp K)
  obtain ⟨z, hzK, hzL⟩ := H.2.adj_inter K L hKL
  have hdist : dist (ε • z) (ε • p K) < 1 := by
    rw [dist_smul₀, Real.norm_of_nonneg hε.le]
    exact lt_trans (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (Metric.dist_le_diam_of_mem K.1.isCompact.isBounded hzK (hp K)) hε.le) hKd) hρ1
  have hzball : ε • z ∈ closedBall (0 : Plane) (R + 1) := by
    rw [Metric.mem_closedBall] at hK ⊢
    have ht := dist_triangle (ε • z) (ε • p K) (0 : Plane)
    linarith
  have hLd : ε * diam (L.1 : Set Plane) < ρ :=
    hsmall ε hε hεsmall (ε • z) hzball L.1 L.2 (by simpa only [hcancel] using hzL)
  have hbound := CellConfigInterpolation.dist_representatives_le H.1 H.2 p hp hKL
  have hscaled := mul_le_mul_of_nonneg_left hbound hε.le
  rw [mul_add] at hscaled
  linarith

end LatticeProb.GMSScaledAdjacentJump
end
