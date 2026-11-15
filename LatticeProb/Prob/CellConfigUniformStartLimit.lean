import LatticeProb.Prob.CellConfigUniformStartTransfer

/-! # Uniform convergence for all containing cells -/

set_option autoImplicit false

noncomputable section

open Set Metric
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigContainingCell

/-- Uniform selected-cell convergence extends to all containing cells when
scaled cell diameters vanish uniformly and the target is uniformly continuous. -/
theorem all_containing_cell_uniform_convergence {Y : Type*} [PseudoMetricSpace Y]
    (H : GMSSpace) (W : ℝ → Cell → Y) (B : Plane → Y) (R : ℝ)
    (hB : UniformContinuousOn B (closedBall (0 : Plane) (R + 1)))
    (hdiam : ∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
        ε⁻¹ • z ∈ (K.1 : Set Plane) → ε * Metric.diam (K.1 : Set Plane) < η)
    (hselected : ∀ t > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) (R + 1),
        dist (W ε (containingCell (H, ε⁻¹ • z))) (B z) < t) :
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      ∀ z ∈ closedBall (0 : Plane) R, ∀ K : H.1.cells,
        ε⁻¹ • z ∈ (K.1 : Set Plane) → dist (W ε K.1) (B z) < δ := by
  intro δ hδ
  obtain ⟨η₀, hη₀, hmod⟩ := Metric.uniformContinuousOn_iff.mp hB (δ / 2) (by linarith)
  let η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ zero_lt_one
  obtain ⟨ε₁, hε₁, hdiam'⟩ := hdiam η hη
  obtain ⟨ε₂, hε₂, hselected'⟩ := hselected (δ / 2) (by linarith)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro ε hε hεsmall
  have h₁ : ε < ε₁ := lt_of_lt_of_le hεsmall (min_le_left _ _)
  have h₂ : ε < ε₂ := lt_of_lt_of_le hεsmall (min_le_right _ _)
  have hmod' : ∀ u ∈ closedBall (0 : Plane) (R + 1),
      ∀ z ∈ closedBall (0 : Plane) (R + 1), dist u z < η →
        dist (B u) (B z) < δ / 2 := by
    intro u hu z hz hdist
    exact hmod u hu z hz (lt_of_lt_of_le hdist (min_le_left _ _))
  have hresult := all_containing_cell_dist_lt_of_selected H (W ε) B hε
    (min_le_right η₀ 1) (hdiam' ε hε h₁) (hselected' ε hε h₂) hmod'
  intro z hz K hzK
  have h := hresult z hz K hzK
  linarith

end LatticeProb.CellConfigContainingCell
