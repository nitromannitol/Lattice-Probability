import LatticeProb.Walk.CellConfigInterpolationDiameter

/-! # Local diameter bounds for adjacent cells -/

set_option autoImplicit false

noncomputable section

open Set ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigInterpolation

/-- A local cell-diameter bound controls both cells on an edge whose first
representative has a diameter-sized buffer inside the region of the bound. -/
theorem diam_add_le_of_adj_of_local_bound (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (U W : Set Plane) (δ : ℝ)
    (hδ : 0 ≤ δ) (hbuffer : ∀ x ∈ U, Metric.closedBall x δ ⊆ W)
    (hmesh : ∀ K : H.cells, ((K.1 : Set Plane) ∩ W).Nonempty →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    {K L : H.cells} (hK : p K ∈ U) (hKL : H.Adj K L) :
    Metric.diam (K.1 : Set Plane) + Metric.diam (L.1 : Set Plane) ≤ 2 * δ := by
  have hpW : p K ∈ W := hbuffer _ hK (Metric.mem_closedBall_self hδ)
  have hKd := hmesh K ⟨p K, hp K, hpW⟩
  obtain ⟨z, hzK, hzL⟩ := hH.adj_inter K L hKL
  have hzdist : dist z (p K) ≤ δ :=
    (Metric.dist_le_diam_of_mem (K.1 : Cell).isCompact.isBounded hzK (hp K)).trans hKd
  have hzW : z ∈ W := hbuffer _ hK (Metric.mem_closedBall.mpr hzdist)
  have hLd := hmesh L ⟨z, hzL, hzW⟩
  linarith


/-- The local diameter estimate in scaled spatial coordinates. -/
theorem diam_add_le_of_adj_of_scaled_local_bound (H : CellConfig)
    (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (U W : Set Plane) (a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ U, Metric.closedBall x (a * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    {K L : H.cells} (hK : a • p K ∈ U) (hKL : H.Adj K L) :
    Metric.diam (K.1 : Set Plane) + Metric.diam (L.1 : Set Plane) ≤ 2 * δ := by
  apply diam_add_le_of_adj_of_local_bound H hH p hp
    ((fun z : Plane => a • z) ⁻¹' U) ((fun z : Plane => a • z) ⁻¹' W) δ hδ
  · intro x hx y hy
    apply hbuffer (a • x) hx
    apply Metric.mem_closedBall.mpr
    rw [dist_smul₀, Real.norm_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) ha
  · intro C hC
    obtain ⟨z, hz, hzW⟩ := hC
    exact hmesh C ⟨z, hz, hzW⟩
  · exact hK
  · exact hKL

end LatticeProb.CellConfigInterpolation
end
