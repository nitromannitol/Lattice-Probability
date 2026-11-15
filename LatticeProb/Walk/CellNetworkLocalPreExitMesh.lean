import LatticeProb.Walk.CellConfigLocalDiameter
import LatticeProb.Bonanno.BouRabeeGwynne.WalkEdgeSupport
import LatticeProb.Bonanno.BouRabeeGwynne.ActualWalkSkeleton

/-! # Local mesh bounds before exit for a finite cell network -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork

namespace LatticeProb.CellConfigInterpolation

/-- Before leaving the target domain, every step of the ambient network walk
has length at most twice the scaled local cell-diameter bound. -/
theorem trajectoryLaw_ae_preExit_step_le_local_mesh
    {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (H : CellConfig) (hH : H.IsCellConfiguration) (p : H.cells → Plane)
    (hp : ∀ K, p K ∈ (K.1 : Set Plane)) (cell : V → H.cells)
    (N : FiniteConductanceNetwork V)
    (hedge : ∀ v w, 0 < N.a v w → H.Adj (cell v) (cell w))
    (A : Set V) (hA : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    (φ : Plane → Euc 2) (hφ : Isometry φ) (U : Set (Euc 2)) (W : Set Plane)
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ (fun x => φ x) ⁻¹' U, Metric.closedBall x (a * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ) :
    ∀ᵐ ω ∂N.trajectoryLaw A hA v, ∀ j : ℕ,
      (j : WithTop ℕ) < exitTime ((fun x => φ (a • p (cell x))) ⁻¹' U) ω →
      dist (φ (a • p (cell (ω (j + 1))))) (φ (a • p (cell (ω j)))) ≤
        2 * (a * δ) := by
  filter_upwards [N.trajectoryLaw_ae_edge_or_constant A hA v] with ω hω
  intro j hj
  have hin := mem_of_lt_exitTime hj
  rcases hω j with he | he
  · have hadj := hedge (ω j) (ω (j + 1)) he
    have hd := diam_add_le_of_adj_of_scaled_local_bound H hH p hp
      (φ ⁻¹' U) W a δ ha hδ hbuffer hmesh hin hadj
    have hpdist := dist_representatives_le H hH p hp hadj
    rw [hφ.dist_eq, dist_comm, dist_smul₀, Real.norm_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left (hpdist.trans hd) ha]
  · rw [he, dist_self]
    positivity

end LatticeProb.CellConfigInterpolation
end
