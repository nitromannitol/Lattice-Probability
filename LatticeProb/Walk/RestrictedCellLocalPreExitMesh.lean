import LatticeProb.Walk.CellNetworkLocalPreExitMesh
import LatticeProb.Prob.FiniteConductanceRestriction

/-! # Local mesh bounds for finite restrictions of cell configurations -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork

namespace LatticeProb.CellConfigInterpolation

/-- A finite restriction of a cell configuration has locally bounded steps
before exit whenever cells meeting the buffered region have bounded diameter. -/
theorem finiteRestriction_trajectoryLaw_ae_preExit_step_le_local_mesh
    (H : CellConfig) (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v)
    (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (R : Set H.cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (A : Set R)
    (hA : ∀ v ∈ A, 0 < (finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).totalConductance v)
    (v : R) (φ : Plane → Euc 2) (hφ : Isometry φ) (U : Set (Euc 2)) (W : Set Plane)
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (a * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ) :
    ∀ᵐ ω ∂(finiteConductanceRestriction
      (fun v w : H.cells => H.c v w) hsymm hnonneg hloop R).trajectoryLaw A hA v,
      ∀ j : ℕ, (j : WithTop ℕ) < exitTime
        ((fun x : R => φ (a • p x)) ⁻¹' U) ω →
      dist (φ (a • p (ω (j + 1)))) (φ (a • p (ω j))) ≤ 2 * (a * δ) := by
  apply trajectoryLaw_ae_preExit_step_le_local_mesh H hH p hp Subtype.val
    (finiteConductanceRestriction (fun v w : H.cells => H.c v w)
      hsymm hnonneg hloop R) ?_ A hA v φ hφ U W a δ ha hδ hbuffer hmesh
  intro v w hvw
  exact hvw

end LatticeProb.CellConfigInterpolation
end
