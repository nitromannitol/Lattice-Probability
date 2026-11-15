import LatticeProb.Walk.RestrictedCellLocalPreExitMesh
import LatticeProb.Walk.RepresentativeCouplingPath

/-! # Coupled path bounds for finite cell restrictions -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ReflectedGMS ReflectedGMS.GMS BouRabeeGwynne
open BouRabeeGwynne.FiniteConductanceNetwork
open scoped unitInterval

namespace LatticeProb.CellConfigInterpolation

/-- Local cell diameters supply the prefix edge bound under the original
coupling of a finite restriction, provided its coupled exit condition holds. -/
theorem finiteRestriction_representativeCoupling_goodPath_of_local_mesh
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    [MeasurableSingletonClass (Option J)]
    (H : CellConfig) (hH : H.IsCellConfiguration)
    (hsymm : ∀ v w : H.cells, H.c v w = H.c w v)
    (hnonneg : ∀ v w : H.cells, 0 ≤ H.c v w)
    (hloop : ∀ v : H.cells, H.c v v = 0)
    (p : H.cells → Plane) (hp : ∀ K, p K ∈ (K.1 : Set Plane))
    (R : Set H.cells) [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
    (N : FiniteConductanceNetwork R)
    (hN : N = finiteConductanceRestriction (fun v w : H.cells => H.c v w)
      hsymm hnonneg hloop R)
    (A : Set R) (B : J → Set R) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (φ : Plane → Euc 2) (hφ : Isometry φ) (U Q : Set (Euc 2)) (W : Set Plane)
    (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hbuffer : ∀ x ∈ φ ⁻¹' U, Metric.closedBall x (a * δ) ⊆ W)
    (hmesh : ∀ K : H.cells, (∃ z ∈ (K.1 : Set Plane), a • z ∈ W) →
      Metric.diam (K.1 : Set Plane) ≤ δ)
    (q : R → Euc 2) (initial : J) (select : ℕ → Euc 2 → Option J)
    (v : R) (n : ℕ) (ρ : Measure ((ℕ → R) × C(unitInterval, Euc 2)))
    (hρ : ρ.fst = N.trajectoryLaw A hA v)
    (E : Set ((ℕ → R) × C(unitInterval, Euc 2)))
    (hpath : ∀ᵐ x ∂ρ, x ∉ E →
      ∃ k : ℕ, k ≤ (actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        exitTime ((fun x : R => φ (a • p x)) ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        ∃ t, x.2 t ∉ Q) :
    ∀ᵐ x ∂ρ, x ∉ E →
      (actualWalkStage q B initial (fun i w => select i (q w)) n x.1).1 ≠ ⊤ ∧
      ∃ k : ℕ, k ≤ (actualWalkStage q B initial
        (fun i w => select i (q w)) n x.1).1.untopD 0 ∧
        exitTime ((fun x : R => φ (a • p x)) ⁻¹' U) x.1 = (k : WithTop ℕ) ∧
        (∀ j < k, dist (φ (a • p (x.1 (j + 1)))) (φ (a • p (x.1 j))) ≤
          2 * (a * δ)) ∧ ∃ t, x.2 t ∉ Q := by
  apply LatticeProb.representativeCoupling_goodPath_of_exit N
    (fun x => φ (a • p x)) q B hBA hA haccess initial select v n ρ hρ U Q
    ?_ E hpath
  subst N
  exact finiteRestriction_trajectoryLaw_ae_preExit_step_le_local_mesh H hH
    hsymm hnonneg hloop p hp R A hA v φ hφ U W a δ ha hδ hbuffer hmesh

end LatticeProb.CellConfigInterpolation
end
